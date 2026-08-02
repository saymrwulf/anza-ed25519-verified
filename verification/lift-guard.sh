#!/usr/bin/env bash
# lift-guard.sh <payload> <driver> [<phase-label>]
#
# Every variable the LIFTED PAYLOAD reads must be one the DRIVER defines.
# Prints the offending names and exits 1 if any are missing.
#
# ───────────────────────────────────────────────────────────────────────────
# WHY THIS EXISTS — 2026-08-02
#
# Five of this repository's self-tests work by lifting one phase out of
# check.sh and running it standalone against a deliberately corrupted tree.
# That is the right design: the test then attacks the SHIPPING gate rather
# than a re-implementation of it. But a lifted phase is a fragment, and it
# reads variables its neighbours defined. Each self-test therefore carries a
# hand-written preamble supplying them.
#
# A hand-written preamble is a hand-kept list, and hand-kept lists drift. Twice
# in two days a phase grew a dependency and no preamble was told:
#
#   · Phase 2c grew an accounting block reading $KERNLOG, a file Phase 2b
#     creates. selftest-shapes.sh died on its first expansion under `set -u`.
#     It could not pass on any fork from the moment that block was added.
#
#   · Phase 2b changed from globbing Proofs/*.lean to reading the $PROOFS
#     membership manifest — the spelling-versus-ownership fix ScalarPackSpec
#     forced. selftest-axgate.sh's preamble was never told. Bash does NOT
#     error on an unset array expansion under `set -u`; it expands to nothing,
#     so `printf '"%s.olean", ' "${PROOFS[@]}"` silently produced
#         expected := [".olean"]
#     — one entry, empty name — and the gate's own fail-closed absence check
#     rejected it. The baseline went red and both attack cases were then
#     rejected for the WRONG REASON.
#
# Both failed loudly rather than passing vacuously, which is the only reason
# they were not false assurance. That is luck, not design: a missing variable
# that happens to make an ATTACK case die still looks like the attack being
# caught, and only the substring assertions in each `expect` helper stand
# between that and a green test measuring nothing.
#
# The fix for the CLASS is to stop maintaining the list by hand. This tool
# derives the requirement from the two artifacts themselves, so a phase that
# grows a new dependency fails AT LIFT TIME, naming it, instead of dying
# mid-run or — worse — passing for the wrong reason.
#
# WHAT IT IS NOT. This is a shell-text approximation, not a bash parser: it
# cannot see indirect expansion, `eval`, or a name built at runtime. It is a
# tripwire on the failure mode that actually occurred twice, not a proof of
# closure. Its answer is advisory in one direction only — it can miss a
# dependency, it does not invent one, and every name it reports is a name the
# payload genuinely mentions and the driver genuinely does not set.
# ───────────────────────────────────────────────────────────────────────────
set -euo pipefail

PAYLOAD="${1:?usage: lift-guard.sh <payload> <driver> [phase-label]}"
DRIVER="${2:?usage: lift-guard.sh <payload> <driver> [phase-label]}"
LABEL="${3:-the lifted phase}"

for f in "$PAYLOAD" "$DRIVER"; do
  [ -s "$f" ] || { echo "FATAL: lift-guard: '$f' is missing or empty."; exit 1; }
done

UNBOUND=$(python3 - "$PAYLOAD" "$DRIVER" <<'PYGUARD'
import re, sys
payload = open(sys.argv[1]).read()
driver  = open(sys.argv[2]).read()

# What the payload READS. Deliberately over-approximates: a name mentioned in a
# comment costs one lifted definition, a name missed costs a broken self-test.
reads = set(re.findall(r'\$\{?([A-Za-z_][A-Za-z0-9_]*)', payload))

# What the DRIVER defines, in every form these scripts actually use.
# An assignment may open a line OR follow `;`, `&&`, `||`, `then`, `do`, `{` —
# `TIMEOUT=$T; CORES="$C"` is one line with two of them, and a start-anchored
# pattern sees only the first. That over-strictness is not harmless: a guard
# that cries wolf gets edited away, and then it guards nothing.
assigns  = set(re.findall(
    r'(?:^|;|&&|\|\||\bthen\b|\bdo\b|\{)\s*([A-Za-z_][A-Za-z0-9_]*)=',
    driver, re.M))
assigns |= set(re.findall(r'\b(?:export|declare|local|readonly)\s+(?:-\w+\s+)*'
                          r'([A-Za-z_][A-Za-z0-9_]*)', driver))
assigns |= set(re.findall(r'\bfor\s+([A-Za-z_][A-Za-z0-9_]*)\s+in\b', driver))
# `read` binds names too, and it is almost never at end of line: the shape that
# matters here is `while read -r n; do`. An end-anchored pattern misses it and
# the guard then demands a definition for a loop variable the payload binds
# itself — a false alarm, which is the one failure a guard cannot afford.
for m in re.finditer(r'\bread\b((?:\s+-\w+)*(?:\s+[A-Za-z_][A-Za-z0-9_]*)+)', driver):
    assigns |= set(re.findall(r'[A-Za-z_][A-Za-z0-9_]*', m.group(1)))

# Names the driver INHERITS rather than defines: the shell's own, and the ones
# `source ~/aeneas-toolchain/env.sh` puts in the environment. Keep this list
# short and justified — every entry is a hole in the guard.
ENV = {'PWD', 'HOME', 'PATH', 'IFS', 'PIPESTATUS', 'BASH_SOURCE', 'FUNCNAME',
       'LINENO', 'RANDOM', 'SECONDS', 'OSTYPE', 'HOSTNAME', 'USER', 'SHELL',
       'TMPDIR', 'LC_ALL', 'LANG', 'BASH_REMATCH', 'REPLY', 'PS4',
       'AENEAS_HOME', 'LEAN_PATH', 'LEAN_MEM_MB', 'LEAN_TIMEOUT',
       'LEAN_MAX_CORES'}

print(' '.join(sorted(n for n in reads - assigns - ENV if not n.isdigit())))
PYGUARD
)

if [ -n "$UNBOUND" ]; then
  cat <<EOF
FATAL: $LABEL reads variables this lift does not define: $UNBOUND
       Either lift their definitions too — VERBATIM from check.sh, with a
       sed range, so this test cannot drift away from the button's idea of
       them — or end the lift range before the block that uses them.
       Do NOT stub them: a stub makes the test measure something the button
       never runs, which is how a self-test becomes decoration.
EOF
  exit 1
fi
