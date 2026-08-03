#!/usr/bin/env bash
# lift-guard.sh <payload> <driver> [<phase-label>]
#
# Every VARIABLE the LIFTED PAYLOAD reads must be one the DRIVER defines.
#
# VARIABLES ONLY — and the emphasis is a round-8 correction (Claude, N1). A
# lifted payload also inherits FUNCTIONS, shell options, traps and a working
# directory from the script it was cut out of. This tool models none of those.
# A lifted phase calling a function defined in a neighbouring phase fails with
# `command not found`, loud under `set -e`, which is why it is not urgent; but
# the banner used to read as a completeness claim about lifting and it is a
# completeness claim about variables.
#
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
# WHAT IT IS NOT. This is a shell-text approximation, not a bash parser. It
# still cannot see a name built at runtime or passed through `eval`, and it
# models variables only — not functions, shell options, traps or the working
# directory a lifted phase also inherits. It is a tripwire on failure modes
# that actually occurred, not a proof of closure.
#
# Where it CANNOT bound the reads it refuses rather than staying silent:
# indirect expansion (`${!name}`) is detected and fails the lift. That is the
# round-8 correction — a guard whose contract is "does not miss a dependency"
# must say so when it cannot honour it, instead of shrugging.
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

# ARITHMETIC CONTEXTS READ NAMES WITHOUT A `$`. Round-8 review (Claude, N1):
#   echo $((X + 1))      reads X
#   (( Y > 0 )) && ...   reads Y
# and the pattern above cannot see either, because the character after `$` is
# `(`. This is the guard's own failure mode — a phase growing a dependency the
# guard is blind to — and `if [ $((inm + ins)) -eq 0 ]` is already live in
# check.sh's Phase 1b. Not lifted today, which made it latent, not absent.
for expr in (re.findall(r'\$\(\((.*?)\)\)', payload, re.S)
             + re.findall(r'(?<!\$)\(\((.*?)\)\)', payload, re.S)):
    for tok in re.findall(r'[A-Za-z_][A-Za-z0-9_]*', expr):
        reads.add(tok)

# What the DRIVER defines, in every form these scripts actually use.
# `TIMEOUT=$T; CORES="$C"` is one line with two assignments, and a
# start-anchored pattern sees only the first.
# An assignment may open a line or follow `;`, `&&`, `||`, `then`, `do`, `{`,
# and — round-8 review (Claude, N1) — `else`, a `case` branch's `)`, and `!`.
# Six false-positive classes were demonstrated. A guard that cries wolf gets
# edited away, so over-strictness here is not the safe direction.
assigns  = set(re.findall(
    r'(?:^|;|&&|\|\||\)|!|\bthen\b|\bdo\b|\belse\b|\{)\s*'
    r'([A-Za-z_][A-Za-z0-9_]*)=', driver, re.M))
# `mapfile`/`readarray` and `printf -v` bind a name without an `=` at all.
assigns |= set(re.findall(
    r'\b(?:mapfile|readarray)\b(?:\s+-[A-Za-z]\s*\S*)*\s+([A-Za-z_][A-Za-z0-9_]*)',
    driver))
assigns |= set(re.findall(r'\bprintf\b[^\n]*?\s-v\s+([A-Za-z_][A-Za-z0-9_]*)', driver))
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

# INDIRECT EXPANSION DEFEATS TEXT ANALYSIS, so say so instead of staying
# silent. `n=Q; echo "${!n}"` reads Q, and no amount of pattern-matching
# recovers that from the source. The guard's contract is that it does not miss
# a dependency; where it cannot honour that it must refuse, not shrug.
if re.search(r'\$\{!', payload):
    print('INDIRECT-EXPANSION')
else:
    print(' '.join(sorted(n for n in reads - assigns - ENV if not n.isdigit())))
PYGUARD
)

if [ "$UNBOUND" = "INDIRECT-EXPANSION" ]; then
  cat <<EOF
FATAL: $LABEL uses indirect expansion (\${!name}).
       The set of variables it reads cannot be derived from its text, so this
       guard cannot certify that the lift carries them. Rewrite the phase
       without indirection, or lift it with a driver that is known-complete by
       other means and say so in the self-test.
EOF
  exit 1
fi
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
