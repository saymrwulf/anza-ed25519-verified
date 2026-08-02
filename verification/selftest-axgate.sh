#!/usr/bin/env bash
# ─────────────────────────────────────────────────────────────────────────────
# selftest-axgate.sh — adversarial self-test for check.sh Phase 2b.
#
# An untested guard is decoration. This script breaks the thing Phase 2b
# guards and asserts the gate goes red FOR THE STATED REASON — a rejection by
# some other gate, or with some other message, fails the test too.
#
# It extracts Phase 2b out of check.sh at run time, so it attacks THE SHIPPING
# GATE rather than a copy that can drift away from it.
#
# Requires: Proofs/*.olean already built (run check.sh first, or any prior
# green build). Takes ~10 s; compiles one tiny throwaway module.
# ─────────────────────────────────────────────────────────────────────────────
set -uo pipefail
source ~/aeneas-toolchain/env.sh
HERE="$(cd "$(dirname "$0")" && pwd)"
AENEAS_LEAN="$AENEAS_HOME/backends/lean"
TIMEOUT="${LEAN_TIMEOUT:-600}"
export LEAN_MEM_MB="${LEAN_MEM_MB:-8192}"
CORES="${LEAN_MAX_CORES:-0-3}"

ATTACK="$HERE/Proofs/ZZSelftestAttack.lean"
STASH="$(mktemp -d)"
FAILURES=0
# Recorded before anything is touched, so the restore check compares against
# reality rather than assuming a pristine checkout.
TREE_AT_START="$(cd "$(dirname "$0")/.." && git status --porcelain -- verification/Proofs)"

# Declared before the trap: cleanup reads it, and under `set -u` an unset name
# turns any early abort into a second, misleading failure.
VICTIM=""

cleanup() {
  rm -f "$ATTACK" "${ATTACK%.lean}.olean"
  [ -f "$STASH/FeQ.olean" ] && mv "$STASH/FeQ.olean" "$HERE/Proofs/FeQ.olean"
  # Restore the poisoned module on EVERY path. A self-test that aborts midway
  # must not leave a proof module carrying `axiom cheat : ∀ P, P` behind it.
  if [ -n "$VICTIM" ] && [ -f "$STASH/victim.lean" ]; then
    cp "$STASH/victim.lean"  "$HERE/Proofs/$VICTIM.lean"
    [ -f "$STASH/victim.olean" ] && cp "$STASH/victim.olean" "$HERE/Proofs/$VICTIM.olean"
  fi
  rm -rf "$STASH"
  rm -f "$HERE"/.axgate-*.lean "$HERE"/.axgate-*.olean
}
trap cleanup EXIT INT TERM

# Phase 2b, lifted verbatim from the shipping button.
DRIVER="$STASH/phase2b.sh"
PAYLOAD="$STASH/payload.sh"
# Stop at the NEXT phase marker, whatever it is called. A hardcoded terminator
# ("...to Phase 3") silently widens the moment a phase is inserted between the
# two: adding Phase 2c made this driver swallow 2c as well and die on variables
# that phase expects check.sh to have defined, which surfaced as the BASELINE
# failing — a self-test blaming a gate for its own extraction bug.
awk '/^# ── Phase 2b/{f=1} f&&/^# ── (Phase |Phases end)/&&!/Phase 2b/{exit} f{print}' \
  "$HERE/check.sh" > "$PAYLOAD"
{
  echo 'set -euo pipefail'
  echo 'source ~/aeneas-toolchain/env.sh'
  echo "HERE=\"$HERE\""
  echo 'AENEAS_LEAN="$AENEAS_HOME/backends/lean"'
  echo "TIMEOUT=$TIMEOUT; CORES=\"$CORES\""
  # THE COMPILE MANIFEST. Phase 2b used to glob Proofs/*.lean; it now reads
  # $PROOFS by MEMBERSHIP, because a glob demands artifacts this button never
  # makes (the spelling-versus-ownership error ScalarPackSpec exposed). This
  # preamble was not told, and bash does not error on an unset array under
  # `set -u` — it expands to nothing, so the gate got `expected := [".olean"]`
  # and rejected the baseline for a reason that had nothing to do with axioms.
  # Lifted VERBATIM, never re-derived: a re-derivation lets this test's idea of
  # the manifest drift away from the button's, and then the test checks its own
  # opinion. lift-guard.sh below is what makes the omission impossible to
  # repeat silently.
  sed -n '/^PROOFS=(/,/^)/p' "$HERE/check.sh"
  cat "$PAYLOAD"
} > "$DRIVER"
# Guard on the PAYLOAD, not the concatenation: a marker appearing in the
# preamble or in a lifted definition would otherwise satisfy these.
if [ "$(wc -l < "$PAYLOAD")" -lt 40 ]; then
  echo "FATAL: could not lift Phase 2b out of check.sh — the phase markers moved."
  echo "This self-test must attack the shipping gate; refusing to run against nothing."
  exit 1
fi
if [ "$(grep -c '^# ── Phase ' "$PAYLOAD")" -ne 1 ]; then
  echo "FATAL: the lifted block spans more than one phase; the extraction is wrong."
  grep '^# ── Phase ' "$PAYLOAD" | sed 's/^/    /'
  exit 1
fi
grep -qF 'PROOFS=(' "$DRIVER" || {
  echo "FATAL: the lift carries no 'PROOFS=(' — the compile manifest is missing."; exit 1; }
"$HERE/lift-guard.sh" "$PAYLOAD" "$DRIVER" "check.sh Phase 2b" || exit 1

expect() {   # expect <name> <expected-rc> <required-substring>
  local name="$1" want_rc="$2" want_txt="$3"
  local out rc
  out=$(bash "$DRIVER" 2>&1); rc=$?
  if [ "$rc" -ne "$want_rc" ]; then
    echo "  FAIL $name: exit $rc, expected $want_rc"; FAILURES=$((FAILURES+1)); return
  fi
  if ! grep -qF "$want_txt" <<<"$out"; then
    echo "  FAIL $name: exit code right but diagnostic wrong (rejected for the wrong reason)"
    echo "        wanted substring: $want_txt"
    echo "        got: $(tr '\n' '|' <<<"$out" | cut -c1-300)"
    FAILURES=$((FAILURES+1)); return
  fi
  echo "  ok   $name"
}

echo "=== selftest-axgate: attacking check.sh Phase 2b ==="

# ── 1. Baseline: the untouched repo must pass, and say how much it covered.
expect "baseline green, coverage reported" 0 "none is an axiom"

# ── 2. The attack Phase 1's grep cannot see: an indented top-level axiom.
#      Lean accepts it; the repo then proves False; the source-text gate is blind.
#
#      THE ATTACK GOES INTO A MANIFESTED MODULE, and that is the whole point of
#      this case. Until 2026-08-02 it created a NEW file, Proofs/ZZSelftestAttack
#      .lean, which worked while Phase 2b globbed Proofs/*.olean. Phase 2b now
#      reads $PROOFS by MEMBERSHIP, so a stray module is simply not this gate's
#      business — it is the dead-file gate's, and selftest-harness.sh case 8
#      already proves check.sh dies with DEAD FILE on exactly that. Against
#      membership, the stray-file attack passed the gate and the case went red.
#      It is also the WEAKER attack: an adversary who can add files to Proofs/
#      has to get past the dead-file gate, whereas an adversary who edits a
#      module that is already manifested does not. So the case now poisons a
#      real manifested module, which is what the kernel gate exists to catch.
MANIFEST=$(sed -n '/^PROOFS=(/,/^)/p' "$HERE/check.sh" \
           | sed 's/#.*//; s/PROOFS=(//; s/)//' | tr -s ' \t' '\n' | sed '/^$/d')
# A LEAF: nothing else in the manifest imports it, so poisoning it cannot make
# a sibling's artifact stale. Smallest such module, to keep the recompile cheap.
#
# The SEARCH SET excludes Inventory* and Audit, and that exclusion is
# load-bearing: those are the aggregators, they import the whole corpus, and
# grepping them makes every module look imported. Leave them in and the loop
# finds no leaf at all — which is precisely how this case first reported
# "the corpus shape changed" against a corpus that had not changed.
SEARCHERS=$(for m in $MANIFEST; do
              case $m in Inventory*|Audit) ;; *) echo "$HERE/Proofs/$m.lean";; esac
            done)
_best=999999
for m in $MANIFEST; do
  case $m in Inventory*|Audit) continue;; esac
  [ -f "$HERE/Proofs/$m.lean" ] || continue
  grep -qE "^import Proofs\.$m\$" $SEARCHERS 2>/dev/null && continue
  n=$(wc -l < "$HERE/Proofs/$m.lean")
  if [ "$n" -lt "$_best" ]; then _best=$n; VICTIM=$m; fi
done
if [ -z "$VICTIM" ]; then
  echo "  FAIL premise: no manifested leaf module to poison — the corpus shape changed."
  FAILURES=$((FAILURES+1))
else
  cp "$HERE/Proofs/$VICTIM.lean"  "$STASH/victim.lean"
  cp "$HERE/Proofs/$VICTIM.olean" "$STASH/victim.olean"
  cat >> "$HERE/Proofs/$VICTIM.lean" <<'EOF'

namespace ZZSelftestAttack
 axiom cheat : ∀ (P : Prop), P
theorem repo_proves_false : False := cheat _
end ZZSelftestAttack
EOF
  if grep -rnE '^(private |protected |noncomputable )*axiom ' "$HERE"/Proofs/*.lean >/dev/null 2>&1; then
    echo "  FAIL premise: Phase 1's grep sees the attack — this test no longer tests what it claims"
    FAILURES=$((FAILURES+1))
  else
    echo "  ok   premise: Phase 1's source-text grep is blind to this attack"
  fi
  (cd "$AENEAS_LEAN" && lake env bash -c "
    set -euo pipefail
    cd '$HERE/gen' && export LEAN_PATH=\"\$LEAN_PATH:\$PWD:$HERE\"
    cd '$HERE'
    LEAN_TIMEOUT=$TIMEOUT LEAN_MAX_CORES=$CORES '$HERE/lean-guard' 'Proofs/$VICTIM.lean'
  ") >/dev/null 2>&1 || { echo "  FAIL setup: the poisoned module did not compile"; FAILURES=$((FAILURES+1)); }
  expect "indented axiom in a manifested module caught kernel-side" 1 "AXIOM DECLARED under Proofs/"
  cp "$STASH/victim.lean"  "$HERE/Proofs/$VICTIM.lean"
  cp "$STASH/victim.olean" "$HERE/Proofs/$VICTIM.olean"
fi

# ── 3. Vacuity: delete a compiled module. "Nothing found" must not pass for
#      "nothing wrong" — the gate has to notice it stopped covering something.
#      The expected wording tracks the SHIPPING diagnostic: it read "COVERAGE
#      MISMATCH" while the gate compared two counts, and became a per-module
#      message when the gate started walking $PROOFS by membership. Asserting
#      the reason and not merely the exit code is deliberate — a gate that goes
#      red for an unrelated cause has not been tested.
mv "$HERE/Proofs/FeQ.olean" "$STASH/FeQ.olean"
expect "missing .olean is a failure, not a vacuous pass" 1 \
       "is in the compile manifest but its artifact is absent"
mv "$STASH/FeQ.olean" "$HERE/Proofs/FeQ.olean"

# ── 4. Litter: neither path may leave the temp gate source or its artifact
#      behind (this repo accumulated 101 orphan .olean files exactly that way).
if ls "$HERE"/.axgate-* >/dev/null 2>&1; then
  echo "  FAIL litter: temp gate files survived a run"; FAILURES=$((FAILURES+1))
else
  echo "  ok   no litter left by either the green or the red path"
fi

# ── 5. Restored: the self-test must leave the working tree exactly as it found
#      it. Compared against the state recorded at START, not against a pristine
#      checkout — files can be legitimately uncommitted while work is in flight,
#      and a test that assumes otherwise reports its own premise as a failure.
# Compare the two states AS STRINGS. Comparing `echo "$VAR"` against a raw
# command substitution is asymmetric: for a clean tree the variable is empty
# and `echo` still emits one blank line while the command emits none, so the
# check reports a spurious difference exactly when nothing is wrong.
TREE_NOW="$(cd "$HERE/.." && git status --porcelain -- verification/Proofs)"
if [ "$TREE_AT_START" != "$TREE_NOW" ]; then
  echo "  FAIL restore: Proofs/ differs from how this test found it:"
  diff <(printf '%s\n' "$TREE_AT_START") <(printf '%s\n' "$TREE_NOW") | sed 's/^/        /'
  FAILURES=$((FAILURES+1))
else
  echo "  ok   working tree restored to its starting state"
fi

echo ""
if [ "$FAILURES" -eq 0 ]; then
  echo "SELFTEST PASSED — Phase 2b rejects what it claims to reject, for the stated reason."
  exit 0
fi
echo "SELFTEST FAILED: $FAILURES check(s) did not behave as claimed."
exit 1
