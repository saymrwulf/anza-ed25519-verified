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

cleanup() {
  rm -f "$ATTACK" "${ATTACK%.lean}.olean"
  [ -f "$STASH/FeQ.olean" ] && mv "$STASH/FeQ.olean" "$HERE/Proofs/FeQ.olean"
  rm -rf "$STASH"
  rm -f "$HERE"/.axgate-*.lean "$HERE"/.axgate-*.olean
}
trap cleanup EXIT INT TERM

# Phase 2b, lifted verbatim from the shipping button.
DRIVER="$STASH/phase2b.sh"
{
  echo 'set -euo pipefail'
  echo 'source ~/aeneas-toolchain/env.sh'
  echo "HERE=\"$HERE\""
  echo 'AENEAS_LEAN="$AENEAS_HOME/backends/lean"'
  echo "TIMEOUT=$TIMEOUT; CORES=\"$CORES\""
  sed -n '/^# ── Phase 2b/,/^# ── Phase 3/p' "$HERE/check.sh" | sed '$d'
} > "$DRIVER"
if [ "$(wc -l < "$DRIVER")" -lt 40 ]; then
  echo "FATAL: could not lift Phase 2b out of check.sh — the phase markers moved."
  echo "This self-test must attack the shipping gate; refusing to run against nothing."
  exit 1
fi

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
cat > "$ATTACK" <<'EOF'
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
  LEAN_TIMEOUT=$TIMEOUT LEAN_MAX_CORES=$CORES '$HERE/lean-guard' 'Proofs/ZZSelftestAttack.lean'
") >/dev/null 2>&1 || { echo "  FAIL setup: the attack module did not compile"; FAILURES=$((FAILURES+1)); }
expect "indented axiom caught kernel-side" 1 "AXIOM DECLARED under Proofs/"
rm -f "$ATTACK" "${ATTACK%.lean}.olean"

# ── 3. Vacuity: delete a compiled module. "Nothing found" must not pass for
#      "nothing wrong" — the gate has to notice it stopped covering something.
mv "$HERE/Proofs/FeQ.olean" "$STASH/FeQ.olean"
expect "missing .olean is a failure, not a vacuous pass" 1 "COVERAGE MISMATCH"
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
if ! diff -q <(echo "$TREE_AT_START") \
             <(cd "$HERE/.." && git status --porcelain -- verification/Proofs) >/dev/null; then
  echo "  FAIL restore: Proofs/ differs from how this test found it:"
  diff <(echo "$TREE_AT_START") \
       <(cd "$HERE/.." && git status --porcelain -- verification/Proofs) | sed 's/^/        /'
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
