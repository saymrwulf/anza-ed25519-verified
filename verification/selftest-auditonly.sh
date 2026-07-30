#!/usr/bin/env bash
# ─────────────────────────────────────────────────────────────────────────────
# selftest-auditonly.sh — adversarial self-test for check.sh --audit-only.
#
# --audit-only skips recompilation, which makes it the most dangerous thing in
# this repository: if it ever accepted a tree whose sources had changed, a green
# transcript would describe a corpus that is not on disk. Its whole safety rests
# on refusing, so refusal is what this tests.
#
# Cases, each asserting a SPECIFIC diagnostic:
#   0  no basis recorded                     -> REFUSING, may only follow a full run
#   1  a proof source edited by one comment  -> REFUSING, sources no longer match
#   2  a proof source DELETED                -> REFUSING (the basis lists it)
#   3  a NEW proof source added              -> ORPHAN, from the seam check,
#      which runs BEFORE the mode gate and catches it first
#   4  an artifact deleted, sources intact   -> MISSING ARTIFACT
#   5  the basis file truncated              -> REFUSING (mismatch, not a pass)
#   6  mtimes touched but bytes unchanged    -> PASSES, because bytes are the
#      test and mtimes are not: `touch` must neither grant nor deny permission
#
# Requires a prior full green run in this tree (that is what writes the basis).
# No Lean runs here; the whole thing takes seconds.
# ─────────────────────────────────────────────────────────────────────────────
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
FAILURES=0
STASH="$(mktemp -d)"
BASIS="$HERE/.audit-basis"
VICTIM_SRC="Proofs/FeQ.lean"
VICTIM_ART="Proofs/FeQ.olean"
NEWSRC="$HERE/Proofs/ZZAuditOnlyProbe.lean"

cleanup() {
  [ -f "$STASH/basis" ]  && cp "$STASH/basis" "$BASIS"
  [ -f "$STASH/src" ]    && cp "$STASH/src" "$HERE/$VICTIM_SRC"
  [ -f "$STASH/art" ]    && cp "$STASH/art" "$HERE/$VICTIM_ART"
  rm -f "$NEWSRC" "${NEWSRC%.lean}.olean"
  rm -rf "$STASH"
}
trap cleanup EXIT INT TERM

if [ ! -s "$BASIS" ]; then
  echo "FATAL: no basis in this tree. Run ./check.sh with no arguments first;"
  echo "this self-test exercises --audit-only, which requires one."
  exit 1
fi
cp "$BASIS" "$STASH/basis"
cp "$HERE/$VICTIM_SRC" "$STASH/src"
cp "$HERE/$VICTIM_ART" "$STASH/art"

expect() {  # expect <label> <want-rc> <want-substring>
  local label="$1" want_rc="$2" want_txt="$3" out rc
  out=$( cd "$HERE" && ./check.sh --audit-only 2>&1 ); rc=$?
  if [ "$rc" -ne "$want_rc" ]; then
    echo "  ✗ $label: exit $rc, expected $want_rc"; tail -6 <<<"$out" | sed 's/^/      /'
    FAILURES=$((FAILURES+1)); return
  fi
  if ! grep -qF "$want_txt" <<<"$out"; then
    echo "  ✗ $label: exit code right, diagnostic wrong (refused for the wrong reason)"
    echo "      wanted: $want_txt"; tail -6 <<<"$out" | sed 's/^/      /'
    FAILURES=$((FAILURES+1)); return
  fi
  echo "  ✓ $label"
}

echo "=== selftest-auditonly: attacking check.sh --audit-only ==="

expect "control: unchanged tree passes" 0 "sources byte-identical to the last full run"

rm -f "$BASIS"
expect "case 0: no basis recorded" 1 "may only follow a full green run"
cp "$STASH/basis" "$BASIS"

printf '\n-- selftest\n' >> "$HERE/$VICTIM_SRC"
expect "case 1: a proof source edited by one comment" 1 "no longer match the basis"
cp "$STASH/src" "$HERE/$VICTIM_SRC"

mv "$HERE/$VICTIM_SRC" "$STASH/moved"
expect "case 2: a proof source deleted" 1 "no longer match the basis"
mv "$STASH/moved" "$HERE/$VICTIM_SRC"

# A new source is refused EARLIER than the basis comparison: the seam check
# (Phase 1b) runs first and reports it as belonging to no manifest. Asserting
# the seam's diagnostic rather than the basis's is not a weaker test — it is the
# true one, and demanding the basis message here would go red the day the seam
# check does its job.
printf 'namespace ZZProbe\ntheorem t : 1 = 1 := rfl\nend ZZProbe\n' > "$NEWSRC"
expect "case 3: a new proof source added -> caught by the seam check first" 1 "is in NEITHER manifest"
rm -f "$NEWSRC"

mv "$HERE/$VICTIM_ART" "$STASH/movedart"
expect "case 4: an artifact deleted, sources intact" 1 "MISSING ARTIFACT"
mv "$STASH/movedart" "$HERE/$VICTIM_ART"

head -3 "$STASH/basis" > "$BASIS"
expect "case 5: the basis truncated" 1 "no longer match the basis"
cp "$STASH/basis" "$BASIS"

# BYTES, NOT MTIMES. Touching every source must change nothing: a check keyed on
# timestamps would both deny this legitimate run and, worse, ACCEPT a modified
# file whose mtime had been reset. Asserting the pass is what pins that choice.
find "$HERE/Proofs" "$HERE/gen" -name '*.lean' -exec touch {} +
expect "case 6: mtimes touched, bytes unchanged -> still passes" 0 "sources byte-identical to the last full run"

echo ""
if [ "$FAILURES" -eq 0 ]; then
  echo "SELFTEST PASSED — --audit-only refuses every stale tree it was shown, and"
  echo "accepts only one whose sources are byte-identical to the recorded basis."
  exit 0
fi
echo "SELFTEST FAILED: $FAILURES case(s) did not behave as claimed."
exit 1
