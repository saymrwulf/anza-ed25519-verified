#!/usr/bin/env bash
# ─────────────────────────────────────────────────────────────────────────────
# selftest-harness.sh — adversarial self-test for check.sh Phase 0c.
#
# Phase 0c pins the scripts and policy files the button itself runs on. The
# attack it exists to stop is the cheapest one in the estate: don't touch the
# proofs at all, edit the checker. Round-5 review of the companion SLH-DSA
# repository stubbed the compiler wrapper alone and got ALL GREEN in 3.6
# seconds over deliberately destroyed proofs.
#
# Cases, each asserting a SPECIFIC diagnostic:
#   0  positive control: untouched tree passes
#   1  a pinned harness file edited by one byte      → does not match its pin
#   2  a NEW executable appears, unpinned            → set mismatch
#   3  an entry DELETED from HARNESS.sha256          → set mismatch, NOT a
#      silent un-pin (this is the shape of the defect SLH-DSA round-6 found:
#      dropping a key un-pinned two files with no diagnostic at all)
#   4  HARNESS.sha256 itself removed                 → fail-closed
#
# Phase 0c is lifted out of check.sh at run time, so the tested logic IS the
# shipping logic. Cheap: no Lean, runs in about a second.
# ─────────────────────────────────────────────────────────────────────────────
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
FAILURES=0
STASH="$(mktemp -d)"
NEWEXE="$HERE/zz-selftest-helper.sh"

cleanup() {
  [ -f "$STASH/HARNESS.sha256" ] && cp "$STASH/HARNESS.sha256" "$HERE/HARNESS.sha256"
  [ -f "$STASH/victim" ] && cp "$STASH/victim" "$HERE/$VICTIM"
  rm -f "$NEWEXE"
  rm -rf "$STASH"
}
trap cleanup EXIT INT TERM

cp "$HERE/HARNESS.sha256" "$STASH/HARNESS.sha256"

# Lift Phase 0c. The two repo families end the phase differently, so accept
# either terminator rather than hardcoding one and silently lifting nothing.
DRIVER="$STASH/phase0c.sh"
PAYLOAD="$STASH/payload.sh"
awk '/^# ── Phase 0c/{f=1} f{print} /^# ── Phase 1|^echo "=== Phase 1/{if(f && !/Phase 0c/) exit}' "$HERE/check.sh" \
  | sed '/^# ── Phase 1/d; /^echo "=== Phase 1/d' > "$PAYLOAD"
{
  echo 'set -uo pipefail'
  echo "HERE=\"$HERE\""
  cat "$PAYLOAD"
} > "$DRIVER"
if [ "$(grep -c . "$PAYLOAD")" -lt 20 ]; then
  echo "FATAL: could not lift Phase 0c out of check.sh — the phase markers moved."
  echo "This self-test must attack the shipping gate; refusing to run against nothing."
  exit 1
fi
"$HERE/lift-guard.sh" "$PAYLOAD" "$DRIVER" "check.sh Phase 0c" || exit 1

expect() {  # expect <label> <want-rc> <want-substring>
  local label="$1" want_rc="$2" want_txt="$3" out rc
  out=$(bash "$DRIVER" 2>&1); rc=$?
  if [ "$rc" -ne "$want_rc" ]; then
    echo "  ✗ $label: exit $rc, expected $want_rc"; echo "$out" | sed 's/^/      /'
    FAILURES=$((FAILURES+1)); return
  fi
  if ! grep -qF "$want_txt" <<<"$out"; then
    echo "  ✗ $label: exit code right, diagnostic wrong (rejected for the wrong reason)"
    echo "      wanted: $want_txt"; echo "$out" | sed 's/^/      /'
    FAILURES=$((FAILURES+1)); return
  fi
  echo "  ✓ $label"
}

echo "=== selftest-harness: attacking check.sh Phase 0c ==="

# ── 0. positive control ────────────────────────────────────────────────────
expect "case 0 control: untouched harness passes" 0 "match their pins"

# ── 1. edit a pinned file. lean-guard is the pointed choice: it is the memory
#      cap protecting this machine, and stubbing it is the demonstrated
#      3.6-second path to a false green.
VICTIM=lean-guard
cp "$HERE/$VICTIM" "$STASH/victim"
printf '\n# selftest\n' >> "$HERE/$VICTIM"
expect "case 1: edited lean-guard caught" 1 "does not match its pin"
cp "$STASH/victim" "$HERE/$VICTIM"

# ── 2. a new executable the button could shell out to ──────────────────────
printf '#!/bin/sh\necho "unpinned"\n' > "$NEWEXE"; chmod +x "$NEWEXE"
expect "case 2: new unpinned executable caught" 1 "does not match HARNESS.sha256"
rm -f "$NEWEXE"

# ── 3. delete a pin entry: the set must be derived from the filesystem, not
#      read out of the map being consulted, or this is a silent un-pin.
grep -v " ${VICTIM}\$" "$STASH/HARNESS.sha256" > "$HERE/HARNESS.sha256"
expect "case 3: deleted pin entry is a failure, not a silent un-pin" 1 "does not match HARNESS.sha256"
cp "$STASH/HARNESS.sha256" "$HERE/HARNESS.sha256"

# ── 4. absence must not pass for cleanliness ───────────────────────────────
rm -f "$HERE/HARNESS.sha256"
expect "case 4: missing pin file is fail-closed" 1 "the harness is unpinned"
cp "$STASH/HARNESS.sha256" "$HERE/HARNESS.sha256"

# ── 5. restored ────────────────────────────────────────────────────────────
expect "case 5: restored to green" 0 "match their pins"

echo ""
if [ "$FAILURES" -eq 0 ]; then
  echo "SELFTEST PASSED — Phase 0c rejects harness tampering for the stated reason."
  exit 0
fi
echo "SELFTEST FAILED: $FAILURES case(s) did not behave as claimed."
exit 1
