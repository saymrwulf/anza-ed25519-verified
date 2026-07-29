#!/usr/bin/env bash
# ─────────────────────────────────────────────────────────────────────────────
# selftest-statements.sh — adversarial self-test for the BINDING phases,
# check.sh 0b (the extracted model) and 3c (statements and specifications).
#
# These phases exist because Phases 2b/3/3b establish what a certificate RESTS
# ON and never what it SAYS, nor what it is ABOUT. This script performs the
# attacks that move no axiom cone at all, and asserts each is rejected FOR THE
# STATED REASON.
#
# It lifts Phase 3c out of check.sh at run time, so it attacks the shipping
# gate rather than a copy that can drift away from it.
#
# Requires a prior green build (Proofs/*.olean present). The cheap cases each
# recompile only Proofs/Audit.lean (~10 s). The gutted-statement case also
# recompiles one certificate module and is therefore slower; skip it with
# SKIP_SLOW=1 if you only want the fast gates exercised.
# ─────────────────────────────────────────────────────────────────────────────
set -uo pipefail
source ~/aeneas-toolchain/env.sh
HERE="$(cd "$(dirname "$0")" && pwd)"
AENEAS_LEAN="$AENEAS_HOME/backends/lean"
TIMEOUT="${LEAN_TIMEOUT:-900}"
export LEAN_MEM_MB="${LEAN_MEM_MB:-8192}"
CORES="${LEAN_MAX_CORES:-0-3}"
SKIP_SLOW="${SKIP_SLOW:-0}"

STASH="$(mktemp -d)"
FAILURES=0
# Recorded before anything is touched, so the restore check compares against
# reality rather than assuming a pristine checkout.
TREE_AT_START="$(cd "$(dirname "$0")/.." && git status --porcelain)"

cleanup() {
  [ -f "$STASH/Audit.lean" ]         && cp "$STASH/Audit.lean" "$HERE/Proofs/Audit.lean"
  [ -f "$STASH/AUDIT-MANIFEST.txt" ] && cp "$STASH/AUDIT-MANIFEST.txt" "$HERE/AUDIT-MANIFEST.txt"
  [ -f "$STASH/check.sh" ]           && cp "$STASH/check.sh" "$HERE/check.sh"
  [ -n "${GUT_MOD:-}" ] && [ -f "$STASH/gut.lean" ] && cp "$STASH/gut.lean" "$HERE/Proofs/$GUT_MOD.lean"
  [ -n "${GENF:-}" ] && [ -f "$STASH/genfile.bak" ] && cp "$STASH/genfile.bak" "$HERE/gen/$GENF"
  [ -n "${GENF:-}" ] && rm -f "$HERE/gen/$(dirname "$GENF")/ZZExtra.lean"
  rm -rf "$STASH"
}
trap cleanup EXIT INT TERM

cp "$HERE/Proofs/Audit.lean"   "$STASH/Audit.lean"
cp "$HERE/AUDIT-MANIFEST.txt"  "$STASH/AUDIT-MANIFEST.txt"
cp "$HERE/check.sh"            "$STASH/check.sh"

DRIVER0B="$STASH/phase0b.sh"
{
  echo 'set -uo pipefail'
  echo "HERE=\"$HERE\""
  sed -n '/^# ── Phase 0b/,/^# ── Phase 1/p' "$HERE/check.sh" | sed '$d'
} > "$DRIVER0B"
if [ "$(wc -l < "$DRIVER0B")" -lt 20 ]; then
  echo "FATAL: could not lift Phase 0b out of check.sh."; exit 1
fi

DRIVER="$STASH/phase3c.sh"
build_driver() {
  {
    echo 'set -uo pipefail'
    echo 'source ~/aeneas-toolchain/env.sh'
    echo "HERE=\"$HERE\""
    echo 'AENEAS_LEAN="$AENEAS_HOME/backends/lean"'
    echo "TIMEOUT=$TIMEOUT; CORES=\"$CORES\""
    # CERTS is referenced by the cross-check inside Phase 3c.
    sed -n '/^CERTS=(/,/^)/p' "$HERE/check.sh"
    # `$0` inside Phase 3c must resolve to the shipping check.sh, not to this
    # driver, or the apex-name recovery would read the wrong file.
    # Stop at the next phase marker, not at a blank echo: a terminator that is
    # not itself a phase boundary breaks the moment the phase's body changes.
    awk '/^# ── Phase 3c/{f=1} f&&/^# ── Phase /&&!/Phase 3c/{exit} f{print}' "$HERE/check.sh" \
      | sed "s|\"\$0\"|\"$HERE/check.sh\"|g"
  } > "$DRIVER"
  if [ "$(wc -l < "$DRIVER")" -lt 60 ]; then
    echo "FATAL: could not lift Phase 3c out of check.sh — the phase markers moved."
    echo "This self-test must attack the shipping gate; refusing to run against nothing."
    exit 1
  fi
}
build_driver

recompile_audit() {
  ( cd "$AENEAS_LEAN" && lake env bash -c "
      set -uo pipefail
      cd '$HERE/gen' && export LEAN_PATH=\"\$LEAN_PATH:\$PWD:$HERE\"
      cd '$HERE'
      LEAN_TIMEOUT=$TIMEOUT '$HERE/lean-guard' Proofs/Audit.lean
  " ) >/dev/null 2>&1
}

expect() {   # expect <name> <expected-rc> <required-substring>
  local name="$1" want_rc="$2" want_txt="$3" out rc
  out=$(bash "$DRIVER" 2>&1); rc=$?
  if [ "$rc" -ne "$want_rc" ]; then
    echo "  FAIL $name: exit $rc, expected $want_rc"; FAILURES=$((FAILURES+1)); return
  fi
  if ! grep -qF "$want_txt" <<<"$out"; then
    echo "  FAIL $name: exit code right, diagnostic wrong (rejected for the wrong reason)"
    echo "        wanted: $want_txt"
    echo "        got:    $(tr '\n' '|' <<<"$out" | cut -c1-260)"
    FAILURES=$((FAILURES+1)); return
  fi
  echo "  ok   $name"
}

echo "=== selftest-statements: attacking check.sh Phases 0b and 3c ==="

# ── 0. THE SUBJECT. The certificates are stated ABOUT the extracted model in
#      gen/. A statement names an extracted function; editing that function's
#      BODY changes what the theorem is about while leaving every statement,
#      every cone and the Phase 3c digest byte-identical. Demonstrated on
#      2026-07-28: risc0 and betrusted ship different extracted models and
#      produce the SAME audit-manifest digest. Only the byte pin separates them.
expect0b() {
  local name="$1" want_rc="$2" want_txt="$3" out rc
  out=$(bash "$DRIVER0B" 2>&1); rc=$?
  if [ "$rc" -ne "$want_rc" ]; then
    echo "  FAIL $name: exit $rc, expected $want_rc"; FAILURES=$((FAILURES+1)); return
  fi
  if ! grep -qF "$want_txt" <<<"$out"; then
    echo "  FAIL $name: exit code right, diagnostic wrong (rejected for the wrong reason)"
    echo "        wanted: $want_txt"; FAILURES=$((FAILURES+1)); return
  fi
  echo "  ok   $name"
}
expect0b "model pin: baseline green" 0 "match their pins"
GENF=$(awk 'NR==1{print $2}' "$HERE/GEN-MODEL.sha256")
cp "$HERE/gen/$GENF" "$STASH/genfile.bak"
printf '\n-- edited\n' >> "$HERE/gen/$GENF"
expect0b "model pin: edited model body caught" 1 "does not match its pin"
cp "$STASH/genfile.bak" "$HERE/gen/$GENF"
cp "$HERE/gen/$GENF" "$HERE/gen/$(dirname "$GENF")/ZZExtra.lean"
expect0b "model pin: an unlisted model file caught" 1 "does not match GEN-MODEL.sha256"
rm -f "$HERE/gen/$(dirname "$GENF")/ZZExtra.lean"

# ── 1. Baseline: untouched repository passes and reports what it bound.
expect "baseline green, manifest digest matches" 0 "audit-manifest sha256"

# ── 2. WIDEN THE POLICY. Add one name to the apex boundary.
#      The policy IS inside the digest, but this attack never reaches the
#      digest: because the apex tier requires EXACT cone equality, a widened
#      boundary immediately shows up as `missing=` on all four apex
#      certificates. That is a strictly stronger rejection than a digest
#      mismatch — it names which certificates stopped matching instead of
#      merely reporting that some byte moved. Asserted here as such, because a
#      test that demanded the weaker diagnostic would go red the day the
#      stronger guard started working.
python3 - "$HERE/Proofs/Audit.lean" <<'PY'
import sys, re
f = sys.argv[1]; s = open(f).read()
m = re.search(r'^def apexExtra : List Name :=\n  \[(.*)\]$', s, re.M)
assert m, "apexExtra not found"
s = s.replace(m.group(0), m.group(0)[:-1] + ", `Classical.byContradiction]", 1)
open(f, "w").write(s)
PY
recompile_audit
expect "widened policy caught by the exact-cone requirement" 1 "missing=[Classical.byContradiction]"
cp "$STASH/Audit.lean" "$HERE/Proofs/Audit.lean"; recompile_audit

# ── 3. HAND-EDIT THE COMMITTED BLOCK. The digest still matches the emitted
#      block, so only the byte-comparison against the committed input can see
#      this. Without it the diff printed on a future failure would silently
#      compare against a doctored reference.
sed -i '2s/$/ TAMPERED/' "$HERE/AUDIT-MANIFEST.txt"
expect "hand-edited committed block caught" 1 "does not match the emitted block"
cp "$STASH/AUDIT-MANIFEST.txt" "$HERE/AUDIT-MANIFEST.txt"

# ── 4. DROP A CERTIFICATE FROM THE AUDITOR — AND REFRESH THE DIGEST TO MATCH,
#      exactly as an author covering their tracks would. The digest and the
#      committed block are now perfectly consistent with each other. The only
#      thing that can still object is the cross-check against the certificate
#      list this script derives from its OWN two sources.
python3 - "$HERE/Proofs/Audit.lean" <<'PY'
import sys, re
f = sys.argv[1]; s = open(f).read()
lines = s.splitlines(True)
i = next(k for k, l in enumerate(lines) if l.strip().startswith(', (`') and 'kernel3)' in l)
del lines[i]
open(f, "w").write("".join(lines))
PY
recompile_audit
# Regenerate the committed block and re-pin the digest from the tampered run.
TAMPERED_OUT=$(cd "$AENEAS_LEAN" && lake env bash -c "
  set -uo pipefail
  cd '$HERE/gen' && export LEAN_PATH=\"\$LEAN_PATH:\$PWD:$HERE\"
  cd '$HERE'
  LEAN_TIMEOUT=$TIMEOUT '$HERE/lean-guard' Proofs/Audit.lean 2>&1")
awk '/AUDIT-MANIFEST-BEGIN/{f=1;next} /AUDIT-MANIFEST-END/{f=0} f' <<<"$TAMPERED_OUT" > "$HERE/AUDIT-MANIFEST.txt"
NEWSHA=$(sha256sum "$HERE/AUDIT-MANIFEST.txt" | cut -d' ' -f1)
sed -i "s/^EXPECTED_AUDIT_SHA256=.*/EXPECTED_AUDIT_SHA256=\"$NEWSHA\"/" "$HERE/check.sh"
build_driver
expect "dropped certificate caught by the cross-check, digest refreshed or not" 1 "have drifted"
cp "$STASH/Audit.lean" "$HERE/Proofs/Audit.lean"
cp "$STASH/AUDIT-MANIFEST.txt" "$HERE/AUDIT-MANIFEST.txt"
cp "$STASH/check.sh" "$HERE/check.sh"
build_driver
recompile_audit

# ── 5. THE REAL ONE: gut a certificate's STATEMENT while preserving its axiom
#      cone. Every earlier phase passes this; only the statement binding sees it.
if [ "$SKIP_SLOW" = "1" ]; then
  echo "  skip gutted-statement case (SKIP_SLOW=1) — the fast gates above do not cover it"
else
  # A TERMINAL certificate: nothing else in the corpus consumes it. Gutting a
  # load-bearing one simply breaks its consumers and the module stops
  # compiling, which demonstrates the compiler working, not this gate.
  GUT_MOD=FieldMain
  GUT_CERT=CurveFieldProofs.fieldImplementation
  cp "$HERE/Proofs/$GUT_MOD.lean" "$STASH/gut.lean"
  python3 - "$HERE/Proofs/$GUT_MOD.lean" "$GUT_CERT" <<'PY'
import sys, re
f, cert = sys.argv[1], sys.argv[2]
short = cert.split('.')[-1]
s = open(f).read()
m = re.search(r'^theorem %s\b' % re.escape(short), s, re.M)
assert m, f"certificate {short} not found in {f}"
i = m.start()
# find the next top-level declaration after it
nxt = re.search(r'^(theorem|lemma|def|noncomputable def|end|/--|@\[)', s[i+10:], re.M)
assert nxt, "no following declaration"
j = i + 10 + nxt.start()
# Same cone (Classical.em pulls in Classical.choice/propext), utterly different claim.
gut = "theorem %s : (∀ p : Prop, p ∨ ¬p) := Classical.em\n\n" % short
open(f, "w").write(s[:i] + gut + s[j:])
PY
  ( cd "$AENEAS_LEAN" && lake env bash -c "
      set -uo pipefail
      cd '$HERE/gen' && export LEAN_PATH=\"\$LEAN_PATH:\$PWD:$HERE\"
      cd '$HERE'
      LEAN_TIMEOUT=$TIMEOUT '$HERE/lean-guard' Proofs/$GUT_MOD.lean
  " ) >/dev/null 2>&1 || { echo "  FAIL setup: the gutted module did not compile"; FAILURES=$((FAILURES+1)); }
  recompile_audit
  expect "gutted statement caught (cone unchanged)" 1 "audit-manifest digest mismatch"
  cp "$STASH/gut.lean" "$HERE/Proofs/$GUT_MOD.lean"
  ( cd "$AENEAS_LEAN" && lake env bash -c "
      set -uo pipefail
      cd '$HERE/gen' && export LEAN_PATH=\"\$LEAN_PATH:\$PWD:$HERE\"
      cd '$HERE'
      LEAN_TIMEOUT=$TIMEOUT '$HERE/lean-guard' Proofs/$GUT_MOD.lean
  " ) >/dev/null 2>&1
  recompile_audit
fi

# ── 6. Restored: green again, and the working tree is as we found it.
expect "restored to green" 0 "audit-manifest sha256"
# String comparison, not diff of process substitutions: for a clean tree the
# variable is empty and `echo` emits a blank line the raw command does not,
# which reports a difference precisely when there is none.
TREE_NOW="$(cd "$HERE/.." && git status --porcelain)"
if [ "$TREE_AT_START" != "$TREE_NOW" ]; then
  echo "  FAIL restore: the working tree differs from how this test found it:"
  diff <(printf '%s\n' "$TREE_AT_START") <(printf '%s\n' "$TREE_NOW") | sed 's/^/        /'
  FAILURES=$((FAILURES+1))
else
  echo "  ok   working tree restored to its starting state"
fi

echo ""
if [ "$FAILURES" -eq 0 ]; then
  echo "SELFTEST PASSED — Phase 3c rejects statement- and specification-level"
  echo "tampering that moves no axiom cone, for the stated reason in each case."
  exit 0
fi
echo "SELFTEST FAILED: $FAILURES check(s) did not behave as claimed."
exit 1
