#!/usr/bin/env bash
# ─────────────────────────────────────────────────────────────────────────────
# selftest-scalar-statements.sh — adversarial self-test for check-scalar.sh
# Phase 3c, the scalar statement + specification binding.
#
# WHY THIS EXISTS. Round-7 review (GPT-5.6, register key
# `scalar-statements-unbound`, CRITICAL): the main button bound its 31
# certificates' elaborated statements and reachable specification bodies; this
# repository's scalar button bound NONE of its thirteen, while TRUSTED-BASE
# item 8 said the audit covers "every certificate". The binding was added in
# the same commit as this file. The reviewer asked for exactly two shipping
# attacks, and this file is those two:
#
#   1. same-cone theorem statement gutting;
#   2. a reachable reference body rewritten while name and cone remain fixed.
#
# Both are invisible to every earlier phase by construction. Phase 2b sees no
# new axiom; Phase 3's exact-cone audit sees the same three axioms; only the
# statement binding sees them.
#
# It extracts Phase 3c out of check-scalar.sh at run time, so it attacks THE
# SHIPPING GATE rather than a copy that can drift away from it.
#
# Requires a prior green scalar build. Recompiling the corpus is the expensive
# part; SKIP_SLOW=1 runs only the fast cases and SAYS SO rather than passing
# quietly over the two that matter.
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
TREE_AT_START="$(cd "$HERE/.." && git status --porcelain)"

cleanup() {
  [ -f "$STASH/gut.lean" ] && cp "$STASH/gut.lean" "$HERE/Proofs/ScalarMain.lean"
  [ -f "$STASH/den.lean" ] && cp "$STASH/den.lean" "$HERE/Proofs/ScalarDenote.lean"
  rm -rf "$STASH"
  rm -f "$HERE"/.scalar-audit-manifest.observed
}
trap cleanup EXIT INT TERM

DRIVER="$STASH/phase3c.sh"
PAYLOAD="$STASH/payload.sh"
build_driver() {
  awk '/^# ── Phase 3c/{f=1} f&&/^# ── (Phase |Phases end)/&&!/Phase 3c/{exit} f{print}' \
    "$HERE/check-scalar.sh" > "$PAYLOAD"
  { echo 'set -euo pipefail'  # -e matches the button; see lift-drivers-drop-errexit
    echo 'source ~/aeneas-toolchain/env.sh'
    echo "HERE=\"$HERE\""
    echo 'AENEAS_LEAN="$AENEAS_HOME/backends/lean"'
    echo "TIMEOUT=$TIMEOUT; CORES=\"$CORES\""
    # CERTS is referenced by the cross-check inside Phase 3c. Lifted VERBATIM
    # rather than re-derived, so this test cannot drift from the button's set.
    sed -n '/^CERTS=(/,/^)/p' "$HERE/check-scalar.sh"
    cat "$PAYLOAD"
  } > "$DRIVER"
  if [ "$(wc -l < "$PAYLOAD")" -lt 40 ]; then
    echo "FATAL: could not lift Phase 3c out of check-scalar.sh — the markers moved."
    exit 1
  fi
  grep -qF 'SCALAR-AUDIT-MANIFEST-BEGIN' "$PAYLOAD" || {
    echo "FATAL: the lifted payload does not read the scalar audit block."; exit 1; }
  "$HERE/lift-guard.sh" "$PAYLOAD" "$DRIVER" "check-scalar.sh Phase 3c" || exit 1
}

recompile() {   # recompile <module>
  ( cd "$AENEAS_LEAN" && lake env bash -c "
      set -uo pipefail
      cd '$HERE/gen' && export LEAN_PATH=\"\$LEAN_PATH:\$PWD:$HERE\"
      cd '$HERE'
      LEAN_TIMEOUT=$TIMEOUT LEAN_MAX_CORES=$CORES '$HERE/lean-guard' Proofs/$1.lean
  " ) >/dev/null 2>&1
}

expect() {   # expect <name> <expected-rc> <required-substring>
  local name="$1" want_rc="$2" want_txt="$3" out rc
  out=$(bash "$DRIVER" 2>&1); rc=$?
  if [ "$rc" -ne "$want_rc" ]; then
    echo "  FAIL $name: exit $rc, expected $want_rc"
    tail -6 <<<"$out" | sed 's/^/        /'; FAILURES=$((FAILURES+1)); return
  fi
  if ! grep -qF "$want_txt" <<<"$out"; then
    echo "  FAIL $name: exit code right but diagnostic wrong (rejected for the wrong reason)"
    echo "        wanted substring: $want_txt"
    echo "        got: $(tr '\n' '|' <<<"$out" | cut -c1-260)"
    FAILURES=$((FAILURES+1)); return
  fi
  echo "  ok   $name"
}

echo "=== selftest-scalar-statements: attacking check-scalar.sh Phase 3c ==="
build_driver

# ── 1. Baseline: the untouched repository passes and reports what it bound.
expect "baseline green, statements bound" 0 "statements + reachable specification bodies bound"

# ── 2. HAND-EDIT THE COMMITTED BLOCK. The digest still matches what Lean
#      emits, so only the committed-copy comparison can see this.
cp "$HERE/SCALAR-AUDIT-MANIFEST.txt" "$STASH/manifest.bak"
sed -i '2s/$/ TAMPERED/' "$HERE/SCALAR-AUDIT-MANIFEST.txt"
expect "hand-edited committed block caught" 1 "does not match the emitted block"
cp "$STASH/manifest.bak" "$HERE/SCALAR-AUDIT-MANIFEST.txt"

if [ "$SKIP_SLOW" = "1" ]; then
  echo "  SKIPPED (SKIP_SLOW=1): the two attacks this file exists for — gutted"
  echo "  statement and rewritten specification body — were NOT run. The fast"
  echo "  case above does not cover either of them."
else
  # ── 3. ATTACK ONE: gut a certificate's STATEMENT, preserving its axiom cone.
  #      ScalarProofs.scalarImplementation is the aggregate and is TERMINAL —
  #      nothing outside its own module consumes it. Gutting a load-bearing
  #      certificate would simply break its consumers, which demonstrates the
  #      compiler working, not this gate.
  cp "$HERE/Proofs/ScalarMain.lean" "$STASH/gut.lean"
  python3 - "$HERE/Proofs/ScalarMain.lean" <<'PY'
import sys, re
f = sys.argv[1]
s = open(f).read()
m = re.search(r'^theorem scalarImplementation\b', s, re.M)
assert m, "scalarImplementation not found"
i = m.start()
nxt = re.search(r'^(theorem|lemma|def|noncomputable def|end|/--|@\[)', s[i+10:], re.M)
assert nxt, "no following declaration"
j = i + 10 + nxt.start()
# Same cone (Classical.em pulls in Classical.choice/propext), utterly different
# claim. Every earlier phase is satisfied; only the statement binding is not.
gut = "theorem scalarImplementation : (∀ p : Prop, p ∨ ¬p) := Classical.em\n\n"
open(f, "w").write(s[:i] + gut + s[j:])
PY
  recompile ScalarMain || { echo "  FAIL setup: the gutted module did not compile"; FAILURES=$((FAILURES+1)); }
  recompile ScalarAudit
  expect "gutted statement caught (cone unchanged)" 1 "audit-manifest digest mismatch"
  cp "$STASH/gut.lean" "$HERE/Proofs/ScalarMain.lean"; rm -f "$STASH/gut.lean"
  recompile ScalarMain; recompile ScalarAudit

  # ── 4. ATTACK TWO: rewrite a REACHABLE SPECIFICATION BODY while the
  #      certificate's name and cone stay fixed. This is the attack the whole
  #      block exists for: if a reference definition can be edited without
  #      notice, a certificate can be made to say `loop = loop` and every cone
  #      stays byte-identical.
  #
  #      scDenote is reachable from the scalar statements and its body is
  #      rewritten here to `id (…)`, which is DEFINITIONALLY EQUAL — so the
  #      corpus still compiles and every proof still typechecks. That is the
  #      point: the binding must be sensitive to the body AS WRITTEN, not
  #      merely to what it evaluates to. If the setup fails to compile this
  #      case reports FAIL rather than passing quietly.
  cp "$HERE/Proofs/ScalarDenote.lean" "$STASH/den.lean"
  python3 - "$HERE/Proofs/ScalarDenote.lean" <<'PY'
import sys
f = sys.argv[1]
s = open(f).read()
old = "def scDenote (a : Sc) : ZMod Ell := (scVal a : ZMod Ell)"
assert old in s, "scDenote body not in the expected form"
new = "def scDenote (a : Sc) : ZMod Ell := id (scVal a : ZMod Ell)"
open(f, "w").write(s.replace(old, new, 1))
PY
  if recompile ScalarDenote; then
    recompile ScalarAudit
    expect "rewritten specification body caught (name and cone unchanged)" 1 \
           "audit-manifest digest mismatch"
  else
    echo "  FAIL setup: the rewritten specification body did not compile —"
    echo "        this attack did NOT exercise the gate. Do not read the"
    echo "        surrounding passes as covering it."
    FAILURES=$((FAILURES+1))
  fi
  cp "$STASH/den.lean" "$HERE/Proofs/ScalarDenote.lean"; rm -f "$STASH/den.lean"
  recompile ScalarDenote; recompile ScalarAudit
fi

# ── 5. Restored: green again, and the working tree is as we found it.
expect "restored to green" 0 "statements + reachable specification bodies bound"
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
  echo "SELFTEST PASSED — scalar Phase 3c rejects statement- and specification-"
  echo "level tampering that moves no axiom cone, for the stated reason."
  exit 0
fi
echo "SELFTEST FAILED: $FAILURES check(s) did not behave as claimed."
exit 1
