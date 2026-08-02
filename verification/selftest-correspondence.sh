#!/usr/bin/env bash
# ─────────────────────────────────────────────────────────────────────────────
# selftest-correspondence.sh — attacks check.sh Phase 0d.
#
# Phase 0d asserts HOW each external the extraction asks for is answered: with
# an assumption in the hand-written model, or with a proof already in the
# extracted corpus. The second class is the one the documents make a claim
# about — the curve calls and curve types are said to resolve to the proven
# model's own definitions rather than to axioms — and that claim was prose
# until this phase existed.
#
#   0  control: the committed table matches the files
#   1  the extraction asks for something NOTHING provides -> UNRESOLVED
#   2  a PROVEN external answered by an axiom in the model instead. This is the
#      attack that matters: a proof silently downgraded to an assumption, in a
#      name whose spelling does not change anywhere else.
#   3  a row deleted from the committed table -> drift
#   4  a row's verdict edited in the committed table -> drift
#
# No Lean: Phase 0d is pure text over gen/. Seconds, not minutes.
# ─────────────────────────────────────────────────────────────────────────────
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
FAILURES=0
STASH="$(mktemp -d)"

cleanup() {
  [ -f "$STASH/corr" ]  && cp "$STASH/corr"  "$HERE/MODEL-CORRESPONDENCE.txt"
  [ -f "$STASH/model" ] && cp "$STASH/model" "$HERE/$MODEL_REL"
  [ -f "$STASH/tmpl" ]  && cp "$STASH/tmpl"  "$HERE/$TMPL_REL"
  rm -rf "$STASH"
}

# Derive the victims from this repo rather than naming them: the forks do not
# share a gen/ layout (anza has no CurveSig crate at all, so it has no PROVEN
# rows and case 2 does not apply there).
TMPL_REL=$(cd "$HERE" && ls gen/*/FunsExternal_Template.lean | head -1)
MODEL_REL="${TMPL_REL/_Template/}"
PROVEN_ROW=$(grep -m1 '|PROVEN$' "$HERE/MODEL-CORRESPONDENCE.txt" || true)

trap cleanup EXIT INT TERM
cp "$HERE/MODEL-CORRESPONDENCE.txt" "$STASH/corr"
cp "$HERE/$MODEL_REL"               "$STASH/model"
cp "$HERE/$TMPL_REL"                "$STASH/tmpl"

# Phase 0d lifted from the shipping button.
awk '/^# ── Phase 0d/{f=1} f&&/^# ── (Phase 1|Phases end)/{exit} f{print}' \
  "$HERE/check.sh" > "$STASH/payload.sh"
{ echo 'set -euo pipefail'
  echo "HERE=\"$HERE\""
  cat "$STASH/payload.sh"
} > "$STASH/p0d.sh"
# Assert on the PAYLOAD, not the concatenation: a marker appearing in the
# preamble would otherwise satisfy a check meant to prove the lift landed.
for want in 'Phase 0d' 'MODEL CORRESPONDENCE' 'model-correspondence.py'; do
  grep -qF "$want" "$STASH/payload.sh" || {
    echo "FATAL: the lifted driver has no '$want' — check.sh's phase markers moved."; exit 1; }
done
"$HERE/lift-guard.sh" "$STASH/payload.sh" "$STASH/p0d.sh" "check.sh Phase 0d" || exit 1

expect() {  # expect <label> <want-rc> <want-substring>
  local label="$1" want_rc="$2" want_txt="$3" out rc
  out=$(bash "$STASH/p0d.sh" 2>&1); rc=$?
  if [ "$rc" -ne "$want_rc" ]; then
    echo "  ✗ $label: exit $rc, expected $want_rc"; tail -6 <<<"$out" | sed 's/^/      /'
    FAILURES=$((FAILURES+1)); return
  fi
  if ! grep -qF "$want_txt" <<<"$out"; then
    echo "  ✗ $label: exit code right, diagnostic wrong (rejected for the wrong reason)"
    echo "      wanted: $want_txt"; tail -6 <<<"$out" | sed 's/^/      /'
    FAILURES=$((FAILURES+1)); return
  fi
  echo "  ✓ $label"
}

echo "=== selftest-correspondence: attacking check.sh Phase 0d ==="
echo "    template: $TMPL_REL"

expect "control: the committed table matches the files" 0 "answered by PROVEN definitions"

# ── 1. the extraction asks for something nothing provides ──────────────────
printf '\naxiom selftest_unprovided_external : Nat\n' >> "$HERE/$TMPL_REL"
expect "case 1: an external nothing provides" 1 "MODEL CORRESPONDENCE FAILED"
cp "$STASH/tmpl" "$HERE/$TMPL_REL"

# ── 2. a proof silently downgraded to an assumption ────────────────────────
# Answer a PROVEN external with an axiom in the model. The name does not change
# anywhere; only the way it is answered does. Nothing else in the button sees
# this: the byte pins still match their files, the compiler is content because
# the signature is unchanged, and no certificate's cone moves unless something
# happens to depend on it.
if [ -n "$PROVEN_ROW" ]; then
  PROVEN_NAME=$(cut -d'|' -f2 <<<"$PROVEN_ROW")
  PROVEN_TMPL=$(cut -d'|' -f1 <<<"$PROVEN_ROW")
  VICTIM_MODEL="gen/${PROVEN_TMPL}.lean"
  cp "$HERE/$VICTIM_MODEL" "$STASH/model2"
  printf '\naxiom %s : Nat\n' "$PROVEN_NAME" >> "$HERE/$VICTIM_MODEL"
  expect "case 2: a PROVEN external downgraded to an assumption" 1 "MODEL CORRESPONDENCE DRIFT"
  cp "$STASH/model2" "$HERE/$VICTIM_MODEL"
else
  echo "  · case 2 skipped: this fork's extraction has no PROVEN externals"
fi

# ── 3/4. the committed table itself ────────────────────────────────────────
# Delete the FIRST row, whatever its verdict. An earlier draft deleted the
# PROVEN rows, which was vacuous on anza — that fork's extraction has none, so
# nothing was removed, the table still matched, and the case passed by testing
# nothing. Pick a row every fork is guaranteed to have.
sed '0,/|/{/|/d}' "$STASH/corr" > "$HERE/MODEL-CORRESPONDENCE.txt"
if ! diff -q "$STASH/corr" "$HERE/MODEL-CORRESPONDENCE.txt" >/dev/null; then
  expect "case 3: a row deleted from the committed table" 1 "MODEL CORRESPONDENCE DRIFT"
else
  echo "  ✗ case 3: the table was not actually modified — the case is vacuous"
  FAILURES=$((FAILURES+1))
fi
cp "$STASH/corr" "$HERE/MODEL-CORRESPONDENCE.txt"

sed -i '0,/|MODEL$/s/|MODEL$/|PROVEN/' "$HERE/MODEL-CORRESPONDENCE.txt"
expect "case 4: a verdict edited in the committed table" 1 "MODEL CORRESPONDENCE DRIFT"
cp "$STASH/corr" "$HERE/MODEL-CORRESPONDENCE.txt"

# ── 5/6. THE ROUND-7 FINDINGS, so they cannot regress ──────────────────────
# Both were real. Case 5 is GPT-5.6's constructive counterexample: a definition
# that exists ONLY inside a block comment was read as a real declaration, so the
# scanner reported PROVEN for a name Lean resolves to an axiom. Case 6 is the
# one that was live in four committed tables: Aeneas wraps long declarations,
# the old scanner required keyword and name on one physical line, and so it
# SILENTLY DROPPED them — nine to ten externals per fork had no row at all.
#
# Case 6 is the more important of the two. A gate that drops what it cannot
# read is worse than no gate: it prints green across a gap that is invisible in
# the diff. The scanner must now FAIL rather than skip.
CX=$(mktemp -d)
mkdir -p "$CX/gen/Forged"
printf 'axiom Forged.value : Nat\n' > "$CX/gen/Forged/FunsExternal_Template.lean"
printf 'axiom\n  Forged.value : Nat\n'  > "$CX/gen/Forged/FunsExternal.lean"
printf '/-\nnamespace Forged\ndef value : Nat := 0\nend Forged\n-/\n' > "$CX/gen/Forged/Funs.lean"
OUT=$(python3 "$HERE/model-correspondence.py" "$CX" 2>&1)
if grep -q 'Forged.value|MODEL' <<<"$OUT"; then
  echo "  ✓ case 5: a definition inside a block comment is not read as a declaration"
else
  echo "  ✗ case 5: comment-only definition mis-read — scanner says:"; sed 's/^/      /' <<<"$OUT"
  FAILURES=$((FAILURES+1))
fi

printf 'axiom\n  Forged.wrapped\n  :\n  Nat\n' >> "$CX/gen/Forged/FunsExternal_Template.lean"
OUT=$(python3 "$HERE/model-correspondence.py" "$CX" 2>&1); RC=$?
if [ "$RC" -ne 0 ] && grep -q 'UNRESOLVED\|Forged.wrapped' <<<"$OUT"; then
  echo "  ✓ case 6: a declaration whose name wraps to the next line is SEEN, not dropped"
else
  echo "  ✗ case 6: wrapped declaration dropped or mis-handled (rc=$RC):"; sed 's/^/      /' <<<"$OUT"
  FAILURES=$((FAILURES+1))
fi

printf 'axiom\n' > "$CX/gen/Forged/FunsExternal_Template.lean"
OUT=$(python3 "$HERE/model-correspondence.py" "$CX" 2>&1); RC=$?
if [ "$RC" -eq 2 ] && grep -q 'fails closed' <<<"$OUT"; then
  echo "  ✓ case 7: an unparseable declaration stops the scanner (exit 2), never silence"
else
  echo "  ✗ case 7: unparseable declaration did not fail closed (rc=$RC)"
  FAILURES=$((FAILURES+1))
fi
rm -rf "$CX"

expect "restored: the table matches again" 0 "answered by PROVEN definitions"

echo ""
if [ "$FAILURES" -eq 0 ]; then
  echo "SELFTEST PASSED — an external cannot change how it is answered, and a"
  echo "proof cannot be downgraded to an assumption, without failing the button."
  exit 0
fi
echo "SELFTEST FAILED: $FAILURES case(s) did not behave as claimed."
exit 1
