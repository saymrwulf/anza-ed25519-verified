#!/usr/bin/env bash
# ─────────────────────────────────────────────────────────────────────────────
# check-scalar.sh — THE SECOND BUTTON (Scalar52 arithmetic mod ℓ).
#
# Runs against the merged gen/CurveField universe (the scalar module lives
# there since the merge; see extract.sh). Guarded compiles throughout.
#
# Brought to the same standard as check.sh on 2026-07-30 (P0-b). Before that
# it was the weakest link in the estate, and increasingly so as the main button
# was hardened: no source-integrity check, no harness pin, no dead-file gate,
# no declaration inventory, an EVADABLE source-text grep for axioms where the
# main button asks the kernel, and a count of matching output lines where the
# main button asserts each certificate's cone individually.
#
# Phases:
#   0  source integrity + harness pin (so running this button alone is also
#      protected, not only running it after check.sh)
#   1  the two-button seam: every shipped proof source belongs to exactly one
#      of the two manifests, asserted against check.sh's, both directions
#   2  compile the scalar layer, with a dead-file gate over Scalar*
#  2b  kernel-side axiom-declaration gate over the compiled artifacts
#  2c  environment-derived declaration inventory, diffed both directions
#   3  per-certificate exact-cone audit
# ─────────────────────────────────────────────────────────────────────────────
set -uo pipefail
source ~/aeneas-toolchain/env.sh
HERE="$(cd "$(dirname "$0")" && pwd)"
AENEAS_LEAN="$AENEAS_HOME/backends/lean"
TIMEOUT="${LEAN_TIMEOUT:-300}"
CORES="${LEAN_MAX_CORES:-0-3}"
GEN=(CurveField/TypesExternal CurveField/Types CurveField/FunsExternal CurveField/Funs)
PROOFS=(ScalarDenote ScalarLoop ScalarSubSpec ScalarAddSpec ScalarMulSpec ScalarMontSpec ScalarReduceSpec ScalarFullMulSpec ScalarMain ScalarWideSpec ScalarBytesSpec ScalarUnpackSpec ScalarFromBytesSpec)
# Fully-qualified scalar certificates. Each must report EXACTLY the standard
# three axioms — asserted per certificate, not by counting how many lines of
# output happened to match. A count cannot tell you WHICH certificate is clean.
CERTS=(
  ScalarProofs.L_val
  ScalarProofs.sub_loop_spec
  ScalarProofs.cond_add_l_one_spec
  ScalarProofs.sub_val_spec
  ScalarProofs.add_val_spec
  ScalarProofs.mul_internal_spec
  ScalarProofs.part1_spec
  ScalarProofs.montgomery_reduce_spec
  ScalarProofs.mul_spec
  ScalarProofs.scalarImplementation
  ScalarProofs.montgomery_mul_spec
  ScalarProofs.bytes_unpack_spec
  ScalarProofs.from_bytes_wide_spec
)
EXPECTED="[propext, Classical.choice, Quot.sound]"

# ── Phase 0: source integrity + harness pin ─────────────────────────────────
echo "=== Phase 0: source integrity + harness pin ==="
free -m | awk '/Mem:/{if($7<2048){print "FATAL: <2GB RAM available — refusing to compile"; exit 1}}' || exit 1
for f in "$HERE"/Proofs/Scalar*.lean; do
  [ -f "$f" ] || continue
  if ! grep -qE '^(/-|import |namespace |theorem |def |open |set_option |--)' "$f"; then
    echo "CORRUPTED: $f is not Lean source (olean clobber?). Restore: git checkout HEAD -- $f"
    exit 1
  fi
done
# The pin file and its policy live with check.sh; this button verifies the same
# pins so that running it ALONE is protected too. If check.sh is absent the
# harness is not pinned and that is a hard stop, not a warning.
if [ ! -s "$HERE/HARNESS.sha256" ]; then
  echo "FATAL: HARNESS.sha256 is missing or empty — the harness is unpinned."; exit 1
fi
if ! ( cd "$HERE" && sha256sum -c --quiet HARNESS.sha256 ) ; then
  echo "FATAL: a harness file does not match its pin. The button you are running"
  echo "is not the button that was reviewed."; exit 1
fi
echo "  sources valid; $(wc -l < "$HERE/HARNESS.sha256") harness files match their pins"

# ── Phase 1: the two-button seam ────────────────────────────────────────────
# The mirror of check.sh's Phase 1b. Each button reads the other's manifest, so
# a new Proofs/ScalarX.lean cannot be absent from one by exemption and from the
# other by omission — which is exactly what it was until today.
echo "=== Phase 1: two-button seam ==="
SEAMFAIL=0
MAIN_SH="$HERE/check.sh"
if [ ! -f "$MAIN_SH" ]; then
  echo "  FATAL: check.sh is absent — most of the corpus would go unchecked."; exit 1
fi
MAIN_MANIFEST=$(sed -n '/^PROOFS=(/,/^)/p' "$MAIN_SH" | grep -oE '^  [A-Za-z][A-Za-z0-9]*' | tr -d ' ' | sort -u)
if [ -z "$MAIN_MANIFEST" ]; then
  echo "  FATAL: could not read check.sh's manifest; refusing to guess its scope."; exit 1
fi
SCALAR_MANIFEST=$(printf '%s\n' "${PROOFS[@]}" | sort -u)
for f in "$HERE"/Proofs/*.lean; do
  b=$(basename "$f" .lean)
  case "$b" in AxiomCheck|Inventory|InventoryBasic|InventoryCore|InventoryScalar) continue;; esac
  inm=0; ins=0
  grep -qx "$b" <<<"$MAIN_MANIFEST"   && inm=1
  grep -qx "$b" <<<"$SCALAR_MANIFEST" && ins=1
  if [ $((inm + ins)) -eq 0 ]; then
    echo "  ORPHAN: Proofs/$b.lean is in NEITHER manifest — compiled and audited by no button"; SEAMFAIL=1
  elif [ $((inm + ins)) -eq 2 ]; then
    echo "  DOUBLE-CLAIMED: Proofs/$b.lean is in BOTH manifests"; SEAMFAIL=1
  fi
done
[ "$SEAMFAIL" = 0 ] && echo "  every proof source belongs to exactly one button"
[ "$SEAMFAIL" = 0 ] || { echo "SEAM CHECK FAILED"; exit 1; }

# ── Phase 2: compile ────────────────────────────────────────────────────────
echo "=== Phase 2: compile (guarded) ==="
cd "$AENEAS_LEAN"
lake env bash -c "
  set -uo pipefail
  cd '$HERE/gen' && export LEAN_PATH=\"\$LEAN_PATH:\$PWD:$HERE\"
  for m in ${GEN[*]}; do echo \"  · gen \$m\"; LEAN_TIMEOUT=$TIMEOUT LEAN_MEM_MB=6144 '$HERE/lean-guard' \"\$m.lean\" || exit 1; done
  cd '$HERE'
  for m in ${PROOFS[*]}; do echo \"  · proof \$m\"; LEAN_TIMEOUT=$TIMEOUT LEAN_MEM_MB=4096 '$HERE/lean-guard' \"Proofs/\$m.lean\" || exit 1; done
  # NO NAME-PREFIX DEAD-FILE GATE HERE. A Scalar* NAME does not imply this
  # button owns the file: Proofs/ScalarPackSpec.lean is in check.sh's manifest,
  # and a prefix gate demanded it be in this one. Phase 1 above is the correct
  # test and strictly stronger — it requires every proof source to be in
  # EXACTLY ONE of the two manifests, by membership rather than by spelling.
" || { echo FAIL; exit 1; }

# ── Phase 2b: kernel-side axiom-declaration gate ────────────────────────────
# The source-text grep this button used until today is evadable four ways on
# Lean v4.30.0-rc2 (indented, @[simp], unsafe, and name-on-the-next-line — all
# compile, none match an anchored pattern). Ask the kernel instead, reading the
# compiled artifacts, exactly as check.sh Phase 2b does.
echo "=== Phase 2b: kernel-side axiom-declaration gate ==="
# The scanned set is this button's MANIFEST, not everything spelled Scalar*.
# Proofs/ScalarPackSpec.lean is compiled by check.sh, so a glob swept in an
# artifact this button does not own — and on a tree where check.sh had not run,
# that olean is absent and the coverage count would fail for a false reason.
SCALAR_OLEANS=$(printf '"%s.olean", ' "${PROOFS[@]}" | sed 's/, $//')
GATE=$(mktemp "$HERE/.axgate-scalar-XXXX.lean")
{
  echo "import Lean"
  echo "open Lean"
  echo "def expected : List String := [$SCALAR_OLEANS]"
  cat <<'LEANGATE'

run_cmd do
  let dir : System.FilePath := "Proofs"
  let mut errs : Array String := #[]
  let mut nMod := 0
  for name in expected do
    let p := dir / name
    -- FAIL CLOSED ON ABSENCE: a manifest module whose artifact is missing makes
    -- this gate vacuous for that module, which must be an error, not a skip.
    unless (← p.pathExists) do
      throwError "COVERAGE: {name} is in the manifest but its compiled artifact is absent"
    nMod := nMod + 1
    let (mod, _) ← readModuleData p
    for ci in mod.constants do
      if ci matches .axiomInfo _ then
        errs := errs.push s!"  {name}: {ci.name}"
  unless errs.isEmpty do
    throwError "AXIOM DECLARED in the scalar layer:\n{String.intercalate "\n" errs.toList}"
  logInfo s!"  kernel confirms: {nMod} compiled scalar modules (the manifest, by membership), none declares an axiom"
LEANGATE
} > "$GATE"
cd "$AENEAS_LEAN"
GATE_RC=0
lake env bash -c "
  set -uo pipefail
  cd '$HERE/gen' && export LEAN_PATH=\"\$LEAN_PATH:\$PWD:$HERE\"
  cd '$HERE'
  LEAN_TIMEOUT=$TIMEOUT LEAN_MAX_CORES=$CORES '$HERE/lean-guard' '$GATE'
" || GATE_RC=$?
rm -f "$GATE" "${GATE%.lean}.olean"
[ "$GATE_RC" -eq 0 ] || { echo "SCALAR AXIOM GATE FAILED"; exit 1; }

# ── Phase 2c: declaration inventory ─────────────────────────────────────────
# Until today these 13 modules were the only part of the proof corpus with no
# declaration inventory: check.sh Phase 2c covers the main chain and named them
# as uncovered on every run. This closes that.
echo "=== Phase 2c: scalar declaration inventory ==="
INVFAIL=0
INVLOG=$(mktemp /tmp/check-scalar-inv-XXXX.log)
cd "$AENEAS_LEAN"
lake env bash -c "
  set -uo pipefail
  cd '$HERE/gen' && export LEAN_PATH=\"\$LEAN_PATH:\$PWD:$HERE\"
  cd '$HERE'
  LEAN_TIMEOUT=$TIMEOUT LEAN_MEM_MB=8192 '$HERE/lean-guard' Proofs/InventoryScalar.lean
" > "$INVLOG" 2>&1 || { cat "$INVLOG"; echo "SCALAR INVENTORY COMPILE FAILED"; rm -f "$INVLOG"; exit 1; }
OBS=$(mktemp /tmp/check-scalar-obs-XXXX.log)
grep -E '^INV\|' "$INVLOG" > "$OBS"
grep '^INV-COUNT|' "$INVLOG" | tail -1 >> "$OBS"
"$HERE/inventory_gate.sh" "$OBS" "$HERE/inventory-allowlist-scalar.txt" || INVFAIL=1
rm -f "$INVLOG" "$OBS"
# The driver's corpus list must BE this script's manifest, both directions.
COVERED=$(grep -oE '`Proofs\.[A-Za-z0-9]+' "$HERE/Proofs/InventoryScalar.lean" | sed 's/`Proofs\.//' | sort -u)
for m in "${PROOFS[@]}"; do
  grep -qx "$m" <<<"$COVERED" || { echo "  UNINVENTORIED: $m is compiled here but the driver does not cover it"; INVFAIL=1; }
done
while read -r m; do
  [ -z "$m" ] && continue
  case " ${PROOFS[*]} " in (*" $m "*) ;; (*) echo "  PHANTOM: driver claims $m, not in this manifest"; INVFAIL=1;; esac
done <<<"$COVERED"
[ "$INVFAIL" = 0 ] || { echo "SCALAR INVENTORY FAILED"; exit 1; }

# ── Phase 3: per-certificate exact-cone audit ───────────────────────────────
# Was: count the lines of #print axioms output that matched the clean cone and
# compare against 13. A count cannot say WHICH certificate is clean, and it
# passes just as happily if one certificate's cone is reported twice. Each
# certificate is now asserted by name.
echo "=== Phase 3: per-certificate exact-cone audit ==="
cd "$AENEAS_LEAN"
AUD_OUT=$(lake env bash -c "
  set -uo pipefail
  export LEAN_PATH=\"\$LEAN_PATH:$HERE/gen:$HERE\"
  cd '$HERE'
  AUD=\$(mktemp '$HERE/.audit-scalar-XXXX.lean')
  { echo 'import Proofs.ScalarFromBytesSpec'; echo 'import Proofs.ScalarMain'; echo 'import Proofs.ScalarUnpackSpec'; echo 'import Proofs.ScalarWideSpec'
    for c in ${CERTS[*]}; do echo \"#print axioms \$c\"; done; } > \"\$AUD\"
  OUT=\$(LEAN_TIMEOUT=$TIMEOUT LEAN_MEM_MB=4096 '$HERE/lean-guard' \"\$AUD\" 2>&1)
  rm -f \"\$AUD\" \"\${AUD%.lean}.olean\"
  echo \"\$OUT\"
") || { echo "$AUD_OUT"; echo "SCALAR AUDIT COMPILE FAILED"; exit 1; }
FLAT=$(tr '\n' ' ' <<<"$AUD_OUT" | tr -s ' ')
AUDFAIL=0
for c in "${CERTS[@]}"; do
  grep -qF "'$c' depends on axioms: $EXPECTED" <<<"$FLAT" \
    || { echo "  NOT CLEAN or NOT FOUND: $c"; AUDFAIL=1; }
done
if [ "$AUDFAIL" != 0 ]; then
  echo "SCALAR AXIOM AUDIT FAILED"; echo "$AUD_OUT" | tail -20 | sed 's/^/    /'; exit 1
fi
echo "  ${#CERTS[@]}/${#CERTS[@]} scalar certificates report exactly $EXPECTED"

echo ""
echo "SCALAR LAYER COMPLETE: add, sub, mul (Montgomery reduction, double round"
echo "through RR) proven mod ℓ; aggregate certificate scalarImplementation"
echo "kernel-audited; declaration surface inventoried; harness pinned."
