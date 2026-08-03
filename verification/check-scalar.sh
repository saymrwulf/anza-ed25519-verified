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
PROOFS=(ScalarDenote ScalarLoop ScalarSubSpec ScalarAddSpec ScalarMulSpec ScalarMontSpec ScalarReduceSpec ScalarFullMulSpec ScalarMain ScalarWideSpec ScalarBytesSpec ScalarUnpackSpec ScalarFromBytesSpec ScalarAudit )
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

# ── Phase 3c: statement + specification binding ─────────────────────────────
# WHAT PHASE 3 DOES NOT ESTABLISH — and why this repository claimed something
# false for four rounds. Round-7 review (GPT-5.6, register key
# `scalar-statements-unbound`, CRITICAL): the main button bound its 31
# certificates' elaborated statements and reachable specification bodies; this
# button bound NONE of its thirteen. Meanwhile TRUSTED-BASE item 8 said the
# audit covers "every certificate" and each README said check.sh audits every
# certificate. Both were false across the 44-certificate repository surface.
#
# The finding was raised in round 7, was lost from the round-8 work list by an
# F-number collision between two reviewers, and was re-raised in round 8. It is
# closed here.
#
# Phase 3 proves each scalar certificate rests on exactly the standard three
# axioms. It does not say WHAT THE THEOREM SAYS. A certificate gutted to a
# tautology of the same cone passes it, and so does one whose reference
# definition has been redefined to BE the extracted code — at which point the
# theorem reads `loop = loop` and the cone is byte-identical.
#
# Proofs/ScalarAudit.lean emits a canonical block holding the policy constants,
# every scalar certificate's fully-elaborated statement (`pp.all`, so implicit
# arguments, instances and universes are all visible), and the body of every
# specification constant transitively reachable from those statements. This
# phase binds its SHA-256, and the block's INPUT is committed too, so a
# mismatch can be DIFFED rather than merely reported.
#
# To rotate deliberately: run this button, take the printed OBSERVED digest,
# and update the constant below AND SCALAR-AUDIT-MANIFEST.txt in the same
# reviewable commit. An author who edits a statement and refreshes the digest
# together is caught by reading the diff, not by this script.
EXPECTED_SCALAR_AUDIT_SHA256="0d942e472f5e5cbe428a824f4cd12dcb2d6b26e71db91a0665a4a90e341e9ce8"
echo "=== Phase 3c: scalar statement + specification binding ==="
cd "$AENEAS_LEAN"
# The compiler's own exit code is the primary signal; the transcript is only
# corroboration. A timeout or a memory clamp exits non-zero WITHOUT printing
# "error:", so grepping the text alone would let it through.
SAUD_RC=0
SAUD_OUT=$(lake env bash -c "
  set -uo pipefail
  cd '$HERE/gen' && export LEAN_PATH=\"\$LEAN_PATH:\$PWD:$HERE\"
  cd '$HERE'
  LEAN_TIMEOUT=$TIMEOUT LEAN_MEM_MB=8192 '$HERE/lean-guard' Proofs/ScalarAudit.lean 2>&1
" ) || SAUD_RC=$?
if [ "$SAUD_RC" -ne 0 ]; then
  echo "SCALAR AUDIT FAILED — Proofs/ScalarAudit.lean exited $SAUD_RC:"
  tail -20 <<<"$SAUD_OUT" | sed 's/^/    /'
  exit 1
fi
if grep -q 'error:' <<<"$SAUD_OUT"; then
  echo "SCALAR AUDIT FAILED — Proofs/ScalarAudit.lean did not elaborate cleanly:"
  grep 'error:' <<<"$SAUD_OUT" | head -20 | sed 's/^/    /'
  exit 1
fi
SBLOCK=$(awk '/SCALAR-AUDIT-MANIFEST-BEGIN/{f=1;next} /SCALAR-AUDIT-MANIFEST-END/{f=0} f' <<<"$SAUD_OUT")
# FAIL CLOSED ON ABSENCE: no block and a matching block must not share a path.
if [ -z "$SBLOCK" ]; then
  echo "SCALAR AUDIT FAILED — no SCALAR-AUDIT-MANIFEST block was emitted (fail-closed)."; exit 1
fi
SGOT_SHA=$(printf '%s\n' "$SBLOCK" | sha256sum | cut -d' ' -f1)
if [ "$SGOT_SHA" != "$EXPECTED_SCALAR_AUDIT_SHA256" ]; then
  printf '%s\n' "$SBLOCK" > "$HERE/.scalar-audit-manifest.observed"
  echo "SCALAR AUDIT FAILED — audit-manifest digest mismatch."
  echo "  expected: $EXPECTED_SCALAR_AUDIT_SHA256"
  echo "  observed: $SGOT_SHA"
  echo "  A statement, a specification body, or a policy constant changed."
  echo "  First differences against the committed block:"
  diff -u "$HERE/SCALAR-AUDIT-MANIFEST.txt" "$HERE/.scalar-audit-manifest.observed" 2>/dev/null \
    | head -30 | sed 's/^/    /' || echo "    (SCALAR-AUDIT-MANIFEST.txt absent — cannot diff)"
  rm -f "$HERE/.scalar-audit-manifest.observed"
  exit 1
fi
# The digest's INPUT must be committed and current, or the diff above would
# compare against a stale reference and quietly mislead the next reader.
if ! printf '%s\n' "$SBLOCK" | cmp -s - "$HERE/SCALAR-AUDIT-MANIFEST.txt"; then
  echo "SCALAR AUDIT FAILED — the committed SCALAR-AUDIT-MANIFEST.txt does not match the emitted block."
  echo "  (the digest matched, so the committed copy is stale — refresh it)"; exit 1
fi
# CROSS-CHECK the certificate list against the CERTS array Phase 3 audits, so a
# certificate cannot be dropped from the auditor's manifest unnoticed.
SAUD_CERTS=$(grep -o 'AUDITED-SCALAR-CERTIFICATES:.*' <<<"$SAUD_OUT" \
             | sed 's/AUDITED-SCALAR-CERTIFICATES: //' | tr ' ' '\n' | sort -u | sed '/^$/d')
SBASH_CERTS=$(printf '%s\n' "${CERTS[@]}" | sort -u)
if [ "$SAUD_CERTS" != "$SBASH_CERTS" ]; then
  echo "SCALAR AUDIT FAILED — the auditor's certificate set differs from this button's CERTS array:"
  diff <(echo "$SBASH_CERTS") <(echo "$SAUD_CERTS") | sed 's/^/    /'
  exit 1
fi
echo "  ${#CERTS[@]} scalar statements + reachable specification bodies bound, sha256 = $SGOT_SHA"
cd "$HERE"


echo ""
echo "SCALAR LAYER COMPLETE: add, sub, mul (Montgomery reduction, double round"
echo "through RR) proven mod ℓ; aggregate certificate scalarImplementation"
echo "kernel-audited; declaration surface inventoried; harness pinned."
