#!/usr/bin/env bash
# Scalar-layer check (Scalar52 arithmetic mod ℓ). Compiles the gen model + the
# proven foundation. add/sub (Range-loop reductions) and the Montgomery mul
# path are in progress — see README. Guarded compiles throughout.
set -uo pipefail
source ~/aeneas-toolchain/env.sh
HERE="$(cd "$(dirname "$0")" && pwd)"
AENEAS_LEAN="$AENEAS_HOME/backends/lean"
GEN=(CurveScalar/TypesExternal CurveScalar/Types CurveScalar/FunsExternal CurveScalar/Funs)
PROOFS=(ScalarDenote ScalarLoop ScalarSubSpec ScalarAddSpec ScalarMulSpec ScalarMontSpec ScalarReduceSpec ScalarFullMulSpec ScalarMain ScalarWideSpec ScalarBytesSpec ScalarUnpackSpec)

echo "=== stub/axiom audit ==="
grep -rnE '^(private |protected |noncomputable )*axiom ' "$HERE"/Proofs/Scalar*.lean 2>/dev/null && { echo "axiom under Proofs/"; exit 1; }
echo "  clean"
echo "=== compile (guarded) ==="
cd "$AENEAS_LEAN"
lake env bash -c "
  set -uo pipefail
  cd '$HERE/gen' && export LEAN_PATH=\"\$LEAN_PATH:\$PWD:$HERE\"
  for m in ${GEN[*]}; do echo \"  · gen \$m\"; LEAN_TIMEOUT=300 LEAN_MEM_MB=6144 '$HERE/lean-guard' \"\$m.lean\" || exit 1; done
  cd '$HERE'
  for m in ${PROOFS[*]}; do echo \"  · proof \$m\"; LEAN_TIMEOUT=300 LEAN_MEM_MB=4096 '$HERE/lean-guard' \"Proofs/\$m.lean\" || exit 1; done
" || { echo FAIL; exit 1; }
echo "=== Phase 3: axiom audit (kernel-level) ==="
cd "$AENEAS_LEAN"
lake env bash -c "
  set -uo pipefail
  export LEAN_PATH=\"\$LEAN_PATH:$HERE/gen:$HERE\"
  cd '$HERE'
  AUD=\$(mktemp '$HERE/.audit-scalar-XXXX.lean')
  { echo 'import Proofs.ScalarMain'; echo 'import Proofs.ScalarWideSpec'; echo 'import Proofs.ScalarUnpackSpec'; echo '#print axioms ScalarProofs.L_val'
    echo '#print axioms ScalarProofs.sub_loop_spec'
    echo '#print axioms ScalarProofs.cond_add_l_one_spec'; echo '#print axioms ScalarProofs.sub_val_spec'; echo '#print axioms ScalarProofs.add_val_spec'; echo '#print axioms ScalarProofs.mul_internal_spec'
    echo '#print axioms ScalarProofs.part1_spec'; echo '#print axioms ScalarProofs.montgomery_reduce_spec'; echo '#print axioms ScalarProofs.mul_spec'; echo '#print axioms ScalarProofs.scalarImplementation'; echo '#print axioms ScalarProofs.montgomery_mul_spec'; echo '#print axioms ScalarProofs.bytes_unpack_spec'; } > \"\$AUD\"
  OUT=\$(LEAN_TIMEOUT=120 LEAN_MEM_MB=4096 '$HERE/lean-guard' \"\$AUD\" 2>&1)
  echo \"\$OUT\"
  rm -f \"\$AUD\" \"\${AUD%.lean}.olean\"
  N=\$(echo \"\$OUT\" | grep -cF \"depends on axioms: [propext, Classical.choice, Quot.sound]\" || true)
  [ \"\$N\" -eq 12 ] || { echo \"AXIOM AUDIT FAILED: \$N/12 clean\"; exit 1; }
" || { echo FAIL; exit 1; }
echo "  L_val axiom-clean"

echo ""
echo "SCALAR LAYER COMPLETE: add, sub, mul (Montgomery reduction, double round through RR) proven mod ℓ; aggregate certificate scalarImplementation kernel-audited."
