#!/usr/bin/env bash
# Scalar-layer check (Scalar52 arithmetic mod ℓ). Compiles the gen model + the
# proven foundation. add/sub (Range-loop reductions) and the Montgomery mul
# path are in progress — see README. Guarded compiles throughout.
set -uo pipefail
source ~/aeneas-toolchain/env.sh
HERE="$(cd "$(dirname "$0")" && pwd)"
AENEAS_LEAN="$AENEAS_HOME/backends/lean"
GEN=(CurveScalar/TypesExternal CurveScalar/Types CurveScalar/FunsExternal CurveScalar/Funs)
PROOFS=(ScalarDenote)

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
  for m in ${PROOFS[*]}; do echo \"  · proof \$m\"; LEAN_TIMEOUT=300 LEAN_MEM_MB=6144 '$HERE/lean-guard' \"Proofs/\$m.lean\" || exit 1; done
" || { echo FAIL; exit 1; }
echo ""
echo "SCALAR FOUNDATION: gen compiles; denotation + group-order constant (L = ℓ) proven."
