#!/usr/bin/env bash
# ─────────────────────────────────────────────────────────────────────────────
# check.sh — THE button. Compiles EVERY shipped .lean file and axiom-audits
# EVERY layer certificate. If a file is in this repo, this script checks it;
# if this script doesn't check it, it must not be in the repo.
#
# Phases:
#   0. resource + source-integrity guards
#   1. stub audit: no `by trivial` specs, no True-target theorems, and — the
#      anti-axiom-smuggling gate — ZERO `axiom` declarations under Proofs/
#      (external models in gen/ are the only sanctioned axiom site)
#   2. compile gen/ + Proofs/ in dependency order (explicit -o, capped cores,
#      per-file timeout). Any "declaration uses 'sorry'" warning is a FAILURE
#      (this catches sorry robustly — text greps can't, comments mention it).
#   3. axiom audit: #print axioms for every certificate in CERTS; each must
#      report exactly [propext, Classical.choice, Quot.sound]
# ─────────────────────────────────────────────────────────────────────────────
set -euo pipefail
source ~/aeneas-toolchain/env.sh
HERE="$(cd "$(dirname "$0")" && pwd)"
AENEAS_LEAN="$AENEAS_HOME/backends/lean"
TIMEOUT="${LEAN_TIMEOUT:-300}"
export LEAN_MEM_MB="${LEAN_MEM_MB:-8192}"  # 8192: ReduceSpec exceeds 6144 (coherence pass 2)
CORES="${LEAN_MAX_CORES:-0-3}"

# Layer manifests (extended as the pyramid grows; ORDER = import order).
GEN_MODULES=(
  CurveField/TypesExternal
  CurveField/Types
  CurveField/FunsExternal
  CurveField/Funs
)
PROOFS=(
  Basic
  Denote
  P25519
  ReduceSpec
  SubNegSpec
  ConstSpecs
  AddSpec
  MulSpec
  SquareSpec
  Square2Spec
  Field
  InvertSpec
  FieldMain
  FeQ
  EdCurve
  EdDenote
  EdDouble
  EdAddProjNiels
  EdAddAffNiels
  EdConvert
  EdMain
  DsmTableSpec
  DsmStepSpec
  DsmLoopSpec
  DsmNafLoadSpec
  DsmNafMath
  DsmNafLoopSpec
  DsmNafSpec
  DsmMulSpec
  ToBytesMath
  ToBytesSpec
  ScalarPackSpec
  CompressSpec
  SigApexSpec
  PointLiftSpec
  PointEqSpec
)
# Fully-qualified certificate names; each must be axiom-clean.
CERTS=(
  CurveFieldProofs.fieldImplementation
  CurveFieldProofs.edwardsImplementation
  CurveFieldProofs.naf_table_spec
  CurveFieldProofs.naf_select_spec
  CurveFieldProofs.proj_double_law
  CurveFieldProofs.compl_as_projective_law
  CurveFieldProofs.dsm_step_p_law
  CurveFieldProofs.dsm_step_b_law
  CurveFieldProofs.dsm_loop_spec
  CurveFieldProofs.naf_load_spec
  CurveFieldProofs.naf_exit
  CurveFieldProofs.naf_digit_loop_spec
  CurveFieldProofs.non_adjacent_form_spec
  CurveFieldProofs.run_basepoint
  CurveFieldProofs.vartime_double_base_mul_spec
  CurveFieldProofs.verify_loop_full
  CurveFieldProofs.to_bytes_spec
  CurveFieldProofs.ed_compress_spec
  ScalarProofs.from_bytes_mod_order_wide_spec
  CurveFieldProofs.vartime_dsm_basepoint_spec
  CurveFieldProofs.enc_point_inj
)
# Imports needed so every certificate in CERTS is in scope for the audit.
AUDIT_IMPORTS=(
  Proofs.FieldMain
  Proofs.EdMain
  Proofs.DsmTableSpec
  Proofs.DsmStepSpec
  Proofs.DsmLoopSpec
  Proofs.DsmNafSpec
  Proofs.DsmMulSpec
  Proofs.SigApexSpec
  Proofs.ToBytesSpec
  Proofs.CompressSpec
  Proofs.ScalarPackSpec
  Proofs.PointLiftSpec
  Proofs.PointEqSpec
)

# ── Phase 0: resource + integrity guards ────────────────────────────────────
free -m | awk '/Mem:/{if($7<2048){print "FATAL: <2GB RAM available — refusing to compile"; exit 1}}'
echo "=== Phase 0: source integrity ==="
for f in "$HERE"/gen/CurveField/*.lean "$HERE"/Proofs/*.lean; do
  [ -f "$f" ] || continue
  if ! grep -qE '^(/-|import |namespace |theorem |def |open |set_option |--)' "$f"; then
    echo "CORRUPTED: $f is not Lean source (olean clobber?). Restore: git checkout HEAD -- $f"
    exit 1
  fi
done
echo "  all sources valid"

# ── Phase 1: stub + axiom-smuggling audit ───────────────────────────────────
echo "=== Phase 1: stub audit ==="
if grep -rn 'by trivial' "$HERE"/Proofs/*Spec*.lean 2>/dev/null; then
  echo "STUB DETECTED: 'by trivial' in spec files"; exit 1; fi
if grep -rn ' : True :=' "$HERE"/Proofs/*.lean 2>/dev/null; then
  echo "STUB DETECTED: True-target theorem"; exit 1; fi
if grep -rnE '^(private |protected |noncomputable )*axiom ' "$HERE"/Proofs/*.lean 2>/dev/null; then
  echo "AXIOM SMUGGLING DETECTED: axiom declaration under Proofs/ — forbidden."
  echo "External models belong in gen/*/FunsExternal.lean and must stay outside"
  echo "every certificate's dependency cone (Phase 3 verifies that)."
  exit 1
fi
echo "  clean: no trivial stubs, no True targets, no axioms outside gen/"

# ── Phase 2: compile everything shipped ─────────────────────────────────────
echo "=== Phase 2: compile ==="
LOG=$(mktemp /tmp/check-compile-XXXX.log)
cd "$AENEAS_LEAN"
lake env bash -c "
  set -euo pipefail
  cd '$HERE/gen' && export LEAN_PATH=\"\$LEAN_PATH:\$PWD:$HERE\"
  compile() {
    echo \"  · \$1\"
    LEAN_TIMEOUT=$TIMEOUT LEAN_MAX_CORES=$CORES '$HERE/lean-guard' \"\${1}.lean\" 2>&1 | tee -a '$LOG' || { echo \"FAIL: \$1\"; exit 1; }
  }
  for m in ${GEN_MODULES[*]}; do compile \"\$m\"; done
  cd '$HERE'
  for m in ${PROOFS[*]}; do
    [ -f \"Proofs/\$m.lean\" ] || { echo \"MISSING: Proofs/\$m.lean listed in manifest\"; exit 1; }
    compile \"Proofs/\$m\"
  done
  # every shipped proof file must be in the manifest (no dead files)
  for f in Proofs/*.lean; do
    b=\$(basename \"\$f\" .lean)
    [ \"\$b\" = AxiomCheck ] && continue
    case \"\$b\" in Scalar*) continue;; esac  # scalar layer: checked by check-scalar.sh (coherence pass 2)
    case \" ${PROOFS[*]} \" in (*\" \$b \"*) ;; (*) echo \"DEAD FILE: \$f not in check manifest\"; exit 1;; esac
  done
"
if grep -q "uses 'sorry'" "$LOG"; then
  echo "STUB DETECTED: a compiled declaration uses 'sorry'"; exit 1; fi
rm -f "$LOG"

# ── Phase 3: axiom audit of every certificate ───────────────────────────────
echo "=== Phase 3: axiom audit ==="
EXPECTED="[propext, Classical.choice, Quot.sound]"
cd "$AENEAS_LEAN"
lake env bash -c "
  set -euo pipefail
  cd '$HERE/gen' && export LEAN_PATH=\"\$LEAN_PATH:\$PWD:$HERE\"
  cd '$HERE'
  AUD=\$(mktemp '$HERE/.audit-XXXX.lean')
  {
    for i in ${AUDIT_IMPORTS[*]}; do echo \"import \$i\"; done
    for c in ${CERTS[*]}; do echo \"#print axioms \$c\"; done
  } > \"\$AUD\"
  OUT=\$(LEAN_TIMEOUT=$TIMEOUT LEAN_MEM_MB=4096 '$HERE/lean-guard' \"\$AUD\" 2>&1)
  echo \"\$OUT\"
  rm -f \"\$AUD\"
  N_CLEAN=\$(echo \"\$OUT\" | grep -cF \"depends on axioms: $EXPECTED\" || true)
  if [ \"\$N_CLEAN\" -ne ${#CERTS[@]} ]; then
    echo \"AXIOM AUDIT FAILED: \$N_CLEAN/${#CERTS[@]} certificates clean\"
    exit 1
  fi
"
echo "=== Phase 3b: signature-apex audit (SHA-512 + wire-format boundary) ==="
# The verification-equation apex is grounded in the PROVEN curve model; its
# only axioms beyond the standard three are the deliberate, documented
# boundary: the SHA-512 hash oracle and the opaque wire-format types.
# NO curve axioms, NO scalar axioms, NO backend-dispatch axioms.
cd "$AENEAS_LEAN"
lake env bash -c "
  set -euo pipefail
  cd '$HERE/gen' && export LEAN_PATH=\"\$LEAN_PATH:\$PWD:$HERE\"
  cd '$HERE'
  ALLOWED='[propext, Classical.choice, Quot.sound, ed25519.Signature, ed_sigs.sha512_hash3, ed25519.Signature.r_bytes, ed25519.Signature.s_bytes]'
  AUD=\$(mktemp '$HERE/.apex-XXXX.lean')
  { echo 'import Proofs.SigApexSpec'; echo 'import Proofs.PointLiftSpec'; echo 'import Proofs.PointEqSpec'; echo '#print axioms CurveFieldProofs.verify_accepts_iff'; echo '#print axioms CurveFieldProofs.verify_accepts_iff_point'; echo '#print axioms CurveFieldProofs.verify_accepts_iff_point_eq'; } > \"\$AUD\"
  OUT=\$(LEAN_TIMEOUT=$TIMEOUT LEAN_MEM_MB=4096 '$HERE/lean-guard' \"\$AUD\" 2>&1)
  echo \"\$OUT\"
  rm -f \"\$AUD\"
  FLAT=\$(echo \"\$OUT\" | tr '\\n' ' ' | tr -s ' ')
  if echo \"\$FLAT\" | grep -qF \"'CurveFieldProofs.verify_accepts_iff' depends on axioms: \$ALLOWED\" \
     && echo \"\$FLAT\" | grep -qF \"'CurveFieldProofs.verify_accepts_iff_point' depends on axioms: \$ALLOWED\" \
     && echo \"\$FLAT\" | grep -qF \"'CurveFieldProofs.verify_accepts_iff_point_eq' depends on axioms: \$ALLOWED\"; then
    echo '  apex axiom cone = exactly the SHA-512 + wire-format boundary (no curve/scalar/backend axioms)'
  else
    echo 'APEX AUDIT FAILED: verify_accepts_iff cone is not the documented boundary'; exit 1
  fi
"

echo ""
echo "ALL PROOFS PASS. ALL CERTIFICATES AXIOM-CLEAN. NO DEAD FILES."
