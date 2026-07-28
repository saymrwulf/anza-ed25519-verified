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
#  2b. kernel-side axiom-declaration gate: read every compiled Proofs/*.olean
#      and reject ANY axiom declared there. Phase 1's grep reads source text
#      and is evadable four ways (see the phase header); this one asks the
#      kernel, derives its scope from the filesystem, and fails closed if the
#      set of compiled modules does not match the set of shipped sources.
#   3. axiom audit: #print axioms for every certificate in CERTS; each must
#      report exactly [propext, Classical.choice, Quot.sound]
#  3b. signature-apex audit: the four apex certificates against this fork's
#      documented SHA-512 + wire-format boundary, exactly.
#  3c. statement + specification binding: Proofs/Audit.lean emits a canonical
#      block of the policy constants, every certificate's fully-elaborated
#      statement, and the body of every specification constant reachable from
#      those statements. Its SHA-256 is pinned here and the block itself is
#      committed, so a mismatch is diffable. This is the phase that makes a
#      gutted statement, or a reference definition redefined to BE the
#      extracted code, fail — neither moves any axiom cone.
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
  DecompressSpec
  FromBytesSpec
  DecompressMain
  Audit          # LAST: imports the certificate corpus and runs the audit
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
  CurveFieldProofs.pow_p58_spec
  CurveFieldProofs.fe_ct_eq_spec
  CurveFieldProofs.sqrt_core
  CurveFieldProofs.sqrt_ratio_i_sq_spec
  CurveFieldProofs.from_bytes_spec
  CurveFieldProofs.decompress_of_canonical
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
  Proofs.DecompressSpec
  Proofs.FromBytesSpec
  Proofs.DecompressMain
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

# ── Phase 0b: pin the extracted model ───────────────────────────────────────
# WHY. The certificates are stated ABOUT the extracted model in gen/. Phase 3c
# binds their statements and the specification definitions those statements are
# stated against — but a statement mentions an extracted function BY NAME, so
# editing that function's BODY changes what the theorem is about while leaving
# every statement, every cone and the audit digest byte-identical.
#
# This is not hypothetical. On 2026-07-28 the risc0 and betrusted repositories
# were observed to produce byte-identical AUDIT-MANIFEST digests despite
# shipping demonstrably different extracted models (a different operation order
# in the point-doubling routine). The statements could not tell them apart.
# Only a byte pin can.
#
# Membership is derived from the filesystem, not from a list: every .lean under
# gen/ must appear in GEN-MODEL.sha256 and vice versa, so adding a model file
# fails closed rather than passing unnoticed.
echo "=== Phase 0b: extracted-model byte pin ==="
if [ ! -s "$HERE/GEN-MODEL.sha256" ]; then
  echo "FATAL: GEN-MODEL.sha256 is missing or empty — the extracted model is unpinned."
  exit 1
fi
GEN_OBSERVED=$(cd "$HERE/gen" && find . -name '*.lean' -type f | sed 's|^\./||' | sort)
GEN_PINNED=$(awk '{print $2}' "$HERE/GEN-MODEL.sha256" | sort)
if [ "$GEN_OBSERVED" != "$GEN_PINNED" ]; then
  echo "FATAL: the set of extracted-model files does not match GEN-MODEL.sha256."
  echo "  (< pinned, > present on disk)"
  diff <(echo "$GEN_PINNED") <(echo "$GEN_OBSERVED") | sed 's/^/    /'
  exit 1
fi
if ! ( cd "$HERE/gen" && sha256sum -c --quiet "$HERE/GEN-MODEL.sha256" ) ; then
  echo "FATAL: an extracted-model file does not match its pin. The proofs are"
  echo "about a model that is no longer the one that was reviewed."
  exit 1
fi
echo "  $(wc -l < "$HERE/GEN-MODEL.sha256") extracted-model files match their pins"
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

# ── Phase 2b: kernel-side axiom-declaration gate ────────────────────────────
# WHY THIS EXISTS. Phase 1's anti-smuggling check reads SOURCE TEXT, and a
# source-text grep is the wrong instrument. Measured on Lean v4.30.0-rc2
# (2026-07-28), each of the following compiles cleanly and slips past it:
#     ` axiom cheat : ...`        (one leading space — the pattern is anchored)
#     `@[simp] axiom cheat : ...` (line starts with the attribute)
#     `unsafe axiom cheat : ...`  (`unsafe` is not in the modifier alternation)
#     `axiom` <newline> `  cheat` (no space follows the keyword)
# Only the tab variant is blocked, and by Lean itself, not by us. Hardening the
# pattern would fix the exhibited syntax rather than the class; the class fix is
# to stop parsing text and ask the kernel, which is what this phase does.
# Ported from fips205-slhdsa-verified/verification/Proofs/Audit.lean.
#
# Phase 1's grep is kept as a fast, readable first line of defence. THIS is the
# gate that is load-bearing.
echo "=== Phase 2b: kernel-side axiom-declaration gate ==="
# dot-prefixed and inside $HERE: `lean` refuses a file outside the root
# directory, and a leading dot keeps it out of every *.lean glob.
# The gate reads the COMPILED ARTIFACTS directly (readModuleData) rather than
# importing the modules. Two reasons, both load-bearing:
#   · Proofs.Basic and Proofs.ConstSpecs deliberately reuse the name
#     `zero_spec` (they are never imported together), so a whole-corpus import
#     is impossible by construction — it fails with "environment already
#     contains". Reading oleans merges nothing, so collisions cannot arise.
#   · Membership is then SELF-DERIVING from the filesystem: every .olean under
#     Proofs/ is scanned, including Scalar* and AxiomCheck, which the CERTS
#     audit and the dead-file gate both skip. Nothing is on a hand-kept list.
# Cost is ~3 s for the whole corpus (no mathlib import), against ~53 s for a
# single module-importing invocation.
N_PROOF_SRC=$(ls -1 "$HERE"/Proofs/*.lean 2>/dev/null | wc -l)
GATE=$(mktemp "$HERE/.axgate-XXXX.lean")
{
  echo "import Lean"
  echo "open Lean"
  echo "def expectedModules : Nat := $N_PROOF_SRC"
  cat <<'LEANGATE'

run_cmd do
  let dir : System.FilePath := "Proofs"
  let mut errs : Array String := #[]
  let mut nMod := 0
  let mut nConst := 0
  for entry in (← dir.readDir) do
    if entry.path.extension == some "olean" then
      nMod := nMod + 1
      let (mod, _) ← readModuleData entry.path
      for ci in mod.constants do
        nConst := nConst + 1
        if ci matches .axiomInfo _ then
          errs := errs.push s!"  {entry.fileName}: {ci.name}"
  unless errs.isEmpty do
    throwError "AXIOM DECLARED under Proofs/ (kernel-side gate):\n{String.intercalate "\n" errs.toList}"
  -- FAIL CLOSED ON ABSENCE: an empty result and a clean result must not share
  -- a code path. A deleted .olean would make the scan above vacuous; an extra
  -- one is orphan litter with no shipped source.
  if nMod != expectedModules then
    throwError "COVERAGE MISMATCH under Proofs/: scanned {nMod} compiled modules, but the directory ships {expectedModules} sources. A missing .olean makes this gate vacuous; an extra .olean is an orphan with no source."
  logInfo s!"  kernel confirms: {nConst} declarations across {nMod} compiled Proofs modules, none is an axiom"
LEANGATE
} > "$GATE"
cd "$AENEAS_LEAN"
# The temp source AND its compiled artifact are removed on BOTH paths. Under
# `set -e` a bare `rm` after the call never runs when the gate goes red, which
# is exactly how this repo accumulated 101 orphan .olean files (fixed today).
GATE_RC=0
lake env bash -c "
  set -euo pipefail
  cd '$HERE/gen' && export LEAN_PATH=\"\$LEAN_PATH:\$PWD:$HERE\"
  cd '$HERE'
  LEAN_TIMEOUT=$TIMEOUT LEAN_MAX_CORES=$CORES '$HERE/lean-guard' '$GATE'
" || GATE_RC=$?
rm -f "$GATE" "${GATE%.lean}.olean"
if [ "$GATE_RC" -ne 0 ]; then
  echo "AXIOM SMUGGLING GATE FAILED (kernel-side) — see the error above."
  exit 1
fi

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
  rm -f \"\$AUD\" \"\${AUD%.lean}.olean\"
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
  { echo 'import Proofs.SigApexSpec'; echo 'import Proofs.PointLiftSpec'; echo 'import Proofs.PointEqSpec'; echo 'import Proofs.DecompressMain'; echo '#print axioms CurveFieldProofs.verify_accepts_iff'; echo '#print axioms CurveFieldProofs.verify_accepts_iff_point'; echo '#print axioms CurveFieldProofs.verify_accepts_iff_point_eq'; echo '#print axioms CurveFieldProofs.verify_accepts_iff_decompress'; } > \"\$AUD\"
  OUT=\$(LEAN_TIMEOUT=$TIMEOUT LEAN_MEM_MB=4096 '$HERE/lean-guard' \"\$AUD\" 2>&1)
  echo \"\$OUT\"
  rm -f \"\$AUD\" \"\${AUD%.lean}.olean\"
  FLAT=\$(echo \"\$OUT\" | tr '\\n' ' ' | tr -s ' ')
  if echo \"\$FLAT\" | grep -qF \"'CurveFieldProofs.verify_accepts_iff' depends on axioms: \$ALLOWED\" \
     && echo \"\$FLAT\" | grep -qF \"'CurveFieldProofs.verify_accepts_iff_point' depends on axioms: \$ALLOWED\" \
     && echo \"\$FLAT\" | grep -qF \"'CurveFieldProofs.verify_accepts_iff_point_eq' depends on axioms: \$ALLOWED\" \
     && echo \"\$FLAT\" | grep -qF \"'CurveFieldProofs.verify_accepts_iff_decompress' depends on axioms: \$ALLOWED\"; then
    echo '  apex + full-lift axiom cones = exactly the SHA-512 + wire-format boundary (no curve/scalar/backend axioms)'
  else
    echo 'APEX AUDIT FAILED: apex/full-lift cone is not the documented boundary'; exit 1
  fi
"


# ── Phase 3c: statement + specification binding ─────────────────────────────
# WHAT THE EARLIER PHASES DO NOT ESTABLISH. Phase 3 proves each certificate
# rests on exactly the declared axioms; 3b does the same for the apex tier.
# Neither says WHAT THE THEOREM SAYS. A certificate gutted to a tautology of
# the same cone passes both. So does one whose reference definition has been
# redefined to BE the extracted code, at which point the theorem reads
# `loop = loop` and every cone is byte-identical.
#
# Proofs/Audit.lean emits a canonical block holding the policy constants,
# every certificate's fully-elaborated statement, and the body of every
# specification constant transitively reachable from those statements. This
# phase binds the SHA-256 of that block, and the block's INPUT is committed
# too, so a mismatch can be DIFFED rather than merely reported.
#
# To rotate deliberately: run check.sh, take the printed OBSERVED digest, and
# update the constant below AND AUDIT-MANIFEST.txt in the same reviewable
# commit. That the rotation is visible in review is the whole point — an
# author who edits a statement and refreshes the digest in one commit is
# caught by reading the diff, not by this script.
EXPECTED_AUDIT_SHA256="12dc724bffd590e6f706573d97bf07425b8f268a1be2d72a3bbd9aef48f9c277"
echo "=== Phase 3c: statement + specification binding ==="
cd "$AENEAS_LEAN"
# The compiler's own exit code is the primary signal; the transcript is only
# corroboration. A timeout or a memory clamp exits non-zero WITHOUT printing
# "error:", so grepping the text alone would let it through.
AUD_RC=0
AUD_OUT=$(lake env bash -c "
  set -uo pipefail
  cd '$HERE/gen' && export LEAN_PATH=\"\$LEAN_PATH:\$PWD:$HERE\"
  cd '$HERE'
  LEAN_TIMEOUT=$TIMEOUT LEAN_MEM_MB=8192 '$HERE/lean-guard' Proofs/Audit.lean 2>&1
" ) || AUD_RC=$?
if [ "$AUD_RC" -ne 0 ]; then
  echo "AUDIT FAILED — Proofs/Audit.lean exited $AUD_RC:"
  tail -20 <<<"$AUD_OUT" | sed 's/^/    /'
  exit 1
fi
if grep -q 'error:' <<<"$AUD_OUT"; then
  echo "AUDIT FAILED — Proofs/Audit.lean did not elaborate cleanly:"
  grep 'error:' <<<"$AUD_OUT" | head -20 | sed 's/^/    /'
  exit 1
fi
BLOCK=$(awk '/AUDIT-MANIFEST-BEGIN/{f=1;next} /AUDIT-MANIFEST-END/{f=0} f' <<<"$AUD_OUT")
# FAIL CLOSED ON ABSENCE: no block and a matching block must not share a path.
if [ -z "$BLOCK" ]; then
  echo "AUDIT FAILED — no AUDIT-MANIFEST block was emitted (fail-closed)."; exit 1
fi
GOT_SHA=$(printf '%s\n' "$BLOCK" | sha256sum | cut -d' ' -f1)
if [ "$GOT_SHA" != "$EXPECTED_AUDIT_SHA256" ]; then
  printf '%s\n' "$BLOCK" > "$HERE/.audit-manifest.observed"
  echo "AUDIT FAILED — audit-manifest digest mismatch."
  echo "  expected: $EXPECTED_AUDIT_SHA256"
  echo "  observed: $GOT_SHA"
  echo "  A statement, a specification body, or a policy constant changed."
  echo "  First differences against the committed block:"
  diff -u "$HERE/AUDIT-MANIFEST.txt" "$HERE/.audit-manifest.observed" 2>/dev/null \
    | head -30 | sed 's/^/    /' || echo "    (AUDIT-MANIFEST.txt absent — cannot diff)"
  rm -f "$HERE/.audit-manifest.observed"
  exit 1
fi
# The digest's INPUT must be committed and current, or the diff above would
# compare against a stale reference and quietly mislead the next reader.
if ! printf '%s\n' "$BLOCK" | cmp -s - "$HERE/AUDIT-MANIFEST.txt"; then
  echo "AUDIT FAILED — the committed AUDIT-MANIFEST.txt does not match the emitted block."
  echo "  (the digest matched, so the committed copy is stale — refresh it)"; exit 1
fi
# CROSS-CHECK the certificate list against its OTHER two sources in this file:
# the CERTS array (Phase 3) and the apex names Phase 3b actually asks about.
# The apex names are read back out of this script rather than retyped, so a
# fourth copy cannot drift. Without this, a certificate could be dropped from
# the auditor's manifest and nothing would notice.
# Match only the QUOTED commands Phase 3b actually emits. An unquoted match
# also hits this file's own prose ("#print axioms for every certificate...")
# and silently contributes the word "for" as a certificate name.
# NOT "$0": this phase runs after `cd "$AENEAS_LEAN"`, and $0 is the relative
# path the caller used ("./check.sh"), which no longer resolves from there.
# $HERE was resolved absolutely at the top of the script.
APEX_FROM_3B=$(grep -oE "'#print axioms [A-Za-z0-9_.]+'" "$HERE/check.sh" | tr -d "'" | awk '{print $3}' | sort -u)
if [ -z "$APEX_FROM_3B" ]; then
  echo "AUDIT FAILED — could not recover the apex certificate names from Phase 3b."; exit 1
fi
# Every recovered name must be namespace-qualified; a bare word means the
# pattern drifted onto prose again rather than onto a command.
while read -r n; do
  case "$n" in *.*) ;; *) echo "AUDIT FAILED — recovered apex name '$n' is not qualified."; exit 1;; esac
done <<<"$APEX_FROM_3B"
AUD_CERTS=$(grep -o 'AUDITED-CERTIFICATES:.*' <<<"$AUD_OUT" | sed 's/AUDITED-CERTIFICATES: //' | tr ' ' '\n' | sort -u)
BASH_CERTS=$(printf '%s\n' "${CERTS[@]}" $APEX_FROM_3B | sort -u)
if [ "$AUD_CERTS" != "$BASH_CERTS" ]; then
  echo "AUDIT FAILED — the auditor's certificate list and this script's have drifted:"
  diff <(echo "$BASH_CERTS") <(echo "$AUD_CERTS") | sed 's/^/    /'
  exit 1
fi
grep -o 'statement audit PASSED:.*' <<<"$AUD_OUT" | sed 's/^/  /'
echo "  audit-manifest sha256 = $GOT_SHA (matches the committed block byte-for-byte)"

echo ""
echo "ALL PROOFS PASS. ALL CERTIFICATES AXIOM-CLEAN. NO DEAD FILES."
echo "STATEMENTS AND SPECIFICATIONS BOUND TO THE COMMITTED AUDIT MANIFEST."
