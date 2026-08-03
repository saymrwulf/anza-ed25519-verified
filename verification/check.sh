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

# ── Mode selection ──────────────────────────────────────────────────────────
# --audit-only runs every gate EXCEPT the compile, against the .olean files a
# previous full run left behind. It exists because gate work dominates this
# estate's wall-clock: on 2026-07-29, 3.9 hours of a session went to Lean
# re-elaborating proofs nobody had edited, while the audit phases themselves
# take about fifteen seconds.
#
# IT MUST BE IMPOSSIBLE TO MISUSE, so:
#   · it refuses to run unless a previous FULL run recorded a basis of source
#     hashes AND every source still matches it byte-for-byte. Not mtimes —
#     `touch` defeats those, and a stale-artifact check that fails open is
#     worse than no shortcut at all, because a green button would then
#     describe a corpus that is no longer on disk;
#   · the basis file is build state, never committed, so a fresh clone cannot
#     inherit permission to skip compiling;
#   · the final banner DIFFERS, and says in words that the run is not evidence.
#     A transcript must never be mistakable for a full one.
AUDIT_ONLY=0
for arg in "$@"; do
  case "$arg" in
    --audit-only) AUDIT_ONLY=1 ;;
    --help|-h) echo "usage: check.sh [--audit-only]"; exit 0 ;;
    *) echo "unknown argument: $arg (see --help)"; exit 1 ;;
  esac
done
BASIS="$HERE/.audit-basis"          # gitignored build state, written by full runs

# Every .lean this repository ships, with its hash: the exact set whose
# recompilation --audit-only proposes to skip.
source_basis() {
  { find "$HERE/Proofs" -name '*.lean' -type f -printf '%P\n' | sed 's|^|Proofs/|'
    find "$HERE/gen" -name '*.lean' -type f -printf '%P\n' | sed 's|^|gen/|'; } \
  | LC_ALL=C sort | while read -r f; do printf '%s  %s\n' "$(sha256sum "$HERE/$f" | cut -d' ' -f1)" "$f"; done
}

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
  Audit          # imports the certificate corpus and runs the audit
  InventoryCore  # inventory machinery (imports only Lean)
  Inventory      # inventory driver: main chain
  InventoryBasic # inventory driver: Proofs.Basic (kept separate: name collision)
)
# Modules this button must COMPILE but does not OWN.
#
# The signature apex rests on scalar arithmetic: PointLiftSpec needs
# ScalarPackSpec which needs ScalarFromBytesSpec, and SigApexSpec needs
# ScalarDenote. Twelve of the scalar layer's thirteen modules are
# transitive prerequisites of this manifest.
#
# Until Phase 0a began purging, this button appeared to work without them:
# it silently consumed .olean files that a previous check-scalar.sh run had
# left lying about. The verdict depended on untracked build state produced
# by a DIFFERENT script — precisely the condition build hygiene exists to
# expose, and it stayed invisible for as long as nothing ever cleaned up.
#
# OWNERSHIP IS UNCHANGED: check-scalar.sh audits these — their cones, their
# declaration inventory, their axiom gate. This button only builds them so
# that running it alone is self-contained. Phase 1b asserts that every name
# here belongs to the OTHER manifest, so this list can never quietly become
# a second claim of ownership.
PREREQ=(
  ScalarDenote
  ScalarLoop
  ScalarSubSpec
  ScalarAddSpec
  ScalarMulSpec
  ScalarMontSpec
  ScalarReduceSpec
  ScalarFullMulSpec
  ScalarWideSpec
  ScalarBytesSpec
  ScalarUnpackSpec
  ScalarFromBytesSpec
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

# ── Phase 0a: build hygiene ─────────────────────────────────────────────────
# The verdict must depend on COMMITTED BYTES, never on build state left behind
# by an earlier run. An orphan .olean with no source still satisfies an import,
# and .olean is gitignored, so `git status` shows a clean tree while the
# compiler happily reads a module nobody can review.
#
# NOT RUN UNDER --audit-only, for the obvious reason: that mode exists to audit
# the artifacts a previous full run produced, and purging them would make the
# two features destroy each other. That is also why an audit-only transcript is
# not evidence — it has not had this hygiene applied.
if [ "$AUDIT_ONLY" = 0 ]; then
  echo "=== Phase 0a: build hygiene ==="
  find "$HERE" -name '*.olean' -delete 2>/dev/null || true
  echo "  purged every .olean under verification/ — this run compiles from source"
else
  echo "=== Phase 0a: SKIPPED (--audit-only keeps the artifacts it audits) ==="
fi

# Stray Lean files at the verification/ root join the build through LEAN_PATH,
# which contains $PWD. gen/ and Proofs/ are the only sanctioned locations.
STRAY=$(find "$HERE" -maxdepth 1 \( -name '*.lean' -o -name '*.olean' \) -printf '%f\n' 2>/dev/null || true)
if [ -n "$STRAY" ]; then
  echo "$STRAY" | sed 's/^/  STRAY Lean file outside gen\/ and Proofs\/: /'
  echo "These join the build via LEAN_PATH and are audited by nothing."
  exit 1
fi

# gen/ as a SET, not as a list of names: every .lean under gen/ must be either
# a compiled model module or an Aeneas *_Template.lean. The templates are KEPT
# here, unlike the companion SLH-DSA repo which deletes them: extract.sh directs
# the operator to diff the hand-written external models against them, so they
# are the reference for that comparison and deleting them would destroy it.
GENFAIL=0
while read -r f; do
  [ -z "$f" ] && continue
  case "$f" in *_Template.lean) continue;; esac
  b="${f%.lean}"
  case " ${GEN_MODULES[*]} " in (*" $b "*) ;; (*) echo "  DEAD MODEL FILE: gen/$f is in no manifest"; GENFAIL=1;; esac
done < <(cd "$HERE/gen" && find . -name '*.lean' -printf '%P\n' | sort)
for m in "${GEN_MODULES[@]}"; do
  [ -f "$HERE/gen/$m.lean" ] || { echo "  MISSING MODEL FILE: gen/$m.lean is in the manifest but absent"; GENFAIL=1; }
done
[ "$GENFAIL" = 0 ] || { echo "MODEL-SET CHECK FAILED"; exit 1; }
echo "  gen/ is exactly the manifest plus its pinned templates"
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
# ── Phase 0c: harness integrity ─────────────────────────────────────────────
# WHY. Every gate in this script is executed by a script that, until now,
# nothing pinned. Round-5 review of the companion SLH-DSA repository stubbed
# the compiler wrapper alone and the button printed ALL GREEN in 3.6 seconds
# over deliberately destroyed proofs; flipping two guards in the audit driver
# disabled every check with the digest byte-identical. Depth of checking is
# worth nothing if the thing doing the checking is unbound.
#
# WHICH files must be pinned is POLICY, and policy lives here — in the root of
# trust — never inside the map being consulted. If the required set were read
# from HARNESS.sha256, deleting an entry would silently un-pin the file rather
# than failing the build.
#
# The set is SELF-DERIVING from the executable bit: anything this script can
# shell out to must be pinned, so a NEW script fails closed until someone pins
# it deliberately. Non-executable files that are nonetheless load-bearing —
# the audit driver, the committed manifests, the policy tables — cannot be
# discovered that way and are listed explicitly.
HARNESS_EXTRA=(
  AUDIT-MANIFEST.txt        # the statement block Phase 3c's digest is taken over
  GEN-MODEL.sha256          # the extracted-model pins Phase 0b enforces
  MODEL-CORRESPONDENCE.txt  # the extraction boundary Phase 0d recomputes
  inventory-allowlist.txt   # the audit surface Phase 2c diffs against
  inventory-allowlist-scalar.txt # the scalar layer's audit surface (second button)
  Proofs/Audit.lean         # the audit driver: it computes the digest it is judged by
  driver-allowlist.txt      # the INSTRUMENTS' own declaration surface, with cones.
                            # Not executable, so it would otherwise sit outside the
                            # harness set — and an allowlist an attacker may rewrite
                            # pins nothing.
  Proofs/ScalarAudit.lean   # the scalar audit driver, likewise
  SCALAR-AUDIT-MANIFEST.txt # the block the scalar digest is taken over, committed
                            # so a mismatch can be DIFFED and not merely reported
  Proofs/InventoryCore.lean # inventory machinery
  Proofs/InventoryScalar.lean # inventory driver: the scalar layer
  Proofs/Inventory.lean     # inventory driver: main chain
  Proofs/InventoryBasic.lean # inventory driver: Proofs.Basic
)
echo "=== Phase 0c: harness integrity ==="
if [ ! -s "$HERE/HARNESS.sha256" ]; then
  echo "FATAL: HARNESS.sha256 is missing or empty — the harness is unpinned."
  exit 1
fi
# NOTE ON check.sh ITSELF: it is pinned like everything else. That catches
# drift and accident. It does NOT stop an author who edits this script and
# refreshes its pin in the same commit — nothing executed by the harness can.
# The defence there is that both changes appear in the diff at the pinned
# commit, which is why TRUSTED-BASE.md says the consumer's check is review.
HARNESS_REQUIRED=$( { find "$HERE" -type f -executable -not -path '*/.git/*' -printf '%P\n'
                      printf '%s\n' "${HARNESS_EXTRA[@]}"; } | sort -u )
HARNESS_PINNED=$(awk '{print $2}' "$HERE/HARNESS.sha256" | sort -u)
if [ "$HARNESS_REQUIRED" != "$HARNESS_PINNED" ]; then
  echo "FATAL: the set of harness files does not match HARNESS.sha256."
  echo "  (< pinned, > present and requiring a pin)"
  diff <(echo "$HARNESS_PINNED") <(echo "$HARNESS_REQUIRED") | sed 's/^/    /'
  exit 1
fi
if ! ( cd "$HERE" && sha256sum -c --quiet HARNESS.sha256 ) ; then
  echo "FATAL: a harness file does not match its pin. The button you are"
  echo "running is not the button that was reviewed."
  exit 1
fi
echo "  $(wc -l < "$HERE/HARNESS.sha256") harness files match their pins"
# ── Phase 0d: template/model correspondence ─────────────────────────────────
# WHAT AENEAS'S TEMPLATE IS. When Aeneas extracts the Rust it also emits, for
# each crate, a *_Template.lean naming everything the extracted code needs from
# OUTSIDE itself. That template is the extraction's own statement of its
# boundary. The hand-written *External.lean beside it is our answer to that
# statement, and `extract.sh` has always said, in prose, "after regenerating,
# diff the template against the hand-written file". Prose is not a gate.
#
# WHAT THIS ADDS, given that three other things already stand here. Phase 0b
# byte-pins both files, so neither can drift from its pin unnoticed. The
# generated Funs.lean imports the model and CALLS these externals, so the Lean
# compiler already enforces their types wherever the extracted code uses them.
# The per-certificate exact cones catch any external that becomes — or stops
# being — an assumption anything depends on. What none of those three sees is
# the CLASSIFICATION: for each name the extraction asks for, whether this
# repository answers with an assumption or with a proof.
#
# That distinction is the tier-A/B claim, and it was prose until 2026-07-31.
# The docs say the curve calls (compress, as_bytes,
# vartime_double_scalar_mul_basepoint, from_bytes_mod_order{,_wide}) and the
# three curve TYPES resolve to the PROVEN model's own definitions rather than
# to axioms — because gen/CurveField/Funs.lean opens `namespace
# curve25519_dalek`, so the names Aeneas asks for are the names it defines.
# Nothing checked it. A regeneration that renamed one of those, or a model that
# quietly answered one with an axiom instead, would have left the documents
# claiming a proof where the repository now had an assumption.
#
# model-correspondence.py recomputes the classification from the files —
# namespace-aware, so a definition inside `namespace curve25519_dalek` counts
# under its full name — and the result must equal the committed table exactly.
# UNRESOLVED is a hard failure in the tool itself: the extraction asking for
# something this repository does not provide at all.
echo "=== Phase 0d: template/model correspondence ==="
CORR_FILE="$HERE/MODEL-CORRESPONDENCE.txt"
if [ ! -s "$CORR_FILE" ]; then
  echo "FATAL: MODEL-CORRESPONDENCE.txt is missing or empty — the extraction boundary is unpinned."
  exit 1
fi
CORR_OBSERVED=$(cd "$HERE" && python3 model-correspondence.py .) || {
  echo "$CORR_OBSERVED" | grep UNRESOLVED | sed 's/^/  /'
  echo "MODEL CORRESPONDENCE FAILED: the extraction declares an external that neither"
  echo "the hand-written model nor the proven corpus provides."
  exit 1
}
if ! diff -u "$CORR_FILE" <(printf '%s\n' "$CORR_OBSERVED") > /tmp/corr-diff.$$ 2>&1; then
  echo "  MODEL CORRESPONDENCE DRIFT (< committed, > observed):"
  sed -n '4,24p' /tmp/corr-diff.$$ | sed 's/^/    /'
  rm -f /tmp/corr-diff.$$
  echo "MODEL CORRESPONDENCE FAILED: an external changed how it is answered."
  exit 1
fi
rm -f /tmp/corr-diff.$$
echo "  $(grep -c '|MODEL$' "$CORR_FILE") externals answered by the hand-written model (assumptions)"
echo "  $(grep -c '|PROVEN$' "$CORR_FILE") answered by PROVEN definitions in the extracted corpus"
echo "  $(grep -c '|EXTRA$' "$CORR_FILE") model declarations beyond what the extraction asks for"
echo ""

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

# ── Phase 1b: the two-button seam ───────────────────────────────────────────
# WHY. This repository is checked by TWO buttons: this script covers the field,
# curve and signature layers, and check-scalar.sh covers the scalar layer.
# Until 2026-07-30 neither asserted anything about the other's scope, and this
# script's dead-file gate simply SKIPPED anything named Scalar*. A new
# Proofs/ScalarX.lean was therefore gated by nothing at all: absent from this
# manifest by exemption, absent from the other by omission, compiled by
# neither, inventoried by neither.
#
# The fix is mutual: each button reads the OTHER's manifest and asserts that
# every shipped proof source belongs to exactly one of them. Both directions,
# so a file can neither fall between the two nor be claimed by both.
echo "=== Phase 1b: two-button seam ==="
SEAMFAIL=0
SCALAR_SH="$HERE/check-scalar.sh"
if [ ! -f "$SCALAR_SH" ]; then
  echo "  FATAL: check-scalar.sh is absent — half the corpus would go unchecked."
  exit 1
fi
SCALAR_MANIFEST=$(grep -m1 '^PROOFS=(' "$SCALAR_SH" | sed 's/^PROOFS=(//; s/).*$//' | tr ' ' '\n' | sed '/^$/d' | sort -u)
if [ -z "$SCALAR_MANIFEST" ]; then
  echo "  FATAL: could not read check-scalar.sh's manifest; refusing to guess its scope."
  exit 1
fi
MAIN_MANIFEST=$(printf '%s\n' "${PROOFS[@]}" | sort -u)
# 1. Every shipped proof source belongs to exactly one manifest.
for f in "$HERE"/Proofs/*.lean; do
  b=$(basename "$f" .lean)
  case "$b" in AxiomCheck|Inventory|InventoryBasic|InventoryCore|InventoryScalar) continue;; esac
  inm=0; ins=0
  grep -qx "$b" <<<"$MAIN_MANIFEST"   && inm=1
  grep -qx "$b" <<<"$SCALAR_MANIFEST" && ins=1
  if [ $((inm + ins)) -eq 0 ]; then
    echo "  ORPHAN: Proofs/$b.lean is in NEITHER manifest — compiled and audited by no button"; SEAMFAIL=1
  elif [ $((inm + ins)) -eq 2 ]; then
    echo "  DOUBLE-CLAIMED: Proofs/$b.lean is in BOTH manifests — the buttons disagree about scope"; SEAMFAIL=1
  fi
done
# 2. Neither manifest may name a file that does not exist.
while read -r m; do
  [ -z "$m" ] && continue
  [ -f "$HERE/Proofs/$m.lean" ] || { echo "  PHANTOM: check-scalar.sh lists $m, which does not exist"; SEAMFAIL=1; }
done <<<"$SCALAR_MANIFEST"
# PREREQ is a borrowing, not a claim: every name in it must belong to the
# OTHER manifest. Without this the list could silently grow into a second
# ownership claim over modules this button never audits.
for m in "${PREREQ[@]}"; do
  grep -qx "$m" <<<"$SCALAR_MANIFEST" || { echo "  PREREQ NOT OWNED BY THE SCALAR BUTTON: $m"; SEAMFAIL=1; }
  grep -qx "$m" <<<"$MAIN_MANIFEST"   && { echo "  PREREQ ALSO CLAIMED HERE: $m"; SEAMFAIL=1; }
done
[ "$SEAMFAIL" = 0 ] && echo "  ${#PREREQ[@]} prerequisites borrowed from check-scalar.sh, which audits them"
[ "$SEAMFAIL" = 0 ] && echo "  every proof source belongs to exactly one button ($(grep -c . <<<"$MAIN_MANIFEST") here, $(grep -c . <<<"$SCALAR_MANIFEST") scalar)"
[ "$SEAMFAIL" = 0 ] || { echo "SEAM CHECK FAILED"; exit 1; }
# ── Phase 2: compile everything shipped ─────────────────────────────────────
if [ "$AUDIT_ONLY" = 1 ]; then
  echo "=== Phase 2: SKIPPED (--audit-only) ==="
  if [ ! -s "$BASIS" ]; then
    echo "REFUSING: no basis from a previous full run ($BASIS absent)."
    echo "  --audit-only may only follow a full green run in this working tree."
    echo "  Run ./check.sh with no arguments first."
    exit 1
  fi
  if ! diff -q <(source_basis) "$BASIS" >/dev/null 2>&1; then
    echo "REFUSING: the sources no longer match the basis of the last full run."
    echo "  The .olean files on disk describe a corpus that has changed, so every"
    echo "  audit below would be judging artifacts that no source produces."
    echo "  Differences (< basis, > now):"
    diff <(source_basis) "$BASIS" | head -20 | sed 's/^/    /'
    echo "  Run ./check.sh with no arguments."
    exit 1
  fi
  # Fail closed on absence too: a source with no artifact cannot be audited.
  MISSING=0
  for m in "${PROOFS[@]}"; do
    [ -f "$HERE/Proofs/$m.olean" ] || { echo "  MISSING ARTIFACT: Proofs/$m.olean"; MISSING=1; }
  done
  for m in "${GEN_MODULES[@]}"; do
    [ -f "$HERE/gen/$m.olean" ] || { echo "  MISSING ARTIFACT: gen/$m.olean"; MISSING=1; }
  done
  [ "$MISSING" = 0 ] || { echo "REFUSING: run ./check.sh with no arguments."; exit 1; }
  echo "  sources byte-identical to the last full run's basis; $(grep -c . "$BASIS") files"
else
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
  # Prerequisites first: owned and audited by check-scalar.sh, built here so
  # this run does not depend on artifacts another script may have left behind.
  for m in ${PREREQ[*]}; do
    [ -f \"Proofs/\$m.lean\" ] || { echo \"MISSING PREREQ: Proofs/\$m.lean\"; exit 1; }
    compile \"Proofs/\$m\"
  done
  for m in ${PROOFS[*]}; do
    [ -f \"Proofs/\$m.lean\" ] || { echo \"MISSING: Proofs/\$m.lean listed in manifest\"; exit 1; }
    compile \"Proofs/\$m\"
  done
  # every shipped proof file must be in the manifest (no dead files)
  for f in Proofs/*.lean; do
    b=\$(basename \"\$f\" .lean)
    [ \"\$b\" = AxiomCheck ] && continue
    # InventoryScalar belongs to the other button; the rest are in PROOFS above.
    case \"\$b\" in InventoryScalar) continue;; esac
    case \"\$b\" in Scalar*) continue;; esac  # scalar layer: checked by check-scalar.sh (coherence pass 2)
    case \" ${PROOFS[*]} \" in (*\" \$b \"*) ;; (*) echo \"DEAD FILE: \$f not in check manifest\"; exit 1;; esac
  done
"
if grep -q "uses 'sorry'" "$LOG"; then
  echo "STUB DETECTED: a compiled declaration uses 'sorry'"; exit 1; fi
rm -f "$LOG"
fi

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
# MEMBERSHIP, not a glob. Phase 0a purges every .olean and this button
# rebuilds only its own manifest; the scalar layer's artifacts belong to the
# other button. Counting Proofs/*.lean here would demand artifacts this run
# never makes — the spelling-versus-ownership error ScalarPackSpec exposed.
PROOF_OLEANS=$(printf '"%s.olean", ' "${PROOFS[@]}" | sed 's/, $//')
GATE=$(mktemp "$HERE/.axgate-XXXX.lean")
{
  echo "import Lean"
  echo "open Lean"
  echo "def expected : List String := [$PROOF_OLEANS]"
  cat <<'LEANGATE'

run_cmd do
  let dir : System.FilePath := "Proofs"
  let mut errs : Array String := #[]
  let mut nMod := 0
  let mut nConst := 0
  let mut seen : Std.HashSet Name := {}
  for name in expected do
    let p := dir / name
    -- FAIL CLOSED ON ABSENCE: a manifest module whose artifact is missing makes
    -- this gate vacuous for that module. It must be an error, never a skip.
    unless (← p.pathExists) do
      throwError "COVERAGE: {name} is in the compile manifest but its artifact is absent"
    nMod := nMod + 1
    let (mod, _) ← readModuleData p
    for ci in mod.constants do
      nConst := nConst + 1
      seen := seen.insert ci.name
      if ci matches .axiomInfo _ then
        errs := errs.push s!"  {name}: {ci.name}"
  unless errs.isEmpty do
    throwError "AXIOM DECLARED under Proofs/ (kernel-side gate):\n{String.intercalate "\n" errs.toList}"
  -- FAIL CLOSED ON ABSENCE: an empty result and a clean result must not share
  -- a code path. A deleted .olean would make the scan above vacuous; an extra
  -- one is orphan litter with no shipped source.
  logInfo s!"  kernel confirms: {nConst} declarations across {nMod} compiled modules (this button's manifest, by membership), none is an axiom"
  for n in seen do IO.println s!"KERNEL-NAME|{n}"
LEANGATE
} > "$GATE"
cd "$AENEAS_LEAN"
# The temp source AND its compiled artifact are removed on BOTH paths. Under
# `set -e` a bare `rm` after the call never runs when the gate goes red, which
# is exactly how this repo accumulated 101 orphan .olean files (fixed today).
GATE_RC=0
KERNLOG=$(mktemp /tmp/check-kernel-XXXX.log)
lake env bash -c "
  set -euo pipefail
  cd '$HERE/gen' && export LEAN_PATH=\"\$LEAN_PATH:\$PWD:$HERE\"
  cd '$HERE'
  LEAN_TIMEOUT=$TIMEOUT LEAN_MAX_CORES=$CORES '$HERE/lean-guard' '$GATE'
" 2>&1 | tee "$KERNLOG" || GATE_RC=${PIPESTATUS[0]}
rm -f "$GATE" "${GATE%.lean}.olean"
if [ "$GATE_RC" -ne 0 ]; then
  echo "AXIOM SMUGGLING GATE FAILED (kernel-side) — see the error above."
  exit 1
fi

# ── Phase 2c: environment-derived declaration inventory ─────────────────────
# WHAT THIS ADDS over Phase 2b. Phase 2b asks the kernel whether any AXIOM is
# declared under Proofs/. It says nothing about the ~3000 other declarations:
# a `def` or `theorem` whose cone quietly acquired an oracle, a declaration
# renamed, added or removed, or a compiler-generated auxiliary that changed
# shape, all pass 2b unremarked.
#
# This phase pins the whole surface. Every constant originating in an audited
# module contributes NAME, MODULE, KIND and full AXIOM CONE, and the observed
# set must equal inventory-allowlist.txt EXACTLY, both directions:
# UNCLASSIFIED (in the environment, not allowlisted) and STALE (allowlisted,
# not in the environment) are both build failures.
#
# PORTED from ltl-accumulator-verified, where a nine-attack self-test proved a
# source-regex enumerator evadable by attributed, private, indented and
# `instance` declarations and by a nested-namespace basename collision.
#
# TWO DRIVERS, because this corpus cannot be imported as one environment:
# Proofs.Basic and Proofs.ConstSpecs both declare CurveFieldProofs.zero_spec.
# The records carry their originating module precisely so those two remain
# distinct entries — keyed on name alone they were byte-identical, and the
# merged allowlist covered 3022 declarations with 3021 entries.
echo "=== Phase 2c: environment-derived declaration inventory ==="
INVFAIL=0
INVLOG=$(mktemp /tmp/check-inv-XXXX.log)
cd "$AENEAS_LEAN"
# The DRIVERS are discovered, not listed: whether this corpus needs one or two
# is a per-repo fact (dalek and anza cannot import Proofs.Basic together with
# Proofs.ConstSpecs; risc0 and betrusted have no Proofs.Basic at all). A
# hardcoded pair would silently look for a file that does not exist here.
DRIVERS=$(ls "$HERE"/Proofs/Inventory*.lean 2>/dev/null | xargs -r -n1 basename \
          | sed 's/\.lean$//' | grep -vE '^(InventoryCore|InventoryScalar)$' | sort)
# InventoryScalar belongs to check-scalar.sh, which compiles the modules it
# covers. Globbing Inventory*.lean swept it in here, after which this phase
# correctly complained that its own manifest lacks the scalar modules.
if [ -z "$DRIVERS" ]; then
  echo "  NO INVENTORY DRIVER FOUND — the audit surface would go unchecked."; exit 1
fi
N_DRIVERS=$(printf '%s\n' "$DRIVERS" | grep -c .)
for drv in $DRIVERS; do
  lake env bash -c "
    set -uo pipefail
    cd '$HERE/gen' && export LEAN_PATH=\"\$LEAN_PATH:\$PWD:$HERE\"
    cd '$HERE'
    LEAN_TIMEOUT=$TIMEOUT LEAN_MEM_MB=8192 '$HERE/lean-guard' Proofs/$drv.lean
  " >> "$INVLOG" 2>&1 || { cat "$INVLOG"; echo "INVENTORY COMPILE FAILED ($drv)"; rm -f "$INVLOG"; exit 1; }
done
# Reconcile the two trailers into one. Summing them and comparing against the
# lines actually collected preserves the integrity property in the presence of
# the split: truncation in EITHER driver shows up as a mismatch.
N_TRAILERS=$(grep -c '^INV-COUNT|' "$INVLOG")
if [ "$N_TRAILERS" -ne "$N_DRIVERS" ]; then
  echo "  INVENTORY INCOMPLETE: expected a count trailer from each of the $N_DRIVERS driver(s), saw $N_TRAILERS"
  INVFAIL=1
fi
SUM=$(grep '^INV-COUNT|' "$INVLOG" | cut -d'|' -f2 | paste -sd+ - | bc)
OBS=$(mktemp /tmp/check-inv-obs-XXXX.log)
grep '^INV|' "$INVLOG" > "$OBS"
echo "INV-COUNT|${SUM:-0}" >> "$OBS"
"$HERE/inventory_gate.sh" "$OBS" "$HERE/inventory-allowlist.txt" || INVFAIL=1

# The drivers' corpus lists must together BE the compile manifest, minus the
# audit infrastructure and the scalar layer. Checked in both directions so a
# module cannot fall between the two drivers, and NO SILENT TRUNCATION: what
# this phase does not cover is named on stdout every run.
COVERED=$(for d in $DRIVERS; do grep -ohE '`Proofs\.[A-Za-z0-9]+' "$HERE/Proofs/$d.lean"; done \
          | sed 's/`Proofs\.//' | sort -u)
for m in "${PROOFS[@]}"; do
  case "$m" in Audit|Inventory|InventoryBasic|InventoryCore) continue;; esac
  grep -qx "$m" <<<"$COVERED" || { echo "  UNINVENTORIED: $m is compiled by this script but no driver covers it"; INVFAIL=1; }
done
while read -r m; do
  [ -z "$m" ] && continue
  case " ${PROOFS[*]} " in (*" $m "*) ;; (*) echo "  PHANTOM: driver claims $m, which this script does not compile"; INVFAIL=1;; esac
done <<<"$COVERED"
for f in "$HERE"/Proofs/*.lean; do
  b=$(basename "$f" .lean)
  case "$b" in Audit|Inventory|InventoryBasic|InventoryCore|InventoryScalar) continue;; esac
  grep -qx "$b" <<<"$COVERED" || echo "  NOT INVENTORIED HERE (separate button): Proofs/$b.lean"
done
[ "$INVFAIL" = 0 ] || { echo "INVENTORY COVERAGE FAILED"; exit 1; }

# ── Phase 2c-accounting: every kernel constant is accounted for ─────────────
# SEPARATED FROM PHASE 2c DELIBERATELY, and the reason is a self-test that
# could not pass (round-7 finding F5). This block reads $KERNLOG, created one
# phase earlier in Phase 2b. selftest-shapes.sh lifts "Phase 2c" by text marker
# and runs it standalone; once this block lived inside that range, the lifted
# driver died on its first `$KERNLOG` expansion under `set -u`. The test failed
# loudly in all four forks from the moment the block was added — so the shapes
# property went unverified, though it never produced a false green.
#
# Truncating the lift is NOT the fix: Phase 2c's own verdict
# (`INVENTORY COVERAGE FAILED`) sits after this block, so a shorter range drops
# the phase's ability to fail at all. Instead the block gets its own marker and
# its own verdict, which makes Phase 2c liftable BY CONSTRUCTION rather than by
# the self-test knowing where to stop.
# ── THE ACCOUNTING IDENTITY ───────────────────────────────────────────────
# Every declaration the kernel saw must be accounted for by exactly one walk:
# the corpus inventory, or the instruments' own surface. Until 2026-07-31 the
# two numbers were never compared — the kernel reported 3058 across this
# button's manifest, the inventory accounted for 3022, and the 36-declaration
# difference was the audit drivers' own machinery, covered by no allowlist row
# and by no other check. It was not a soundness hole (the drivers ARE in the
# manifest, so Phase 2b's kernel gate rejects an axiom in one whatever its
# indentation) but it was an unexamined remainder, and an unexamined remainder
# is where the next defect hides.
#
# Stating it as an IDENTITY rather than as two separate counts is what makes it
# fail closed: a declaration that slipped out of both walks leaves the sum
# short, and one counted twice leaves it long.
#
# COUNT DISTINCT CONSTANTS, NOT PHYSICAL DECLARATIONS. The two sides of this
# identity were, at first, counting different things, and the gap was papered
# over with a `+ N_DRIVERS` term justified as a "self-observation blind spot".
# That explanation was WRONG. It fitted dalek and anza (2 drivers, residual 2)
# and broke on risc0 and betrusted (1 driver, residual 2) — the residual is 2
# everywhere and has nothing to do with drivers.
#
# The measured cause: Lean materialises equation lemmas LAZILY, when something
# forces an unfold, and each module that forces one gets its own copy in its
# object file. On every fork, `CurveFieldProofs.denote.eq_1` sits in both
# `SubNegSpec.olean` and `ConstSpecs.olean`, and `CurveFieldProofs.limbsVal.eq_1`
# in both `ReduceSpec.olean` and `ConstSpecs.olean`. The kernel gate reads each
# object file separately and counts both copies; the environment holds one
# constant per name and the inventory sees it once. Hence exactly 2.
#
# So the gate now reports DISTINCT names and the fudge term is gone. This still
# fails closed: a declaration missing from both walks leaves the sum short, and
# one counted twice leaves it long. A future mismatch must be explained — as
# this one finally was — never absorbed into a constant.
# PIN THE INSTRUMENTS' OWN SURFACE, in both directions, with the SAME gate the
# corpus uses (round-8 review, Claude, register keys `drv-surface-no-cones`,
# `accounting-certifies-enumeration`, and it retires `drv-naming-heuristic` as
# load-bearing).
#
# The accounting identity below proves every kernel constant is ENUMERATED by
# one of the two walks. The reviewer demonstrated that enumeration is not
# audit: their planted claim WAS enumerated, carried a real axiom cone, and
# nothing examined it — DRV rows had no cone and no allowlist covered them.
# They now carry the cone, and this gate pins them exactly as the corpus is, so
# a claim smuggled into an instrument is a NEW ROW and a new row fails closed
# whatever it is called.
"$HERE/inventory_gate.sh" "$INVLOG" "$HERE/driver-allowlist.txt" DRV || ACCTFAIL=1
N_DRV=$(grep -c '^DRV|' "$INVLOG" || true)
DRV_TRAILERS=$(grep -c '^DRV-COUNT|' "$INVLOG" || true)
DRV_SUM=$(grep '^DRV-COUNT|' "$INVLOG" | cut -d'|' -f2 | paste -sd+ - | bc)
KERN_NAMES=$(mktemp /tmp/check-kernnames-XXXX.txt)
ACCT_NAMES=$(mktemp /tmp/check-acctnames-XXXX.txt)
LC_ALL=C grep '^KERNEL-NAME|' "$KERNLOG" | cut -d'|' -f2 | LC_ALL=C sort -u > "$KERN_NAMES"
{ LC_ALL=C awk -F'|' '/^INV\|/{print $3}' "$HERE/inventory-allowlist.txt"
  LC_ALL=C grep '^DRV|' "$INVLOG" | cut -d'|' -f3
} | LC_ALL=C sort -u > "$ACCT_NAMES"
UNACCOUNTED=$(LC_ALL=C comm -23 "$KERN_NAMES" "$ACCT_NAMES")
if [ "$DRV_TRAILERS" -ne "$N_DRIVERS" ]; then
  echo "  DRIVER SURFACE INCOMPLETE: expected a trailer from each of the $N_DRIVERS driver(s), saw $DRV_TRAILERS"
  ACCTFAIL=1
elif [ "${DRV_SUM:-0}" != "$N_DRV" ]; then
  echo "  DRIVER SURFACE TRUNCATED: trailers sum to ${DRV_SUM:-0}, observed $N_DRV lines"
  ACCTFAIL=1
elif [ ! -s "$KERN_NAMES" ]; then
  echo "  ACCOUNTING FAILED: Phase 2b reported no constant names — the scan was vacuous"
  ACCTFAIL=1
elif [ -n "$UNACCOUNTED" ]; then
  echo "  ACCOUNTING FAILED: the kernel holds constants that neither walk accounts for:"
  printf '%s\n' "$UNACCOUNTED" | head -20 | sed 's/^/    /'
  ACCTFAIL=1
else
  echo "  accounting: every one of $(wc -l < "$KERN_NAMES") kernel constants is covered by the corpus inventory or the instrument surface"
fi
rm -f "$KERN_NAMES" "$ACCT_NAMES"
ACCTFAIL=${ACCTFAIL:-0}
[ "$ACCTFAIL" = 0 ] || { echo "ACCOUNTING FAILED"; rm -f "$INVLOG" "$OBS" "$KERNLOG"; exit 1; }
rm -f "$INVLOG" "$OBS" "$KERNLOG"
rm -f "$INVLOG" "$OBS" "$KERNLOG"
# ── Phase 2d: SEMANTIC model/template correspondence ────────────────────────
# Phase 0d asks a text scanner what the extraction's boundary looks like. This
# phase asks LEAN what it actually is, and requires the two to agree.
#
# WHY BOTH. Round-7 review (GPT-5.6, finding F1) showed the textual classifier
# could be made to report PROVEN for a name Lean resolves to an axiom — a
# definition inside a `/- -/` comment was read as real. Worse, and found while
# repairing that: Aeneas wraps long declarations, and the old scanner required
# keyword and name on one physical line, so it SILENTLY DROPPED them. Nine to
# ten externals per fork had no row at all, and one — the tier-A/B `neg` — was
# missing from every committed table while the docs claimed that class was
# machine-checked.
#
# A source scanner cannot decide this question. Whether a name resolves to an
# assumption or to a proof is a property of the elaborated ENVIRONMENT: it turns
# on imports, namespaces, `export`, aliases and shadowing, none of which are
# visible to a regex. So the scanner's job is now only DISCOVERY — what does the
# template ask for — and even that fails closed. The verdict comes from Lean.
#
# The template itself is deliberately not imported: it declares the same names
# as the hand-written model and the two would clash. Discovery is therefore
# unavoidably textual, which is exactly why `model-correspondence.py` must stop
# rather than skip on anything it cannot parse.
echo "=== Phase 2d: semantic model/template correspondence ==="
SEMNAMES=$(mktemp /tmp/check-semnames-XXXX.txt)
SEMOUT=$(mktemp /tmp/check-semout-XXXX.txt)
python3 "$HERE/model-correspondence.py" --names "$HERE" > "$SEMNAMES" || {
  echo "MODEL CORRESPONDENCE FAILED: could not enumerate the extraction's externals."
  rm -f "$SEMNAMES" "$SEMOUT"; exit 1; }

SEM=$(mktemp "$HERE/.semcheck-XXXX.lean")
{
  # Import every generated module that is not a template. There are no name
  # clashes between crates (verified), and the crate roots transitively pull
  # their own models, so this is the same environment the proofs are built on.
  for m in $(cd "$HERE/gen" && find . -name '*.lean' -not -name '*_Template.lean' \
             | sed 's|^\./||; s|\.lean$||; s|/|.|g' | sort); do
    echo "import $m"
  done
  cat <<'LEANSEM'
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let path := System.FilePath.mk (← IO.getEnv "SEMNAMES").get!
  for line in (← IO.FS.lines path) do
    let parts := line.splitOn "|"
    if h : parts.length = 2 then
      let rel := parts[0]!
      let nm  := parts[1]!.toName
      match env.find? nm with
      | none => IO.println s!"SEM|{rel}|{parts[1]!}|ABSENT|-"
      | some ci =>
        let kind := match ci with
          | .axiomInfo _  => "axiom"
          | .defnInfo _   => "def"
          | .thmInfo _    => "theorem"
          | .opaqueInfo _ => "opaque"
          | .inductInfo _ => "inductive"
          | .ctorInfo _   => "ctor"
          | .recInfo _    => "recursor"
          | .quotInfo _   => "quot"
        let mdl := match env.getModuleIdxFor? nm with
          | some i => toString env.header.moduleNames[i]!
          | none   => "<current>"
        IO.println s!"SEM|{rel}|{parts[1]!}|{kind}|{mdl}"
LEANSEM
} > "$SEM"

cd "$AENEAS_LEAN"
SEM_RC=0
SEMNAMES="$SEMNAMES" lake env bash -c "
  set -uo pipefail
  cd '$HERE/gen' && export LEAN_PATH=\"\$LEAN_PATH:\$PWD:$HERE\"
  cd '$HERE'
  LEAN_TIMEOUT=$TIMEOUT LEAN_MAX_CORES=$CORES '$HERE/lean-guard' '$SEM'
" > "$SEMOUT" 2>&1 || SEM_RC=$?
cd "$HERE"
rm -f "$SEM" "${SEM%.lean}.olean"
if [ "$SEM_RC" -ne 0 ]; then
  echo "SEMANTIC CORRESPONDENCE FAILED: the resolver did not run."
  tail -12 "$SEMOUT" | sed 's/^/    /'
  rm -f "$SEMNAMES" "$SEMOUT"; exit 1
fi

# Every name the extraction asks for must have been resolved, and its Lean
# verdict must equal the committed table's. The mapping is deliberately strict:
#   resolves into the hand-written model module  -> MODEL
#   resolves to a NON-AXIOM in a generated module -> PROVEN
#   anything else                                 -> failure
SEMFAIL=0
NSEM=$(grep -c '^SEM|' "$SEMOUT" || true)
NWANT=$(grep -c '|' "$SEMNAMES" || true)
if [ "$NSEM" -ne "$NWANT" ]; then
  echo "  SEMANTIC CORRESPONDENCE TRUNCATED: asked about $NWANT externals, Lean answered for $NSEM"
  SEMFAIL=1
fi
while IFS='|' read -r _tag rel name kind mdl; do
  [ "$_tag" = SEM ] || continue
  want=$(awk -F'|' -v r="$rel" -v n="$name" '$1==r && $2==n {print $3}' "$HERE/MODEL-CORRESPONDENCE.txt")
  case "$kind:$mdl" in
    axiom:"${rel//\//.}")  got=MODEL ;;
    *:"${rel//\//.}")      got=MODEL ;;
    axiom:*)               got=AXIOM-OUTSIDE-MODEL ;;
    ABSENT:*)              got=UNRESOLVED ;;
    *)                     got=PROVEN ;;
  esac
  if [ -z "$want" ]; then
    echo "  SEMANTIC DRIFT: $rel|$name resolves ($kind in $mdl) but has NO ROW in MODEL-CORRESPONDENCE.txt"
    SEMFAIL=1
  elif [ "$want" != "$got" ]; then
    echo "  SEMANTIC DRIFT: $rel|$name — table says $want, Lean says $got ($kind in $mdl)"
    SEMFAIL=1
  fi
done < "$SEMOUT"
rm -f "$SEMNAMES" "$SEMOUT"
if [ "$SEMFAIL" != 0 ]; then
  echo "SEMANTIC CORRESPONDENCE FAILED: the committed table does not match what Lean resolves."
  exit 1
fi
echo "  $NWANT externals resolved by Lean; every verdict matches the committed table"
echo ""

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

# ── Phases end ──────────────────────────────────────────────────────────────
# Sentinel. Self-tests lift a phase by scanning from its header to the NEXT
# marker; without this the final phase's lift ran to end-of-file and picked up
# everything appended afterwards. Do not remove: anything added below this line
# would otherwise silently become part of the last phase from a lifter's point
# of view.

echo ""
if [ "$AUDIT_ONLY" = 1 ]; then
  echo "AUDIT-ONLY RUN — GATES PASSED, PROOFS NOT RECOMPILED."
  echo "This is NOT evidence: the kernel did not re-elaborate a single proof in"
  echo "this run. It says the gates accept the artifacts a previous full run"
  echo "left behind. For a recorded result, run ./check.sh with no arguments."
  exit 0
fi
# Only a full run earns the right to let a later --audit-only skip compiling.
source_basis > "$BASIS"
echo "ALL PROOFS PASS. ALL CERTIFICATES AXIOM-CLEAN. NO DEAD FILES."
echo "STATEMENTS AND SPECIFICATIONS BOUND TO THE COMMITTED AUDIT MANIFEST."
