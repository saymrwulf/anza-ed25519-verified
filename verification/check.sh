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
  inventory-allowlist.txt   # the audit surface Phase 2c diffs against
  inventory-allowlist-scalar.txt # the scalar layer's audit surface (second button)
  Proofs/Audit.lean         # the audit driver: it computes the digest it is judged by
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
  for m in ${PROOFS[*]}; do
    [ -f \"Proofs/\$m.lean\" ] || { echo \"MISSING: Proofs/\$m.lean listed in manifest\"; exit 1; }
    compile \"Proofs/\$m\"
  done
  # every shipped proof file must be in the manifest (no dead files)
  for f in Proofs/*.lean; do
    b=\$(basename \"\$f\" .lean)
    [ \"\$b\" = AxiomCheck ] && continue
    # Inventory drivers are compiled by Phase 2c, not here: they must elaborate
    # with the corpus already in the environment, and the two of them cannot be
    # imported together. They are NOT unchecked — Phase 2b reads their compiled
    # .olean like every other module, and Phase 0c pins their sources.
    case \"\$b\" in Inventory|InventoryBasic|InventoryCore|InventoryScalar) continue;; esac
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
rm -f "$INVLOG" "$OBS"

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
