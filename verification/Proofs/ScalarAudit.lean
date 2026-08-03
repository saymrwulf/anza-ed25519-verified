import Proofs.ScalarDenote
import Proofs.ScalarLoop
import Proofs.ScalarSubSpec
import Proofs.ScalarAddSpec
import Proofs.ScalarMulSpec
import Proofs.ScalarMontSpec
import Proofs.ScalarReduceSpec
import Proofs.ScalarFullMulSpec
import Proofs.ScalarMain
import Proofs.ScalarWideSpec
import Proofs.ScalarBytesSpec
import Proofs.ScalarUnpackSpec
import Proofs.ScalarFromBytesSpec
import Lean
open Lean Elab Command

namespace Ed25519ScalarAudit

/-- Lean's three kernel axioms. -/
def kernel3 : List Name := [`propext, `Classical.choice, `Quot.sound]

/-- This fork's apex boundary: the hash oracle and wire-format symbols the
    signature-level certificates are permitted to rest on, and nothing else.
    POLICY CONSTANT — folded into the digest, so widening it moves the hash
    and fails the build. -/
def apexExtra : List Name := []   -- the scalar layer has NO apex tier

def apexBoundary : List Name := kernel3 ++ apexExtra

/-- A constant counts as SPECIFICATION if it was declared in a `Proofs.`
    module — i.e. hand-written by us, as opposed to the extracted model in
    `gen/` (pinned separately by Phase 0). Derived from the environment, not
    from a list, so a new specification module cannot appear unnoticed. -/
def specPrefix : String := "Proofs."

/-- Per-certificate expected cone. Arithmetic tier first, apex tier last. -/
def manifest : List (Name × List Name) :=
  [ (`ScalarProofs.L_val,                          kernel3)
  , (`ScalarProofs.sub_loop_spec,                  kernel3)
  , (`ScalarProofs.cond_add_l_one_spec,            kernel3)
  , (`ScalarProofs.sub_val_spec,                   kernel3)
  , (`ScalarProofs.add_val_spec,                   kernel3)
  , (`ScalarProofs.mul_internal_spec,              kernel3)
  , (`ScalarProofs.part1_spec,                     kernel3)
  , (`ScalarProofs.montgomery_reduce_spec,         kernel3)
  , (`ScalarProofs.mul_spec,                       kernel3)
  , (`ScalarProofs.scalarImplementation,           kernel3)
  , (`ScalarProofs.montgomery_mul_spec,            kernel3)
  , (`ScalarProofs.bytes_unpack_spec,              kernel3)
  , (`ScalarProofs.from_bytes_wide_spec,           kernel3)
  ]

/-- Deterministic name ordering for the canonical serialization. -/
def sortNames (l : List Name) : List Name :=
  ((l.map toString).toArray.qsort (· < ·)).toList.map (·.toName)

/-- Whitespace-canonical: every whitespace run collapses to one space, so the
    pretty-printer's line wrapping cannot perturb the digest. -/
def normWs (s : String) : String :=
  (s.foldl (fun (acc : String × Bool) c =>
      let c := if c.isWhitespace then ' ' else c
      if c == ' ' then (if acc.2 then acc else (acc.1.push ' ', true))
      else (acc.1.push c, false))
    ("", true)).1

/-- Was `n` hand-written by us, in a `Proofs.` module? -/
def isSpecConst (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => (toString env.header.moduleNames[idx.toNat]!).startsWith specPrefix
  | none => false

/-- Transitive closure over specification constants, starting from a
    certificate's STATEMENT and following DEFINITION bodies (a theorem
    contributes its statement only). This discovers the reference definitions —
    and any future one — automatically, so a new specification cannot be
    introduced, or an existing one redefined, without moving the digest. -/
partial def closureOf (env : Environment) (seen : NameSet) (work : List Name) : NameSet :=
  match work with
  | [] => seen
  | n :: rest =>
    if seen.contains n || !isSpecConst env n then closureOf env seen rest
    else
      let seen := seen.insert n
      let more := match env.find? n with
        | some (.defnInfo v) => v.value.getUsedConstants.toList ++ v.type.getUsedConstants.toList
        | some ci            => ci.type.getUsedConstants.toList
        | none               => []
      closureOf env seen (more ++ rest)

/-- Fully-explicit (`pp.all`) rendering, whitespace-canonicalized. Implicit
    arguments, instances and universe levels are all made visible, so two
    statements that merely LOOK alike cannot share a rendering. -/
def ppAll (e : Expr) : CommandElabM String := do
  let s ← Command.liftCoreM <| Meta.MetaM.run' <|
    withOptions (fun o => o.setBool `pp.all true) do
      return (← Meta.ppExpr e).pretty
  return normWs s

elab "auditScalarStatements" : command => do
  let env ← getEnv
  let mut errs : Array String := #[]

  -- (0) The manifest may not permit an axiom outside the two declared tiers.
  --     Without this, widening a cone in the manifest would be invisible.
  for (cert, cone) in manifest do
    for a in cone do
      unless apexBoundary.contains a do
        errs := errs.push s!"manifest permits {a} for {cert}, which is outside every declared tier"

  -- (1) Each certificate must EXIST, be a THEOREM, and have EXACTLY its cone.
  --     Exact, not subset: a certificate that stopped depending on the hash
  --     oracle is as wrong as one that acquired a new axiom.
  for (cert, expected) in manifest do
    match env.find? cert with
    | none                 => errs := errs.push s!"{cert}: NOT FOUND (renamed or deleted?)"
    | some (.thmInfo _)    =>
        let got := (← collectAxioms cert).toList
        let extras  := got.filter      (fun a => !expected.contains a)
        let missing := expected.filter (fun a => !got.contains a)
        unless extras.isEmpty && missing.isEmpty do
          errs := errs.push s!"{cert}: cone extra={extras} missing={missing}"
    | some (.axiomInfo _)  => errs := errs.push s!"{cert}: is an AXIOM, not a proven theorem"
    | some (.opaqueInfo _) => errs := errs.push s!"{cert}: is OPAQUE, not a proven theorem"
    | some _               => errs := errs.push s!"{cert}: is not a theorem"

  unless errs.isEmpty do
    throwError "AUDIT FAILED (fail-closed):\n{String.intercalate "\n" errs.toList}"

  -- (2) CANONICAL BLOCK: policy, then statements, then specification bodies.
  let mut lines : Array String := #[]
  lines := lines.push
    s!"policy|kernel3={String.intercalate "," ((sortNames kernel3).map toString)}|apexExtra={String.intercalate "," ((sortNames apexExtra).map toString)}|specPrefix={specPrefix}"
  let mut specs : NameSet := {}
  for (cert, cone) in manifest do
    let ci := (env.find? cert).get!
    specs := (closureOf env {} ci.type.getUsedConstants.toList).toList.foldl (·.insert ·) specs
    lines := lines.push
      s!"cert|{cert}|cone={String.intercalate "," ((sortNames cone).map toString)}|type={← ppAll ci.type}"
  for nm in sortNames specs.toList do
    match env.find? nm with
    | none => errs := errs.push s!"specification constant vanished mid-audit: {nm}"
    | some ci =>
      let isProp ← Command.liftCoreM <| Meta.MetaM.run' <| Meta.isProp ci.type
      -- Proof irrelevance: a Prop-valued constant contributes its STATEMENT; a
      -- data definition contributes its BODY, which is where fidelity lives.
      if isProp then
        lines := lines.push s!"spec|{nm}|prop|type={← ppAll ci.type}"
      else
        match ci with
        | .defnInfo v => lines := lines.push s!"spec|{nm}|def|value={← ppAll v.value}"
        | _           => lines := lines.push s!"spec|{nm}|other|type={← ppAll ci.type}"

  unless errs.isEmpty do
    throwError "AUDIT FAILED (fail-closed):\n{String.intercalate "\n" errs.toList}"

  -- FAIL CLOSED ON ABSENCE: a manifest that somehow produced no specification
  -- constants would emit a block that binds statements only. That is a weaker
  -- claim than this file advertises, so it is an error, not a quiet pass.
  if specs.toList.isEmpty then
    throwError "AUDIT FAILED: statements reached ZERO specification constants — the closure is not doing its job"

  logInfo ("SCALAR-AUDIT-MANIFEST-BEGIN\n" ++ String.intercalate "\n" lines.toList ++ "\nSCALAR-AUDIT-MANIFEST-END")
  -- check.sh cross-checks its own CERTS array against THIS line, so the two
  -- cannot drift apart without the build noticing.
  logInfo s!"AUDITED-SCALAR-CERTIFICATES: {String.intercalate " " ((manifest.map (·.1)).map toString)}"
  logInfo s!"statement audit PASSED: {manifest.length} certificates (exact cones + elaborated statements), {specs.toList.length} specification constants pinned"

end Ed25519ScalarAudit

open Ed25519ScalarAudit in
auditScalarStatements
