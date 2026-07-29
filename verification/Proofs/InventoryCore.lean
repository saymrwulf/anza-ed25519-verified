/- ──────────────────────────────────────────────────────────────────────────
   Proofs/InventoryCore.lean — shared machinery for the declaration inventory.

   PORTED, NOT REINVENTED. This is the ltl-accumulator-verified design
   (Proofs/Inventory.lean there), which survived a nine-attack self-test that
   defeated a source-regex enumerator: attributed, private, indented and
   `instance` declarations were all invisible to the regex, and a nested
   `namespace Hidden theorem MTH` collided with the basename of an audited
   declaration. Reading the compiled ENVIRONMENT sees exactly what the kernel
   saw, and there is no name shape that can hide from it.

   WHY TWO DRIVERS IMPORT THIS. Unlike the accumulator, this corpus cannot be
   imported as one environment: `Proofs.Basic` and `Proofs.ConstSpecs` both
   declare `CurveFieldProofs.zero_spec`. That is deliberate and documented —
   Basic.lean is compiled by check.sh but imported by nothing, so the reuse is
   harmless — but it makes a single whole-corpus import impossible. The corpus
   therefore splits into the main chain and Basic, one driver each, and
   check.sh concatenates their output before gating. The split is asserted in
   check.sh against the compile manifest, so a module cannot fall between the
   two drivers unnoticed.

   The corpus module list lives in each DRIVER, not here, and is checked
   textually against check.sh's manifest in both directions. A listed module
   that is not actually imported is an elaboration error, not a silent skip.
   ────────────────────────────────────────────────────────────────────────── -/
import Lean

open Lean

namespace Ed25519Inventory

def kindOf : ConstantInfo → String
  | .axiomInfo  _ => "axiom"
  | .defnInfo   _ => "def"
  | .thmInfo    _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo   _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo   _ => "ctor"
  | .recInfo    _ => "recursor"

/-- Axiom cone of `n`, from the kernel's own collector — the same machinery
    `#print axioms` uses.

    NO INDEPENDENT SECOND WALKER HERE, and that is a deliberate REDUCTION in
    strength against the ltl-accumulator design this is ported from. There, a
    hand-written closure walker runs alongside `collectAxioms` and every
    constant must get the same answer from both, so the two implementations
    check each other. Porting that walker to this corpus was tried on
    2026-07-29 and abandoned on evidence:

      · without traversing inductive families it UNDER-approximated —
        `CurveFieldProofs.EdPoint`: walker [] vs kernel [Classical.choice,
        Quot.sound, propext];
      · adding constructors, recursor rules and `all` groups made it
        OVER-approximate — `CurveFieldProofs.ProjPoint`: walker
        [Classical.choice, Quot.sound, propext] vs kernel [].

    Disagreeing in BOTH directions means the second implementation is not an
    independent check, it is a second wrong answer. Matching the kernel's
    traversal exactly over mathlib's inductive shapes is a Lean-internals
    project, not a gate, and shipping a walker that is wrong in two directions
    would be worse than shipping none: it would fail builds for reasons that
    are the checker's fault and teach everyone to ignore it.

    CONSEQUENCE, stated so nobody assumes otherwise: on this corpus the cone
    figures rest on `collectAxioms` alone. The accumulator's corpus is
    mathlib-free, its walker agrees there, and it KEEPS the cross-check. This
    is recorded in TRUSTED-BASE.md. -/
def axiomCone (n : Name) : MetaM (Array Name) := do
  let cone ← collectAxioms n
  return cone.qsort (fun a b => a.toString < b.toString)

/-- Emit `INV|name|kind|cone` for every constant originating in `corpus`.
    EVERY constant is emitted — fully qualified, NO filtering. Compiler-
    generated auxiliaries (equation lemmas, match/eq/induct helpers, private
    manglings) are emitted too and pinned in the allowlist, so anything new,
    renamed, removed, or with a changed cone shows up as a diff. -/
def emitInventory (corpus : Array Name) : MetaM Unit := do
  let env ← getEnv
  let mut idxs : Array Nat := #[]
  for m in corpus do
    match env.getModuleIdx? m with
    | some i => idxs := idxs.push i
    | none   => throwError "INVENTORY ERROR: corpus module {m} is not imported"
  let mut lines : Array String := #[]
  for (n, ci) in env.constants.toList do
    if let some i := env.getModuleIdxFor? n then
      if idxs.contains i then
        let cone ← axiomCone n
        let coneStr := ",".intercalate (cone.toList.map (·.toString))
        -- The ORIGINATING MODULE is part of the record, unlike the accumulator's
        -- format. It has to be: this corpus contains two distinct declarations
        -- both named `CurveFieldProofs.zero_spec` (Proofs.Basic and
        -- Proofs.ConstSpecs), inventoried by different drivers. Keyed on name
        -- alone their records were byte-identical, so the merged allowlist held
        -- 3021 entries for 3022 declarations and one real declaration was
        -- covered by an entry describing a different one. The count trailer
        -- caught it; the module field is what fixes it.
        let mdl := env.header.moduleNames[i]!
        lines := lines.push s!"INV|{mdl}|{n}|{kindOf ci}|{coneStr}"
  let sorted := lines.qsort (· < ·)
  for l in sorted do
    IO.println l
  -- Output-integrity trailer: a truncated or crashed run must never pass as an
  -- empty diff. inventory_gate.sh compares this against the lines it actually
  -- received, in both directions.
  IO.println s!"INV-COUNT|{sorted.size}"

end Ed25519Inventory
