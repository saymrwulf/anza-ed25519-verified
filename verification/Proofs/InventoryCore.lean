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

/-- THE INSTRUMENTS' OWN SURFACE.

    `emitInventory` walks the CORPUS. It says nothing about the modules that
    perform the audit, and until 2026-07-31 nothing else enumerated them either:
    the kernel counted 3058 declarations across this button's 43 modules while
    the inventory accounted for 3022, and the 36-declaration difference — the
    drivers' own machinery — was covered by no allowlist row.

    That difference was never a soundness hole. The drivers ARE members of
    check.sh's compile manifest, so Phase 2b's kernel-side gate reads their
    `.olean`s and an axiom in one is rejected whatever its indentation. What was
    missing is the weaker but still real property: that an instrument declares
    nothing but inert machinery, and that every declaration the kernel sees is
    ACCOUNTED FOR by exactly one of the two walks.

    The policy is not "declare nothing" — these files legitimately declare their
    own functions. It is that an instrument may not declare an AXIOM (which
    would widen the trusted base outside every cone) nor a standalone CLAIM
    (which no certificate covers and no allowlist pins). A theorem whose name
    extends a constant declared alongside it is an artefact the elaborator
    generated for a definition — well-founded recursion emits these — and is
    allowed; a theorem whose parent is not a declared constant is not. -/
def emitDrivers (drivers : Array Name) : MetaM Unit := do
  let env ← getEnv
  let mut idxs : Array Nat := #[]
  for m in drivers do
    match env.getModuleIdx? m with
    | some i => idxs := idxs.push i
    | none   => throwError "DRIVER SURFACE ERROR: driver module {m} is not imported"
  -- Two passes: collect the names first, so the artefact test can ask whether a
  -- theorem's parent is itself declared by an instrument.
  let mut names : Std.HashSet Name := {}
  let mut here : Array (Name × ConstantInfo) := #[]
  for (n, ci) in env.constants.toList do
    let mine : Bool :=
      match env.getModuleIdxFor? n with
      | some i => idxs.contains i
      | none   => true   -- declared by the module being elaborated: this driver
    if mine then
      names := names.insert n
      here := here.push (n, ci)
  let mut lines : Array String := #[]
  for (n, ci) in here do
    let k := kindOf ci
    if k == "axiom" then
      throwError "DRIVER SURFACE VIOLATION: {n} is an axiom declared by the audit \
                  infrastructure. An instrument may not widen the trusted base."
    if k == "theorem" && !names.contains n.getPrefix then
      throwError "DRIVER SURFACE VIOLATION: {n} is a standalone theorem declared by \
                  the audit infrastructure. An instrument may declare definitions \
                  and whatever the elaborator generates for them — never a claim \
                  of its own."
    -- THE CONE, and it is the second half of the accounting identity.
    --
    -- Round-8 review (Claude, register keys `drv-surface-no-cones` and
    -- `accounting-certifies-enumeration`). These rows carried name and kind
    -- only. The round-7 accounting identity then proved every kernel constant
    -- was ENUMERATED by one of the two walks — and the reviewer demonstrated
    -- that enumeration is not audit: a claim planted in an instrument WAS
    -- enumerated, as `DRV|…bait.smuggled|theorem`, with a real cone of
    -- [propext, Classical.choice, Quot.sound], and then nothing looked at it.
    -- No allowlist row covered the instrument surface, the statement digest
    -- does not reach instruments, and Phase 2b gates DECLARED AXIOMS, which is
    -- a different question from cones. Their summary: the identity "converted
    -- 36 declarations nobody enumerated into 36 declarations nobody examined.
    -- That is progress of one step, not two."
    --
    -- With the cone emitted here and the rows pinned in driver-allowlist.txt
    -- by the same gate the corpus uses, the identity and the audit coincide:
    -- a planted claim is a new row, and a new row fails closed. The
    -- name-prefix rule above is kept as a fast first line of defence but is no
    -- longer load-bearing — the reviewer showed it breaks in one line.
    let cone ← axiomCone n
    let coneStr := ",".intercalate (cone.toList.map (·.toString))
    -- THE ORIGINATING DRIVER is part of the record, for the same reason the
    -- INV rows carry their module: dalek and anza run TWO drivers, each
    -- declaring its own `corpus`, and keyed on name alone those two distinct
    -- declarations produced one byte-identical row. `sort -u` then collapsed
    -- them, the trailers summed to 37 against 36 unique rows, and the gate
    -- reported the surface truncated. Two declarations must never share a
    -- record — that is what let a real declaration hide behind another one's
    -- entry when this mistake was made on the corpus walk.
    lines := lines.push s!"DRV|{env.mainModule}|{n}|{k}|{coneStr}"
  let sorted := lines.qsort (· < ·)
  for l in sorted do
    IO.println l
  IO.println s!"DRV-COUNT|{sorted.size}"



end Ed25519Inventory
