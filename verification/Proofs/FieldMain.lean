/- ───────────────────────────────────────────────────────────────────────────
   Proofs/FieldMain.lean — MAIN RESULT: the transpiled `FieldElement51` code
   implements the field 𝔽_p, p = 2²⁵⁵ − 19.

   CONTEXT. The Rust crate curve25519/solana-ed25519 implements F_p on
   5 radix-2^51 u64 limbs (src/field.rs + src/backend/serial/u64/field.rs);
   Charon+Aeneas transpiled it mechanically to gen/CurveField/{Types,Funs}.lean.
   The denotation ⟪a⟫ = (a0 + a1·2^51 + a2·2^102 + a3·2^153 + a4·2^204) mod p
   and the limb-bound invariant `Bnd a c` ("all 5 limbs < c") are defined in
   Proofs/Denote.lean; per-operation specs in Add/SubNeg/Mul/Square/Const/
   Invert-Spec.lean; the Field-Fp instance and surjectivity in Field.lean.

   WHY THIS SHAPE. A literal `Field Fe` instance is mathematically impossible:
   * the representation is REDUNDANT — a field element has many limb
     representations, so e.g. `mul_comm` is FALSE as an equality of limb
     vectors (only the denotations agree);
   * the operations are PARTIAL — machine arithmetic can overflow, so every
     transpiled op returns in the `Result` monad (`ok r` = success, `fail` =
     panic/overflow) and is only guaranteed on bounded inputs.
   So "the transpiled code is a field" is formalized the standard way for
   verified implementations, through the surjective denotation:

     * 𝔽_p (= `ZMod P`) IS a field          — mathlib instance + our
       axiom-free primality certificate for p (Proofs/P25519.lean);
     * the denotation ⟪·⟫ : Fe → 𝔽_p is surjective on bounded elements;
     * every transpiled operation TOTALLY (no panic) realizes the
       corresponding field operation of 𝔽_p through ⟪·⟫, under the
       documented limb-bound invariant (the dalek 2⁵⁴ discipline, which the
       Rust code itself asserts via debug_assert! → `massert`);
     * consequently every field axiom holds for the implementation up to
       denotation — proved below as the `impl_*` corollaries, each of which
       RUNS the actual transpiled functions.

   THIS FILE contains, in order:
     1. `run_*` combinators — one per operation, converting the spec triples
        `x ⦃ post ⦄` into plain existentials `∃ r, x = ok r ∧ Bnd r _ ∧ ⟪r⟫ = _`
        (via `spec_exists`), with bounds normalized to the uniform 2⁵²/2⁵⁴
        discipline;
     2. `IsFieldImplementation` — the certificate Prop bundling surjectivity
        and the eight operation contracts;
     3. `fieldImplementation` — THE MAIN THEOREM: the certificate holds;
     4. the `impl_*` corollaries — every field axiom, at implementation level.

   AXIOM HYGIENE: `#print axioms fieldImplementation` reports only Lean's
   three standard axioms [propext, Classical.choice, Quot.sound] — no sorry,
   no native_decide, no custom axiom (the 4 axioms modeling externals in
   gen/CurveField/FunsExternal.lean are outside the dependency cone).

   Nothing in gen/ (the transpiled code) was modified.

   Imports: InvertSpec.lean (which transitively pulls in every other Proofs/
   file).  Imported by: nothing — this is the root of the development.
   ─────────────────────────────────────────────────────────────────────── -/
import Proofs.InvertSpec
open Aeneas Aeneas.Std Result
open curve25519

set_option maxHeartbeats 4000000

namespace CurveFieldProofs

/-! ## Runners: totality + facts for each transpiled op

One `run_*` theorem per operation. Each takes the operation's spec triple
(from the *Spec.lean files), passes it through `spec_exists`
(Proofs/Field.lean) to obtain `∃ r, op = ok r ∧ …` — "the machine code
RUNS without panicking and returns r" — and normalizes the output bound
to the uniform validity discipline:

   Valid (= Bnd · 2⁵²)  ──any op──▶  output Bnd ≤ 2⁵²  (add: 2⁵³)

so the results can be chained: any output is again a legal input (after the
trivial weakening 2⁵² ≤ 2⁵⁴, `valid54` below). -/

/- RUST ANALOG: `FieldElement51::ZERO` (constant [0,0,0,0,0]),
   curve25519/solana-ed25519/src/backend/serial/u64/field.rs.
   MATH:  fe_zero = ok z  with  Bnd(z, 2^52)  and  ⟪z⟫ = 0.
   WHY NEEDED: the additive identity of the implementation (`zero_ok`). -/
theorem run_zero : ∃ z, fe_zero = ok z ∧ Bnd z (2^52) ∧ ⟪z⟫ = 0 := by
  obtain ⟨z, hz, _, h1, h2⟩ := spec_exists zero_spec  -- ConstSpecs.lean
  exact ⟨z, hz, h1.mono (by norm_num), h2⟩            -- weaken 2^51 → 2^52

/- RUST ANALOG: `FieldElement51::ONE` (constant [1,0,0,0,0]),
   curve25519/solana-ed25519/src/backend/serial/u64/field.rs.
   MATH:  fe_one = ok o  with  Bnd(o, 2^52)  and  ⟪o⟫ = 1.
   WHY NEEDED: the multiplicative identity of the implementation (`one_ok`). -/
theorem run_one : ∃ o, fe_one = ok o ∧ Bnd o (2^52) ∧ ⟪o⟫ = 1 := by
  obtain ⟨o, ho, h1, h2⟩ := spec_exists one_spec      -- ConstSpecs.lean
  exact ⟨o, ho, h1.mono (by norm_num), h2⟩            -- weaken 2^51 → 2^52

/- RUST ANALOG: `impl Add for FieldElement51` (the `+` operator: plain
   limbwise addition, NO reduction),
   curve25519/solana-ed25519/src/backend/serial/u64/field.rs.
   MATH:  Bnd(a,2^52) and Bnd(b,2^52)  ==>
          fe_add a b = ok r,  Bnd(r, 2^53),  ⟪r⟫ = ⟪a⟫ + ⟪b⟫.
   Limbwise addition merely doubles the bound (2^52+2^52 = 2^53 < 2^64, so
   no u64 overflow); the value is EXACT, the denotation adds mod p.
   The base `add_spec` (AddSpec.lean) needs per-limb no-overflow hypotheses
   and yields the generic bound law "Bnd a c → Bnd b c → Bnd r (2c)"; this
   runner instantiates both at c = 2^52.
   WHY NEEDED: `add_ok`, and the additive `impl_*` laws. -/
theorem run_add {a b : Fe} (ha : Bnd a (2^52)) (hb : Bnd b (2^52)) :
    ∃ r, fe_add a b = ok r ∧ Bnd r (2^53) ∧ ⟪r⟫ = ⟪a⟫ + ⟪b⟫ := by
  -- name the 5 limbs of each argument and turn `Bnd` into per-limb bounds
  obtain ⟨x0, x1, x2, x3, x4, hla⟩ := Fe.exists_limbs a
  obtain ⟨y0, y1, y2, y3, y4, hlb⟩ := Fe.exists_limbs b
  have hba := (Bnd_eq a _ _ _ _ _ _ hla).mp ha
  have hbb := (Bnd_eq b _ _ _ _ _ _ hlb).mp hb
  -- run add_spec; each pairwise sum < 2^53 < 2^64 is closed by omega
  obtain ⟨r, hr, _, hval, hbnd⟩ :=
    spec_exists (add_spec a b x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 hla hlb
      ⟨by omega, by omega, by omega, by omega, by omega⟩)
  -- bound: instantiate the "doubles any common bound" law at 2^52
  refine ⟨r, hr, by simpa using hbnd (2^52) ha hb, ?_⟩
  -- value: feVal r = feVal a + feVal b, then push through the mod-p cast
  simp [denote, hval]

/- RUST ANALOG: `impl Sub for FieldElement51` (the `-` operator: add 16p
   limbwise before subtracting to avoid u64 underflow, then reduce),
   curve25519/solana-ed25519/src/backend/serial/u64/field.rs.
   MATH:  Bnd(a,2^54) and Bnd(b,2^54)  ==>
          fe_sub a b = ok r,  Bnd(r, 2^52),  ⟪r⟫ = ⟪a⟫ − ⟪b⟫.
   WHY NEEDED: `sub_ok` (subtraction is definable from neg+add, but the Rust
   API exposes it as a primitive, so the certificate covers it directly). -/
theorem run_sub {a b : Fe} (ha : Bnd a (2^54)) (hb : Bnd b (2^54)) :
    ∃ r, fe_sub a b = ok r ∧ Bnd r (2^52) ∧ ⟪r⟫ = ⟪a⟫ - ⟪b⟫ := by
  -- sub_spec (SubNegSpec.lean) already has the desired post; just supply limbs
  obtain ⟨x0, x1, x2, x3, x4, hla⟩ := Fe.exists_limbs a
  obtain ⟨y0, y1, y2, y3, y4, hlb⟩ := Fe.exists_limbs b
  exact spec_exists (sub_spec a b x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 hla hlb ha hb)

/- RUST ANALOG: `FieldElement51::negate` (computes 16p − a limbwise, reduces),
   curve25519/solana-ed25519/src/backend/serial/u64/field.rs.
   MATH:  Bnd(a,2^54)  ==>  fe_neg a = ok r,  Bnd(r, 2^52),  ⟪r⟫ = −⟪a⟫.
   WHY NEEDED: `neg_ok`; additive inverses (`impl_add_neg`). -/
theorem run_neg {a : Fe} (ha : Bnd a (2^54)) :
    ∃ r, fe_neg a = ok r ∧ Bnd r (2^52) ∧ ⟪r⟫ = -⟪a⟫ := by
  obtain ⟨x0, x1, x2, x3, x4, hla⟩ := Fe.exists_limbs a
  exact spec_exists (neg_spec a x0 x1 x2 x3 x4 hla ha)

/- RUST ANALOG: `impl Mul for FieldElement51` (the `*` operator: radix-2^51
   schoolbook with 19-folding — 2^255 ≡ 19 (mod p) lets the high half fold
   back as ×19 — u128 accumulators, carry chain),
   curve25519/solana-ed25519/src/backend/serial/u64/field.rs.
   MATH:  Bnd(a,2^54) and Bnd(b,2^54)  ==>
          fe_mul a b = ok r,  Bnd(r, 2^52),  ⟪r⟫ = ⟪a⟫ · ⟪b⟫.
   (mul_spec' actually gives the sharper bound 2^51 + 2^13; weakened here to
   the uniform 2^52.)  Totality includes the two in-code debug_assert!s.
   WHY NEEDED: `mul_ok`, and the multiplicative `impl_*` laws. -/
theorem run_mul {a b : Fe} (ha : Bnd a (2^54)) (hb : Bnd b (2^54)) :
    ∃ r, fe_mul a b = ok r ∧ Bnd r (2^52) ∧ ⟪r⟫ = ⟪a⟫ * ⟪b⟫ := by
  obtain ⟨r, hr, h1, h2⟩ := spec_exists (mul_spec' a b ha hb)
  exact ⟨r, hr, h1.mono (by norm_num), h2⟩  -- 2^51 + 2^13 ≤ 2^52

/- RUST ANALOG: `FieldElement51::invert` (x^(p−2) by the pow22501 addition
   chain — 254 squarings + 11 multiplications),
   curve25519/solana-ed25519/src/field.rs:239-248.
   MATH:  Bnd(a,2^54)  ==>  fe_invert a = ok r,  Bnd(r, 2^52),  ⟪r⟫ = ⟪a⟫⁻¹
   — including ⟪a⟫ = 0, where both sides are 0 (mathlib's 0⁻¹ = 0 and the
   Rust code's invert(0) = 0 agree).  Proved in Proofs/InvertSpec.lean
   (Fermat's little theorem + the chain's exponent bookkeeping).
   WHY NEEDED: `inv_ok` — the field-defining operation. -/
theorem run_invert {a : Fe} (ha : Bnd a (2^54)) :
    ∃ r, fe_invert a = ok r ∧ Bnd r (2^52) ∧ ⟪r⟫ = ⟪a⟫⁻¹ :=
  spec_exists (invert_spec a ha)

/-! ## The field-implementation certificate -/

/-- The transpiled curve25519 field code implements the field 𝔽_p through the
    denotation ⟪·⟫ on limb-bounded elements: all operations are total (no
    panics / overflows) on the invariant and realize the field structure.

    This `structure … : Prop` is just a named conjunction of nine claims —
    a CERTIFICATE. Field by field:
    * `surj`    — ⟪·⟫ hits all of 𝔽_p with bounded representatives, so the
                  remaining clauses speak about every field element, not just
                  the reachable ones;
    * `zero_ok`/`one_ok` — the constants evaluate (they are `Result`s too:
                  Rust consts become monadic thunks under Aeneas) to bounded
                  elements denoting 0 and 1;
    * `add_ok`/`sub_ok`/`neg_ok`/`mul_ok`/`inv_ok` — on bounded inputs the
                  op returns `ok r` (NO PANIC — every machine-arithmetic
                  side condition holds) with `r` again bounded and
                  ⟪r⟫ = the corresponding 𝔽_p operation on the inputs.
    Together with `Field Fp` (mathlib, P prime) this is the standard meaning
    of "this code implements 𝔽_p": a literal `Field Fe` instance cannot
    exist (redundant representation, partial ops — see the file header), so
    the field laws transfer through ⟪·⟫ instead — see the `impl_*`
    corollaries below, which derive each axiom in executable form.
    WHY NEEDED: this is the STATEMENT of the main theorem. -/
structure IsFieldImplementation : Prop where
  /-- 𝔽_p is reachable: every field element has a bounded representative.
      MATH: forall y in F_p, exists a, Bnd(a,2^52) and ⟪a⟫ = y.
      (Witness: `encode` — Proofs/Field.lean.) -/
  surj : ∀ y : Fp, ∃ a : Fe, Bnd a (2^52) ∧ ⟪a⟫ = y
  /-- 0 and 1 are correctly implemented (and distinct: see `zero_ne_one`). -/
  zero_ok : ∃ z, fe_zero = ok z ∧ Bnd z (2^52) ∧ ⟪z⟫ = 0
  /-- Rust: `FieldElement51::ONE`. MATH: fe_one = ok o, Bnd(o,2^52), ⟪o⟫ = 1. -/
  one_ok : ∃ o, fe_one = ok o ∧ Bnd o (2^52) ∧ ⟪o⟫ = 1
  /-- addition (limbwise, unreduced — hence the 2⁵³ output bound) -/
  add_ok : ∀ a b, Bnd a (2^52) → Bnd b (2^52) →
    ∃ r, fe_add a b = ok r ∧ Bnd r (2^53) ∧ ⟪r⟫ = ⟪a⟫ + ⟪b⟫
  /-- subtraction (the +16p underflow trick, then reduce — Rust `impl Sub`). -/
  sub_ok : ∀ a b, Bnd a (2^54) → Bnd b (2^54) →
    ∃ r, fe_sub a b = ok r ∧ Bnd r (2^52) ∧ ⟪r⟫ = ⟪a⟫ - ⟪b⟫
  /-- negation (16p − a, then reduce — Rust `FieldElement51::negate`). -/
  neg_ok : ∀ a, Bnd a (2^54) →
    ∃ r, fe_neg a = ok r ∧ Bnd r (2^52) ∧ ⟪r⟫ = -⟪a⟫
  /-- multiplication (radix-2⁵¹ schoolbook, 19-folding — Rust `impl Mul`). -/
  mul_ok : ∀ a b, Bnd a (2^54) → Bnd b (2^54) →
    ∃ r, fe_mul a b = ok r ∧ Bnd r (2^52) ∧ ⟪r⟫ = ⟪a⟫ * ⟪b⟫
  /-- multiplicative inverse (x^(p−2); maps 0 to 0, matching 𝔽_p's 0⁻¹ = 0) -/
  inv_ok : ∀ a, Bnd a (2^54) →
    ∃ r, fe_invert a = ok r ∧ Bnd r (2^52) ∧ ⟪r⟫ = ⟪a⟫⁻¹

/-- **The transpiled code implements the field 𝔽_p.**

    THE MAIN THEOREM of the development. Each clause of the certificate is
    discharged by the corresponding `run_*` runner above (which in turn
    packages the per-operation machine-code proofs of the *Spec.lean files),
    and surjectivity by `denote_surjective` (Proofs/Field.lean).
    `#print axioms CurveFieldProofs.fieldImplementation` yields exactly
    [propext, Classical.choice, Quot.sound] — Lean's standard axioms only. -/
theorem fieldImplementation : IsFieldImplementation where
  surj := denote_surjective
  zero_ok := run_zero
  one_ok := run_one
  add_ok := fun _ _ ha hb => run_add ha hb
  sub_ok := fun _ _ ha hb => run_sub ha hb
  neg_ok := fun _ ha => run_neg ha
  mul_ok := fun _ _ ha hb => run_mul ha hb
  inv_ok := fun _ ha => run_invert ha

/-- 𝔽_p is a field (mathlib instance; p prime by Proofs/P25519.lean).
    Re-exported here under a stable name so a reader of the main theorem
    sees both halves of the claim side by side: the TARGET 𝔽_p is a field
    (this abbrev), and the CODE implements it (`fieldImplementation`).
    `noncomputable` because field inversion on `ZMod P` is classical —
    irrelevant here, we never execute it. -/
noncomputable abbrev Fp_field : Field Fp := inferInstance

/-! ## The field axioms, at the implementation level

Each `impl_*` theorem runs the actual transpiled operations and states the
corresponding field law up to denotation. They are direct consequences of
the `run_*` specs + the field structure of 𝔽_p. Throughout, `Valid a` means
`Bnd a (2^52)` (the bound every operation re-establishes).

Note the shape: a law like commutativity CANNOT be `fe_mul a b = fe_mul b a`
(the limb vectors generally differ!), nor can it ignore totality. So each
law asserts (1) all the involved operation calls return `ok` — the code
actually runs — and (2) the final denotations agree. Covered axioms:
  impl_zero_ne_one, impl_add_comm, impl_add_assoc, impl_zero_add,
  impl_add_neg, impl_mul_comm, impl_mul_assoc, impl_one_mul,
  impl_mul_inv_cancel, impl_left_distrib
— exactly the `Field` axioms of mathlib (right-distributivity and `mul_one`
etc. follow from commutativity, included here via impl_mul_comm). -/

/- The working invariant: a "valid" field element has all limbs < 2^52 —
   the bound every operation's output satisfies (add: 2^53, see add_ok) and
   `encode` satisfies, so valid elements are closed under the API.
   WHY NEEDED: gives the impl_* laws a single, chainable precondition. -/
abbrev Valid (a : Fe) : Prop := Bnd a (2^52)

/- MATH: Bnd(a,2^52) ==> Bnd(a,2^54) — trivial weakening (`Bnd.mono`).
   WHY NEEDED: sub/neg/mul/invert take inputs at the 2^54 (dalek) bound;
   this adapter lets them consume `Valid` elements. -/
theorem valid54 {a : Fe} (h : Valid a) : Bnd a (2^54) := h.mono (by norm_num)

/-- 0 ≠ 1 (the implementation is a nontrivial ring).

    MATH:  forall z o,  fe_zero = ok z and fe_one = ok o  ==>  ⟪z⟫ ≠ ⟪o⟫.
    Phrased over ANY successful evaluation of the constants (they are
    deterministic, so z/o are forced to the `run_zero`/`run_one` witnesses).
    WHY NEEDED: `Field` requires nontriviality; here it holds because
    0 ≠ 1 in ZMod P (P > 1). -/
theorem impl_zero_ne_one :
    ∀ z o, fe_zero = ok z → fe_one = ok o → ⟪z⟫ ≠ ⟪o⟫ := by
  intro z o hz ho
  obtain ⟨z', hz', _, hz0⟩ := run_zero
  obtain ⟨o', ho', _, ho1⟩ := run_one
  -- determinism: ok z = ok z' forces z = z' (same for o)
  rw [hz'] at hz; cases hz
  rw [ho'] at ho; cases ho
  rw [hz0, ho1]
  exact zero_ne_one  -- 0 ≠ 1 in the field 𝔽_p

/-- Commutativity of implemented addition.

    MATH:  Valid a, Valid b  ==>  fe_add a b = ok r1,  fe_add b a = ok r2,
           ⟪r1⟫ = ⟪r2⟫.
    (r1 = r2 as limb vectors happens to hold for add, but the law is stated
    denotationally for uniformity with mul.) -/
theorem impl_add_comm {a b : Fe} (ha : Valid a) (hb : Valid b) :
    ∃ r1 r2, fe_add a b = ok r1 ∧ fe_add b a = ok r2 ∧ ⟪r1⟫ = ⟪r2⟫ := by
  obtain ⟨r1, h1, _, hv1⟩ := run_add ha hb   -- run a + b
  obtain ⟨r2, h2, _, hv2⟩ := run_add hb ha   -- run b + a
  exact ⟨r1, r2, h1, h2, by rw [hv1, hv2, add_comm]⟩  -- add_comm in 𝔽_p

/-- Associativity of implemented addition ((a+b)+c ≃ a+(b+c)).
    Note 2⁵³+2⁵² < 2⁶⁴: the unreduced intermediate still cannot overflow.

    MATH:  Valid a, b, c  ==>  all four adds return ok and
           ⟪(a+b)+c⟫ = ⟪a+(b+c)⟫.
    The outer additions take one 2⁵³-bounded and one 2⁵²-bounded argument —
    outside `run_add`'s uniform precondition — so the proof re-invokes the
    base `add_spec` (AddSpec.lean) at the mixed bounds; the per-limb
    no-overflow side conditions 2⁵³ + 2⁵² < 2⁶⁴ close by `omega`.
    WHY NEEDED: associativity is a `Field` axiom; it also documents that one
    unreduced add can be safely chained into another. -/
theorem impl_add_assoc {a b c : Fe} (ha : Valid a) (hb : Valid b) (hc : Valid c) :
    ∃ rab rab_c rbc ra_bc,
      fe_add a b = ok rab ∧ fe_add rab c = ok rab_c ∧
      fe_add b c = ok rbc ∧ fe_add a rbc = ok ra_bc ∧
      ⟪rab_c⟫ = ⟪ra_bc⟫ := by
  -- inner additions: a+b and b+c via the uniform runner
  obtain ⟨rab, h1, hb1, hv1⟩ := run_add ha hb
  obtain ⟨rbc, h3, hb3, hv3⟩ := run_add hb hc
  -- rab : Bnd 2^53, c : 2^52 — rerun the limbwise argument at mixed bounds
  obtain ⟨x0, x1, x2, x3, x4, hla⟩ := Fe.exists_limbs rab
  obtain ⟨y0, y1, y2, y3, y4, hlb⟩ := Fe.exists_limbs c
  have hba := (Bnd_eq rab _ _ _ _ _ _ hla).mp hb1
  have hbb := (Bnd_eq c _ _ _ _ _ _ hlb).mp hc
  obtain ⟨rab_c, h2, _, hval2, _⟩ :=
    spec_exists (add_spec rab c x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 hla hlb
      ⟨by omega, by omega, by omega, by omega, by omega⟩)
  -- symmetrically for a + rbc (a : 2^52, rbc : 2^53)
  obtain ⟨u0, u1, u2, u3, u4, hlu⟩ := Fe.exists_limbs a
  obtain ⟨v0, v1, v2, v3, v4, hlv⟩ := Fe.exists_limbs rbc
  have hbu := (Bnd_eq a _ _ _ _ _ _ hlu).mp ha
  have hbv := (Bnd_eq rbc _ _ _ _ _ _ hlv).mp hb3
  obtain ⟨ra_bc, h4, _, hval4, _⟩ :=
    spec_exists (add_spec a rbc u0 u1 u2 u3 u4 v0 v1 v2 v3 v4 hlu hlv
      ⟨by omega, by omega, by omega, by omega, by omega⟩)
  refine ⟨rab, rab_c, rbc, ra_bc, h1, h2, h3, h4, ?_⟩
  -- turn the exact limb-value equations into denotation equations
  have e2 : ⟪rab_c⟫ = ⟪rab⟫ + ⟪c⟫ := by
    simp [denote, hval2]
  have e4 : ⟪ra_bc⟫ = ⟪a⟫ + ⟪rbc⟫ := by
    simp [denote, hval4]
  -- finish with associativity in 𝔽_p
  rw [e2, e4, hv1, hv3, add_assoc]

/-- 0 + a ≃ a.

    MATH:  Valid a  ==>  fe_zero = ok z,  fe_add z a = ok r,  ⟪r⟫ = ⟪a⟫
    — the implemented 0 is a left additive identity (right identity follows
    with `impl_add_comm`). -/
theorem impl_zero_add {a : Fe} (ha : Valid a) :
    ∃ z r, fe_zero = ok z ∧ fe_add z a = ok r ∧ ⟪r⟫ = ⟪a⟫ := by
  obtain ⟨z, hz, hzb, hz0⟩ := run_zero      -- materialize the 0 constant
  obtain ⟨r, hr, _, hv⟩ := run_add hzb ha   -- run z + a
  exact ⟨z, r, hz, hr, by rw [hv, hz0, zero_add]⟩  -- 0 + x = x in 𝔽_p

/-- a + (−a) ≃ 0.

    MATH:  Valid a  ==>  fe_neg a = ok n,  fe_add a n = ok r,  ⟪r⟫ = 0
    — every element has an additive inverse, computed by the actual
    `negate` code (the 16p − a trick, SubNegSpec.lean). -/
theorem impl_add_neg {a : Fe} (ha : Valid a) :
    ∃ n r, fe_neg a = ok n ∧ fe_add a n = ok r ∧ ⟪r⟫ = 0 := by
  obtain ⟨n, hn, hnb, hnv⟩ := run_neg (valid54 ha)  -- n with ⟪n⟫ = −⟪a⟫
  obtain ⟨r, hr, _, hv⟩ := run_add ha hnb           -- run a + n
  exact ⟨n, r, hn, hr, by rw [hv, hnv, add_neg_cancel]⟩  -- x + (−x) = 0

/-- Commutativity of implemented multiplication.

    MATH:  Valid a, Valid b  ==>  fe_mul a b = ok r1,  fe_mul b a = ok r2,
           ⟪r1⟫ = ⟪r2⟫.
    Note r1 and r2 are generally DIFFERENT limb vectors (the schoolbook
    carry chains differ) — only the denotations coincide; this is exactly
    why the laws are stated through ⟪·⟫. -/
theorem impl_mul_comm {a b : Fe} (ha : Valid a) (hb : Valid b) :
    ∃ r1 r2, fe_mul a b = ok r1 ∧ fe_mul b a = ok r2 ∧ ⟪r1⟫ = ⟪r2⟫ := by
  obtain ⟨r1, h1, _, hv1⟩ := run_mul (valid54 ha) (valid54 hb)  -- run a·b
  obtain ⟨r2, h2, _, hv2⟩ := run_mul (valid54 hb) (valid54 ha)  -- run b·a
  exact ⟨r1, r2, h1, h2, by rw [hv1, hv2, mul_comm]⟩  -- mul_comm in 𝔽_p

/-- Associativity of implemented multiplication.

    MATH:  Valid a, b, c  ==>  all four muls return ok and
           ⟪(a·b)·c⟫ = ⟪a·(b·c)⟫.
    Chaining works because each mul output (Bnd 2⁵²) is again a legal
    mul input after `valid54` — the closure property of the invariant. -/
theorem impl_mul_assoc {a b c : Fe} (ha : Valid a) (hb : Valid b) (hc : Valid c) :
    ∃ rab rab_c rbc ra_bc,
      fe_mul a b = ok rab ∧ fe_mul rab c = ok rab_c ∧
      fe_mul b c = ok rbc ∧ fe_mul a rbc = ok ra_bc ∧
      ⟪rab_c⟫ = ⟪ra_bc⟫ := by
  -- run the four multiplications, feeding each output bound into the next
  obtain ⟨rab, h1, hb1, hv1⟩ := run_mul (valid54 ha) (valid54 hb)
  obtain ⟨rab_c, h2, _, hv2⟩ := run_mul (valid54 hb1) (valid54 hc)
  obtain ⟨rbc, h3, hb3, hv3⟩ := run_mul (valid54 hb) (valid54 hc)
  obtain ⟨ra_bc, h4, _, hv4⟩ := run_mul (valid54 ha) (valid54 hb3)
  refine ⟨rab, rab_c, rbc, ra_bc, h1, h2, h3, h4, ?_⟩
  -- rewrite all four denotations, close with mul_assoc in 𝔽_p
  rw [hv2, hv4, hv1, hv3, mul_assoc]

/-- 1 * a ≃ a.

    MATH:  Valid a  ==>  fe_one = ok o,  fe_mul o a = ok r,  ⟪r⟫ = ⟪a⟫
    — the implemented 1 is a left multiplicative identity (right identity
    follows with `impl_mul_comm`). -/
theorem impl_one_mul {a : Fe} (ha : Valid a) :
    ∃ o r, fe_one = ok o ∧ fe_mul o a = ok r ∧ ⟪r⟫ = ⟪a⟫ := by
  obtain ⟨o, ho, hob, ho1⟩ := run_one                       -- the 1 constant
  obtain ⟨r, hr, _, hv⟩ := run_mul (valid54 hob) (valid54 ha)  -- run o·a
  exact ⟨o, r, ho, hr, by rw [hv, ho1, one_mul]⟩  -- 1·x = x in 𝔽_p

/-- a · a⁻¹ ≃ 1 for a ≢ 0 — multiplicative inverses exist.

    MATH:  Valid a and ⟪a⟫ ≠ 0  ==>  fe_invert a = ok i,  fe_mul a i = ok r,
           ⟪r⟫ = 1.
    LaTeX: $\llbracket a\rrbracket \ne 0 \Rightarrow
           \llbracket a \cdot \mathrm{invert}(a)\rrbracket = 1$.
    THE field axiom — the one that distinguishes 𝔽_p from a mere ring, and
    the pay-off of InvertSpec.lean: `i` is computed by the real addition-
    chain code, `r` by the real multiplication code, and Fermat guarantees
    the product denotes 1.  (For ⟪a⟫ = 0 inversion still RUNS and returns
    the 0 element — see `inv_ok` — but of course no r with ⟪r⟫ = 1 exists.) -/
theorem impl_mul_inv_cancel {a : Fe} (ha : Valid a) (h0 : ⟪a⟫ ≠ 0) :
    ∃ i r, fe_invert a = ok i ∧ fe_mul a i = ok r ∧ ⟪r⟫ = 1 := by
  obtain ⟨i, hi, hib, hiv⟩ := run_invert (valid54 ha)  -- i with ⟪i⟫ = ⟪a⟫⁻¹
  obtain ⟨r, hr, _, hv⟩ := run_mul (valid54 ha) (valid54 hib)  -- run a·i
  exact ⟨i, r, hi, hr, by rw [hv, hiv, mul_inv_cancel₀ h0]⟩  -- x·x⁻¹ = 1

/-- Left distributivity: a·(b+c) ≃ a·b + a·c.

    MATH:  Valid a, b, c  ==>  all five ops return ok and
           ⟪a·(b+c)⟫ = ⟪a·b + a·c⟫.
    (Right distributivity follows with `impl_mul_comm`.)  The inner sum
    b+c is only Bnd 2⁵³ — still a legal mul input after weakening to 2⁵⁴,
    which is exactly why mul's precondition is the generous dalek bound. -/
theorem impl_left_distrib {a b c : Fe} (ha : Valid a) (hb : Valid b) (hc : Valid c) :
    ∃ rbc r_left rab rac r_right,
      fe_add b c = ok rbc ∧ fe_mul a rbc = ok r_left ∧
      fe_mul a b = ok rab ∧ fe_mul a c = ok rac ∧
      fe_add rab rac = ok r_right ∧
      ⟪r_left⟫ = ⟪r_right⟫ := by
  -- left side: rbc = b+c (Bnd 2^53), then a·rbc (weaken 2^53 ≤ 2^54)
  obtain ⟨rbc, h1, hb1, hv1⟩ := run_add hb hc
  obtain ⟨r_left, h2, _, hv2⟩ := run_mul (valid54 ha) (hb1.mono (by norm_num))
  -- right side: a·b, a·c, then their sum
  obtain ⟨rab, h3, hb3, hv3⟩ := run_mul (valid54 ha) (valid54 hb)
  obtain ⟨rac, h4, hb4, hv4⟩ := run_mul (valid54 ha) (valid54 hc)
  obtain ⟨r_right, h5, _, hv5⟩ := run_add hb3 hb4
  refine ⟨rbc, r_left, rab, rac, r_right, h1, h2, h3, h4, h5, ?_⟩
  -- rewrite all denotations, close with left_distrib in 𝔽_p
  rw [hv2, hv1, hv5, hv3, hv4, left_distrib]

end CurveFieldProofs
