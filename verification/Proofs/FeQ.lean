/- ───────────────────────────────────────────────────────────────────────────
   Proofs/FeQ.lean — `FeQ`: the transpiled Rust code as a LITERAL mathlib
   `Field` instance (and a ring isomorphism `FeQ ≃+* 𝔽_p`).

   CONTEXT.  The Rust crate curve25519/solana-ed25519 implements 𝔽_p,
   p = 2²⁵⁵ − 19, on five radix-2⁵¹ u64 limbs (`FieldElement51`); the code was
   transpiled mechanically (Charon + Aeneas) to gen/CurveField/{Types,Funs}.lean.
   Proofs/FieldMain.lean proved THE MAIN THEOREM (`fieldImplementation`): under
   the dalek limb-bound invariant every transpiled operation is TOTAL (panic-
   free) and realizes the corresponding 𝔽_p operation through the denotation
   ⟪·⟫ : Fe → 𝔽_p.

   WHY THIS FILE.  `fieldImplementation` is a *certificate about* the code; the
   field axioms appear there as `impl_*` corollaries, each phrased "the ops run
   and the denotations satisfy the law".  One step remains to make the claim
   "the Rust code IS a field" literally type-check:

       instance : Field FeQ

   where every CORE structure field (add, sub, neg, mul, inv, zero, one) is
   *defined by running the transpiled Rust functions*.  A `Field Fe` instance
   is impossible (see FieldMain.lean's header):
   * the representation is REDUNDANT — one field element has many limb
     vectors, so `mul_comm` etc. are FALSE as equalities of limb vectors;
   * the operations are PARTIAL — they live in the `Result` monad and are
     only guaranteed total on bounded inputs.
   The QUOTIENT fixes both defects at once, and it is the *canonical* fix:

   1. restrict to the valid elements    `VFe := {a : Fe // Bnd a 2⁵²}`
      (totality holds there: every op returns `ok` — FieldMain's runners);
   2. quotient by equality of denotations:  `FeQ := VFe / (⟪·⟫ = ⟪·⟫)`
      (redundancy disappears: a class IS a field element).

   `FeQ` is therefore "the type of field elements as the Rust code represents
   them", with no information added and none removed — and on it the field
   laws hold as REAL equalities, so a genuine `Field FeQ` instance exists.

   HOW THE OPERATIONS ARE DEFINED — `Classical.choose` extraction.  FieldMain's
   runners are existence theorems, e.g.

       run_mul : Bnd a 2⁵⁴ → Bnd b 2⁵⁴ →
                   ∃ r, fe_mul a b = ok r ∧ Bnd r 2⁵² ∧ ⟪r⟫ = ⟪a⟫·⟪b⟫.

   `(run_mul …).choose` names THE result of that run: by the equation
   `fe_mul a b = ok r` the value `r` is uniquely determined — `Result` is
   deterministic, `ok` is injective — so choice does not "pick" anything, it
   merely gives the already-determined machine result a Lean name (the
   functions cannot be executed inside Lean terms directly because they
   return in `Result`; `choose` is the standard bridge from "the run
   succeeds" to "the value of the run").  The accompanying `.choose_spec`
   hands back the program equation (`v*_runs` below — the receipt that the
   definition really is the Rust run) and the denotation fact (`v*_denote`).

   CONTENTS, in order:
     §1  `run_reduce`, `run_add_red` — two more runners: `reduce` is total on
         ANY input and denotation-preserving; `add`-then-`reduce` restores the
         2⁵² bound that bare limbwise `add` (output 2⁵³) does not.
     §2  `VFe`, the setoid (a ≈ b ↔ ⟪a⟫ = ⟪b⟫), and `FeQ` — the carrier.
     §3  `vzero vone vadd vsub vneg vmul vinv` — the operations on `VFe`,
         each extracted from a runner, with `_runs` and `_denote` facts.
     §4  congruences + `Quotient.map/map₂` lifts `qadd … qinv` to `FeQ`.
     §5  THE BRIDGE `denoteQ : FeQ → 𝔽_p` — injective AND surjective — and
         the extensionality principle `feq_ext`.
     §6  every field law for the q-operations (each proof: drop to 𝔽_p via
         `feq_ext`, rewrite with the denotation equations, close with the
         𝔽_p law).
     §7  `instance : CommRing FeQ` and `instance : Field FeQ` — built
         DIRECTLY (layered structure literals; not via Function.Injective.field),
         with the Rust-run operations as the structure fields.
     §8  `feQRingEquiv : FeQ ≃+* 𝔽_p`, `Fintype FeQ` (FeQ is a FINITE field),
         and the axiom audit (`#print axioms` — the three standard axioms).

   AXIOM HYGIENE: `#print axioms feQRingEquiv` reports only
   [propext, Classical.choice, Quot.sound] — no sorry, no native_decide, no
   custom axiom (the 4 axioms modeling externals in
   gen/CurveField/FunsExternal.lean are outside the dependency cone).
   `Classical.choice` enters exactly through the `choose` extraction
   explained above (and through mathlib's `Field 𝔽_p`); `Quot.sound` through
   the quotient.  Nothing in gen/ (the transpiled code) was modified.

   Imports: Proofs/FieldMain.lean (the main theorem and its runners, plus —
   transitively — everything else).  Imported by: nothing; this file is the
   capstone of the development.
   ─────────────────────────────────────────────────────────────────────── -/
import Proofs.FieldMain
open Aeneas Aeneas.Std Result
open curve25519

set_option maxHeartbeats 4000000

namespace CurveFieldProofs

/-! ## §1  Two more runners: `reduce`, and `add` followed by `reduce`

`run_add` (FieldMain.lean) outputs `Bnd r 2⁵³` — limbwise addition does not
reduce, so its result is NOT a valid element (`Valid` = `Bnd · 2⁵²`) and
cannot serve as the result of a `VFe`-level addition.  The Rust crate's own
answer is `FieldElement51::reduce` (one carry pass); composing the transpiled
`add` with the transpiled `reduce` yields a bound-restoring, denotation-
correct addition.  Both runners below follow the `run_*` format of
FieldMain.lean: plain existentials `∃ r, code = ok r ∧ Bnd ∧ ⟪·⟫-equation`. -/

/-- `reduce` runs on ANY input and preserves the denotation.

    RUST ANALOG: `FieldElement51::reduce`,
    curve25519/solana-ed25519/src/backend/serial/u64/field.rs:290-323 (one
    parallel carry pass; the top carry re-enters at limb 0 multiplied by 19).

    MATH:  forall a : Fe,  exists r,
           fe_reduce a = ok r,  Bnd(r, 2^52),  ⟪r⟫ = ⟪a⟫.
    LaTeX: $\forall a\ \exists r,\ \mathrm{reduce}(a)=\mathrm{ok}\,r \wedge
           \mathrm{Bnd}(r,2^{52}) \wedge \llbracket r\rrbracket =
           \llbracket a\rrbracket$.

    Note there is NO precondition: `reduce_spec` (ReduceSpec.lean) is total on
    arbitrary u64 limbs.  Its exact ℕ accounting `feVal r + p·(a₄ div 2⁵¹) =
    feVal a` becomes `⟪r⟫ = ⟪a⟫` after one cast to 𝔽_p, because the term
    `p·…` is a multiple of p and vanishes (`ZMod.natCast_self : (p : 𝔽_p) = 0`).
    The output bound 2⁵¹ + 19·2¹³ is weakened to the uniform 2⁵².

    WHY NEEDED: the second half of `run_add_red`; gives `vadd` (§3) a result
    that is again `Valid`. -/
theorem run_reduce (a : Fe) :
    ∃ r, fe_reduce a = ok r ∧ Bnd r (2^52) ∧ ⟪r⟫ = ⟪a⟫ := by
  -- name the limbs (reduce_spec needs them) and run the spec
  obtain ⟨a0, a1, a2, a3, a4, hl⟩ := Fe.exists_limbs a
  obtain ⟨r, hr, hbnd, hval⟩ := spec_exists (reduce_spec a a0 a1 a2 a3 a4 hl)
  refine ⟨r, hr, hbnd.mono (by norm_num), ?_⟩   -- 2^51 + 19·2^13 ≤ 2^52
  -- hval : feVal r + P * (a4.val / 2^51) = feVal a   (exact, over ℕ).
  -- Cast both sides into 𝔽_p; the P-multiple dies (P ≡ 0 mod P).
  have hcast : ((feVal r + P * (a4.val / 2^51) : ℕ) : Fp)
      = ((feVal a : ℕ) : Fp) := by rw [hval]
  simpa [denote, ZMod.natCast_self] using hcast

/-- Valid + Valid → Valid addition: the transpiled `add` CHAINED INTO the
    transpiled `reduce` (at the program level, with the monadic `do`).

    RUST ANALOG: `&a + &b` followed by `(…).reduce()` — exactly what the crate
    itself does whenever a sum must satisfy the limb discipline again (e.g.
    inside `AddAssign`/point formulas); both functions are the transpiled
    originals, composed in the `Result` monad.

    MATH:  Bnd(a,2^52), Bnd(b,2^52)  ==>  exists r,
           (add a b >>= reduce) = ok r,  Bnd(r, 2^52),  ⟪r⟫ = ⟪a⟫ + ⟪b⟫.
    LaTeX: $\llbracket r\rrbracket = \llbracket a\rrbracket +
           \llbracket b\rrbracket$ with $r$ again 2⁵²-bounded.

    WHY NEEDED: this is the program `vadd` (§3) extracts its value from —
    bare `run_add`'s 2⁵³ output bound would leave `VFe` not closed under
    addition. -/
theorem run_add_red {a b : Fe} (ha : Bnd a (2^52)) (hb : Bnd b (2^52)) :
    ∃ r, (do
            let s ← fe_add a b
            fe_reduce s) = ok r ∧ Bnd r (2^52) ∧ ⟪r⟫ = ⟪a⟫ + ⟪b⟫ := by
  -- run the limbwise add (result s, Bnd 2^53, ⟪s⟫ = ⟪a⟫+⟪b⟫) …
  obtain ⟨s, hs, _, hsv⟩ := run_add ha hb
  -- … then the carry pass (any input is legal; ⟪·⟫ preserved)
  obtain ⟨r, hr, hrb, hrv⟩ := run_reduce s
  refine ⟨r, ?_, hrb, ?_⟩
  · -- the do-block: once `fe_add a b` is rewritten to `ok s`, the bind
    -- reduces definitionally and the goal IS `fe_reduce s = ok r`.
    rw [hs]
    exact hr
  · rw [hrv, hsv]

/-! ## §2  The carrier: valid elements, the setoid, and the quotient `FeQ` -/

/-- A VALID field element: a limb vector together with the proof that it
    satisfies the working invariant `Bnd · 2⁵²` (= `Valid`, FieldMain.lean) —
    the bound every transpiled operation re-establishes and `encode`
    satisfies.

    RUST ANALOG: a `FieldElement51` that respects the crate's documented limb
    discipline (u64/field.rs:26-42) — i.e. every value the Rust API actually
    produces.

    MATH:  VFe = { a : Fe | all limbs of a are < 2^52 }.

    WHY NEEDED: on `VFe` every operation of the API is TOTAL (the runners'
    preconditions hold), so operations extracted from the runners are honest
    functions `VFe → VFe`. -/
def VFe := {a : Fe // Bnd a (2^52)}

/-- Two valid elements are equivalent iff they DENOTE the same element of 𝔽_p.

    MATH:  a ≈ b  iff  ⟪a⟫ = ⟪b⟫  — the kernel of the denotation map.
    Reflexivity/symmetry/transitivity are inherited from `=` on 𝔽_p.

    WHY NEEDED: the limb representation is redundant (e.g. the `mul` carry
    chains produce DIFFERENT limb vectors for `a*b` and `b*a`); identifying
    denotation-equal vectors is exactly what makes the field laws equalities. -/
instance vfeSetoid : Setoid VFe :=
  ⟨fun a b => ⟪a.1⟫ = ⟪b.1⟫,
   fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- Unfolding lemma for the setoid relation (definitionally true).
    WHY NEEDED: lets later proofs move between `a ≈ b` and the denotation
    equation without relying on definitional unfolding inside `rw`. -/
theorem vfe_equiv_iff {a b : VFe} : a ≈ b ↔ ⟪a.1⟫ = ⟪b.1⟫ := Iff.rfl

/-- **The type of field elements, as the Rust code represents them.**

    MATH:  FeQ = VFe / ≈  — bounded limb vectors modulo equal denotation.
    LaTeX: $\mathrm{FeQ} = \{a : \mathrm{Fe} \mid \mathrm{Bnd}(a,2^{52})\}
           /\ (\llbracket\cdot\rrbracket = \llbracket\cdot\rrbracket)$.

    An element of `FeQ` is an equivalence class of valid limb vectors; the
    bridge `denoteQ` (§5) shows `FeQ` is in BIJECTION with 𝔽_p.  On this type
    — and only on this type — "the Rust operations form a field" can be a
    literal `Field` instance (§7).

    WHY NEEDED: the whole point of the file. -/
def FeQ := Quotient vfeSetoid

/-! ## §3  The operations on `VFe`: extracted from the Rust runs

Each definition below is `Classical.choose` of a runner — i.e. *the value the
transpiled Rust function returns on the given inputs* (see the file header:
the run equation `… = ok r` pins the value uniquely; `choose` only names it).
For each operation we record two facts:

  * `v*_runs`   — the program equation `transpiled-code inputs = ok (v* …)`,
                  the RECEIPT that the definition is the Rust run (kept
                  reachable for documentation; the algebra below only needs
                  the denotation);
  * `v*_denote` — the denotation equation, e.g. ⟪vmul a b⟫ = ⟪a⟫·⟪b⟫,
                  which powers every law in §6.

All definitions are `noncomputable` — Lean cannot RUN the extracted machine
code (it lives in the `Result` monad and `choose` is classical) — but they
are definitionally tied to it by the `v*_runs` equations. -/

/-- The zero of the implementation: the run of `FieldElement51::ZERO`
    (limbs [0,0,0,0,0]).  RUST ANALOG: u64/field.rs:263.
    MATH: ⟪vzero⟫ = 0 (see `vzero_denote`). -/
noncomputable def vzero : VFe :=
  ⟨run_zero.choose, run_zero.choose_spec.2.1⟩

/-- Receipt: `vzero` IS the value of the transpiled constant. -/
theorem vzero_runs : fe_zero = ok vzero.1 := run_zero.choose_spec.1

/-- MATH: ⟪vzero⟫ = 0 in 𝔽_p. -/
theorem vzero_denote : ⟪vzero.1⟫ = 0 := run_zero.choose_spec.2.2

/-- The one of the implementation: the run of `FieldElement51::ONE`
    (limbs [1,0,0,0,0]).  RUST ANALOG: u64/field.rs:265. -/
noncomputable def vone : VFe :=
  ⟨run_one.choose, run_one.choose_spec.2.1⟩

/-- Receipt: `vone` IS the value of the transpiled constant. -/
theorem vone_runs : fe_one = ok vone.1 := run_one.choose_spec.1

/-- MATH: ⟪vone⟫ = 1 in 𝔽_p. -/
theorem vone_denote : ⟪vone.1⟫ = 1 := run_one.choose_spec.2.2

/-- Addition on valid elements: the value of the Rust run
    `add a b >>= reduce` (see `run_add_red` — the reduce restores the 2⁵²
    bound that bare limbwise add does not).
    RUST ANALOG: `&a + &b` then `.reduce()` (u64/field.rs:68-72, 290-323). -/
noncomputable def vadd (a b : VFe) : VFe :=
  ⟨(run_add_red a.2 b.2).choose, (run_add_red a.2 b.2).choose_spec.2.1⟩

/-- Receipt: `vadd a b` IS the value of the transpiled add-then-reduce run. -/
theorem vadd_runs (a b : VFe) :
    (do
       let s ← fe_add a.1 b.1
       fe_reduce s) = ok (vadd a b).1 :=
  (run_add_red a.2 b.2).choose_spec.1

/-- MATH: ⟪vadd a b⟫ = ⟪a⟫ + ⟪b⟫ in 𝔽_p. -/
theorem vadd_denote (a b : VFe) : ⟪(vadd a b).1⟫ = ⟪a.1⟫ + ⟪b.1⟫ :=
  (run_add_red a.2 b.2).choose_spec.2.2

/-- Subtraction on valid elements: the value of the Rust run of `sub`
    (the +16p underflow trick, then reduce — already 2⁵²-bounded, no extra
    reduce needed).  RUST ANALOG: `&a - &b`, u64/field.rs:84-101. -/
noncomputable def vsub (a b : VFe) : VFe :=
  ⟨(run_sub (valid54 a.2) (valid54 b.2)).choose,
   (run_sub (valid54 a.2) (valid54 b.2)).choose_spec.2.1⟩

/-- Receipt: `vsub a b` IS the value of the transpiled `sub` run. -/
theorem vsub_runs (a b : VFe) : fe_sub a.1 b.1 = ok (vsub a b).1 :=
  (run_sub (valid54 a.2) (valid54 b.2)).choose_spec.1

/-- MATH: ⟪vsub a b⟫ = ⟪a⟫ − ⟪b⟫ in 𝔽_p. -/
theorem vsub_denote (a b : VFe) : ⟪(vsub a b).1⟫ = ⟪a.1⟫ - ⟪b.1⟫ :=
  (run_sub (valid54 a.2) (valid54 b.2)).choose_spec.2.2

/-- Negation on valid elements: the value of the Rust run of `negate`
    (16p − a limbwise, then reduce).  RUST ANALOG: u64/field.rs:276-286. -/
noncomputable def vneg (a : VFe) : VFe :=
  ⟨(run_neg (valid54 a.2)).choose, (run_neg (valid54 a.2)).choose_spec.2.1⟩

/-- Receipt: `vneg a` IS the value of the transpiled `negate` run. -/
theorem vneg_runs (a : VFe) : fe_neg a.1 = ok (vneg a).1 :=
  (run_neg (valid54 a.2)).choose_spec.1

/-- MATH: ⟪vneg a⟫ = −⟪a⟫ in 𝔽_p. -/
theorem vneg_denote (a : VFe) : ⟪(vneg a).1⟫ = -⟪a.1⟫ :=
  (run_neg (valid54 a.2)).choose_spec.2.2

/-- Multiplication on valid elements: the value of the Rust run of `mul`
    (radix-2⁵¹ schoolbook with ×19 folding, u128 carry chain).
    RUST ANALOG: `&a * &b`, u64/field.rs:115-213. -/
noncomputable def vmul (a b : VFe) : VFe :=
  ⟨(run_mul (valid54 a.2) (valid54 b.2)).choose,
   (run_mul (valid54 a.2) (valid54 b.2)).choose_spec.2.1⟩

/-- Receipt: `vmul a b` IS the value of the transpiled `mul` run. -/
theorem vmul_runs (a b : VFe) : fe_mul a.1 b.1 = ok (vmul a b).1 :=
  (run_mul (valid54 a.2) (valid54 b.2)).choose_spec.1

/-- MATH: ⟪vmul a b⟫ = ⟪a⟫ · ⟪b⟫ in 𝔽_p. -/
theorem vmul_denote (a b : VFe) : ⟪(vmul a b).1⟫ = ⟪a.1⟫ * ⟪b.1⟫ :=
  (run_mul (valid54 a.2) (valid54 b.2)).choose_spec.2.2

/-- Inversion on valid elements: the value of the Rust run of `invert`
    (x^(p−2) by the pow22501 addition chain: 254 squarings + 11 mults;
    maps 0 to 0 exactly like mathlib's `0⁻¹ = 0`).
    RUST ANALOG: field.rs:239-248. -/
noncomputable def vinv (a : VFe) : VFe :=
  ⟨(run_invert (valid54 a.2)).choose, (run_invert (valid54 a.2)).choose_spec.2.1⟩

/-- Receipt: `vinv a` IS the value of the transpiled `invert` run. -/
theorem vinv_runs (a : VFe) : fe_invert a.1 = ok (vinv a).1 :=
  (run_invert (valid54 a.2)).choose_spec.1

/-- MATH: ⟪vinv a⟫ = ⟪a⟫⁻¹ in 𝔽_p (with the 0 ↦ 0 convention on both sides). -/
theorem vinv_denote (a : VFe) : ⟪(vinv a).1⟫ = ⟪a.1⟫⁻¹ :=
  (run_invert (valid54 a.2)).choose_spec.2.2

/-! ## §4  Lifting to the quotient

Each operation descends to `FeQ` because it RESPECTS the relation: if the
inputs denote the same field elements, so do the outputs — immediate from the
`v*_denote` equations, since the 𝔽_p-side value depends only on the input
denotations.  (This is the formal content of "the result of the Rust run is
well-defined up to representation".) -/

/-- `vadd` respects ≈ (congruence for `Quotient.map₂`).
    MATH: ⟪a⟫=⟪a'⟫ and ⟪b⟫=⟪b'⟫ ⟹ ⟪vadd a b⟫ = ⟪a⟫+⟪b⟫ = ⟪a'⟫+⟪b'⟫ = ⟪vadd a' b'⟫. -/
theorem vadd_congr : ∀ ⦃a a' : VFe⦄, a ≈ a' → ∀ ⦃b b' : VFe⦄, b ≈ b' →
    vadd a b ≈ vadd a' b' := by
  intro a a' ha b b' hb
  exact vfe_equiv_iff.mpr (by
    rw [vadd_denote, vadd_denote, vfe_equiv_iff.mp ha, vfe_equiv_iff.mp hb])

/-- `vsub` respects ≈. -/
theorem vsub_congr : ∀ ⦃a a' : VFe⦄, a ≈ a' → ∀ ⦃b b' : VFe⦄, b ≈ b' →
    vsub a b ≈ vsub a' b' := by
  intro a a' ha b b' hb
  exact vfe_equiv_iff.mpr (by
    rw [vsub_denote, vsub_denote, vfe_equiv_iff.mp ha, vfe_equiv_iff.mp hb])

/-- `vmul` respects ≈. -/
theorem vmul_congr : ∀ ⦃a a' : VFe⦄, a ≈ a' → ∀ ⦃b b' : VFe⦄, b ≈ b' →
    vmul a b ≈ vmul a' b' := by
  intro a a' ha b b' hb
  exact vfe_equiv_iff.mpr (by
    rw [vmul_denote, vmul_denote, vfe_equiv_iff.mp ha, vfe_equiv_iff.mp hb])

/-- `vneg` respects ≈. -/
theorem vneg_congr : ∀ ⦃a a' : VFe⦄, a ≈ a' → vneg a ≈ vneg a' := by
  intro a a' ha
  exact vfe_equiv_iff.mpr (by
    rw [vneg_denote, vneg_denote, vfe_equiv_iff.mp ha])

/-- `vinv` respects ≈. -/
theorem vinv_congr : ∀ ⦃a a' : VFe⦄, a ≈ a' → vinv a ≈ vinv a' := by
  intro a a' ha
  exact vfe_equiv_iff.mpr (by
    rw [vinv_denote, vinv_denote, vfe_equiv_iff.mp ha])

/- The q-operations: the Rust-run operations, lifted to equivalence classes.
   `Quotient.map₂ f h ⟦a⟧ ⟦b⟧ = ⟦f a b⟧` definitionally, so each q-op applied
   to classes literally computes "run the Rust code on representatives and
   take the class of the result". -/

/-- Addition on `FeQ` (Rust `add` + `reduce`, lifted). -/
noncomputable def qadd : FeQ → FeQ → FeQ := Quotient.map₂ vadd vadd_congr
/-- Subtraction on `FeQ` (Rust `sub`, lifted). -/
noncomputable def qsub : FeQ → FeQ → FeQ := Quotient.map₂ vsub vsub_congr
/-- Multiplication on `FeQ` (Rust `mul`, lifted). -/
noncomputable def qmul : FeQ → FeQ → FeQ := Quotient.map₂ vmul vmul_congr
/-- Negation on `FeQ` (Rust `negate`, lifted). -/
noncomputable def qneg : FeQ → FeQ := Quotient.map vneg vneg_congr
/-- Inversion on `FeQ` (Rust `invert`, lifted). -/
noncomputable def qinv : FeQ → FeQ := Quotient.map vinv vinv_congr
/-- Zero of `FeQ` (the class of the Rust `ZERO` constant). -/
noncomputable def qzero : FeQ := ⟦vzero⟧
/-- One of `FeQ` (the class of the Rust `ONE` constant). -/
noncomputable def qone : FeQ := ⟦vone⟧

/-! Notation instances: register the q-operations as the meaning of
`+ - * ⁻¹ 0 1` on `FeQ`.  Declared BEFORE the ring/field structures so that
(a) mathlib's recursor defaults (`nsmulRec`/`zsmulRec`, which need standalone
`Zero`/`Add`/`Neg` instances) can fire, and (b) the structures below can cite
exactly these operations as their data fields. -/

noncomputable instance : Add FeQ := ⟨qadd⟩
noncomputable instance : Sub FeQ := ⟨qsub⟩
noncomputable instance : Mul FeQ := ⟨qmul⟩
noncomputable instance : Neg FeQ := ⟨qneg⟩
noncomputable instance : Inv FeQ := ⟨qinv⟩
noncomputable instance : Zero FeQ := ⟨qzero⟩
noncomputable instance : One FeQ := ⟨qone⟩

/-! ## §5  THE BRIDGE: `denoteQ : FeQ → 𝔽_p` is a bijection

The denotation ⟪·⟫ : Fe → 𝔽_p is neither injective (redundant limbs) nor
total-friendly (unbounded elements break the ops).  On `FeQ` both defects are
gone: `denoteQ` is INJECTIVE by construction of the quotient and SURJECTIVE
by `encode` (Field.lean) — `FeQ` and 𝔽_p are the same field in different
clothes, which §8 upgrades to a ring isomorphism. -/

/-- The denotation of an equivalence class: well-defined because the relation
    IS "equal denotation" (the congruence proof is the identity).

    MATH:  denoteQ ⟦a⟧ = ⟪a⟫. -/
noncomputable def denoteQ : FeQ → Fp :=
  Quotient.lift (fun a : VFe => ⟪a.1⟫) (fun _ _ h => h)

/-- Computation rule for `denoteQ` on classes (definitional). -/
@[simp] theorem denoteQ_mk (a : VFe) : denoteQ ⟦a⟧ = ⟪a.1⟫ := rfl

/-- `denoteQ` is INJECTIVE: equal denotations ⟹ equal classes.

    MATH: denoteQ x = denoteQ y ⟹ x = y — quotienting by the kernel of ⟪·⟫
    makes the induced map injective (`Quotient.sound` does all the work).
    WHY NEEDED: half of "FeQ ≅ 𝔽_p"; powers the extensionality `feq_ext`. -/
theorem denoteQ_injective : Function.Injective denoteQ := by
  intro x y
  refine Quotient.inductionOn₂ x y fun a b h => ?_
  exact Quotient.sound h

/-- `denoteQ` is SURJECTIVE: every element of 𝔽_p is the denotation of a
    class — witness: the class of `encode y` (the canonical base-2⁵¹ digits
    of y, bounded by 2⁵¹ ≤ 2⁵², Field.lean).

    MATH: forall y : 𝔽_p, exists x : FeQ, denoteQ x = y.
    WHY NEEDED: the other half of "FeQ ≅ 𝔽_p". -/
theorem denoteQ_surjective : Function.Surjective denoteQ := fun y =>
  ⟨⟦(⟨encode y, (encode_bnd y).mono (by norm_num)⟩ : VFe)⟧, denote_encode y⟩

/-- EXTENSIONALITY for `FeQ`: two classes are equal iff they denote the same
    element of 𝔽_p.

    MATH:  x = y  ⟺  denoteQ x = denoteQ y.
    (⟸ is `denoteQ_injective`, i.e. induction on both quotients +
    `Quotient.sound`; ⟹ is `congrArg`.)

    WHY NEEDED: THE proof device of §6/§7 — every field axiom for `FeQ` drops
    through `feq_ext.mpr` to an equation in 𝔽_p, where mathlib's field theory
    closes it. -/
theorem feq_ext {x y : FeQ} : x = y ↔ denoteQ x = denoteQ y :=
  ⟨fun h => by rw [h], fun h => denoteQ_injective h⟩

/-! Denotation equations for the q-operations: `denoteQ` is a homomorphism
for every Rust-run operation.  Each proof is quotient induction + the
`v*_denote` fact of §3 (definitional on representatives). -/

/-- MATH: denoteQ (qadd x y) = denoteQ x + denoteQ y. -/
theorem denoteQ_qadd (x y : FeQ) :
    denoteQ (qadd x y) = denoteQ x + denoteQ y := by
  refine Quotient.inductionOn₂ x y fun a b => ?_
  exact vadd_denote a b

/-- MATH: denoteQ (qsub x y) = denoteQ x − denoteQ y. -/
theorem denoteQ_qsub (x y : FeQ) :
    denoteQ (qsub x y) = denoteQ x - denoteQ y := by
  refine Quotient.inductionOn₂ x y fun a b => ?_
  exact vsub_denote a b

/-- MATH: denoteQ (qmul x y) = denoteQ x · denoteQ y. -/
theorem denoteQ_qmul (x y : FeQ) :
    denoteQ (qmul x y) = denoteQ x * denoteQ y := by
  refine Quotient.inductionOn₂ x y fun a b => ?_
  exact vmul_denote a b

/-- MATH: denoteQ (qneg x) = −denoteQ x. -/
theorem denoteQ_qneg (x : FeQ) : denoteQ (qneg x) = -denoteQ x := by
  refine Quotient.inductionOn x fun a => ?_
  exact vneg_denote a

/-- MATH: denoteQ (qinv x) = (denoteQ x)⁻¹. -/
theorem denoteQ_qinv (x : FeQ) : denoteQ (qinv x) = (denoteQ x)⁻¹ := by
  refine Quotient.inductionOn x fun a => ?_
  exact vinv_denote a

/-- MATH: denoteQ qzero = 0. -/
theorem denoteQ_qzero : denoteQ qzero = 0 := vzero_denote

/-- MATH: denoteQ qone = 1. -/
theorem denoteQ_qone : denoteQ qone = 1 := vone_denote

/-! ## §6  The field laws for the q-operations

Every law has the same one-line proof skeleton:

    feq_ext.mpr (drop to 𝔽_p) → rewrite with denoteQ_q* → the 𝔽_p law (ring /
    field_simp / mul_inv_cancel₀).

This is precisely the transfer "the implementation satisfies the axiom
because 𝔽_p does and the denotations agree" — the same content as the
`impl_*` corollaries of FieldMain.lean, but now as REAL equalities on `FeQ`. -/

/-- (x+y)+z = x+(y+z) on FeQ. -/
theorem qadd_assoc (x y z : FeQ) : qadd (qadd x y) z = qadd x (qadd y z) :=
  feq_ext.mpr (by simp only [denoteQ_qadd]; ring)

/-- x+y = y+x on FeQ. -/
theorem qadd_comm (x y : FeQ) : qadd x y = qadd y x :=
  feq_ext.mpr (by simp only [denoteQ_qadd]; ring)

/-- 0+x = x on FeQ. -/
theorem qzero_add (x : FeQ) : qadd qzero x = x :=
  feq_ext.mpr (by simp only [denoteQ_qadd, denoteQ_qzero]; ring)

/-- x+0 = x on FeQ. -/
theorem qadd_zero (x : FeQ) : qadd x qzero = x :=
  feq_ext.mpr (by simp only [denoteQ_qadd, denoteQ_qzero]; ring)

/-- (−x)+x = 0 on FeQ — additive inverses, computed by Rust `negate`. -/
theorem qneg_add_cancel (x : FeQ) : qadd (qneg x) x = qzero :=
  feq_ext.mpr (by simp only [denoteQ_qadd, denoteQ_qneg, denoteQ_qzero]; ring)

/-- x−y = x+(−y) on FeQ: the Rust `sub` agrees with `add`-of-`negate`
    (denotationally — the limb-level programs are different!). -/
theorem qsub_eq_add_neg (x y : FeQ) : qsub x y = qadd x (qneg y) :=
  feq_ext.mpr (by simp only [denoteQ_qsub, denoteQ_qadd, denoteQ_qneg]; ring)

/-- (x·y)·z = x·(y·z) on FeQ. -/
theorem qmul_assoc (x y z : FeQ) : qmul (qmul x y) z = qmul x (qmul y z) :=
  feq_ext.mpr (by simp only [denoteQ_qmul]; ring)

/-- x·y = y·x on FeQ (false at limb level, true on the quotient!). -/
theorem qmul_comm (x y : FeQ) : qmul x y = qmul y x :=
  feq_ext.mpr (by simp only [denoteQ_qmul]; ring)

/-- 1·x = x on FeQ. -/
theorem qone_mul (x : FeQ) : qmul qone x = x :=
  feq_ext.mpr (by simp only [denoteQ_qmul, denoteQ_qone]; ring)

/-- x·1 = x on FeQ. -/
theorem qmul_one (x : FeQ) : qmul x qone = x :=
  feq_ext.mpr (by simp only [denoteQ_qmul, denoteQ_qone]; ring)

/-- x·(y+z) = x·y + x·z on FeQ. -/
theorem qleft_distrib (x y z : FeQ) :
    qmul x (qadd y z) = qadd (qmul x y) (qmul x z) :=
  feq_ext.mpr (by simp only [denoteQ_qmul, denoteQ_qadd]; ring)

/-- (x+y)·z = x·z + y·z on FeQ. -/
theorem qright_distrib (x y z : FeQ) :
    qmul (qadd x y) z = qadd (qmul x z) (qmul y z) :=
  feq_ext.mpr (by simp only [denoteQ_qmul, denoteQ_qadd]; ring)

/-- 0·x = 0 on FeQ. -/
theorem qzero_mul (x : FeQ) : qmul qzero x = qzero :=
  feq_ext.mpr (by simp only [denoteQ_qmul, denoteQ_qzero]; ring)

/-- x·0 = 0 on FeQ. -/
theorem qmul_zero (x : FeQ) : qmul x qzero = qzero :=
  feq_ext.mpr (by simp only [denoteQ_qmul, denoteQ_qzero]; ring)

/-- 0 ≠ 1 on FeQ — the implementation is a nontrivial ring (because
    0 ≠ 1 in 𝔽_p: p ≥ 2, primality from Proofs/P25519.lean). -/
theorem qzero_ne_qone : qzero ≠ qone := by
  intro h
  have h' := feq_ext.mp h
  rw [denoteQ_qzero, denoteQ_qone] at h'
  exact zero_ne_one h'

/-- x·x⁻¹ = 1 for x ≠ 0 — THE field axiom, with the inverse computed by the
    real Rust addition chain (`invert`) and the product by the real Rust
    `mul`; Fermat's little theorem (InvertSpec.lean) makes it 1. -/
theorem qmul_inv_cancel (x : FeQ) (h : x ≠ qzero) : qmul x (qinv x) = qone := by
  -- x ≠ qzero transfers to denoteQ x ≠ 0 along the bijection
  have h0 : denoteQ x ≠ 0 := fun hz =>
    h (feq_ext.mpr (by rw [hz, denoteQ_qzero]))
  exact feq_ext.mpr (by
    rw [denoteQ_qmul, denoteQ_qinv, denoteQ_qone, mul_inv_cancel₀ h0])

/-- 0⁻¹ = 0 on FeQ: the Rust `invert` maps 0 to 0 (it computes 0^(p−2) = 0),
    matching mathlib's junk-value convention exactly. -/
theorem qinv_qzero : qinv qzero = qzero :=
  feq_ext.mpr (by rw [denoteQ_qinv, denoteQ_qzero, inv_zero])

/-! ## §7  `FeQ` IS a mathlib field — with the Rust runs as structure fields

Built DIRECTLY, in two layers (CommRing, then Field), so that the data
fields are EXACTLY the q-operations of §4 — i.e. the Rust-run operations:

    add = qadd (Rust add+reduce)   mul = qmul (Rust mul)
    neg = qneg (Rust negate)       sub = qsub (Rust sub)
    inv = qinv (Rust invert)       0 = ⟦Rust ZERO⟧   1 = ⟦Rust ONE⟧

The remaining *auxiliary* data (nsmul/zsmul/npow/natCast/intCast, div, zpow,
ℚ-casts) is left to mathlib's canonical defaults — they are DERIVED from the
core ops (e.g. `div a b := a * b⁻¹` runs Rust mul + invert) and carry no
axiomatic content.  `nnqsmul := _`/`qsmul := _` follow the instruction in
mathlib's `DivisionRing` docstring (unification fills `(cast · * ·)`). -/

/-- `FeQ` is a commutative ring, operation by operation the Rust code. -/
noncomputable instance instCommRingFeQ : CommRing FeQ where
  add := qadd
  add_assoc := qadd_assoc
  zero := qzero
  zero_add := qzero_add
  add_zero := qadd_zero
  add_comm := qadd_comm
  mul := qmul
  left_distrib := qleft_distrib
  right_distrib := qright_distrib
  zero_mul := qzero_mul
  mul_zero := qmul_zero
  mul_assoc := qmul_assoc
  one := qone
  one_mul := qone_mul
  mul_one := qmul_one
  neg := qneg
  sub := qsub
  sub_eq_add_neg := qsub_eq_add_neg
  neg_add_cancel := qneg_add_cancel
  mul_comm := qmul_comm
  -- auxiliary data: mathlib's canonical recursors (iterated qadd/qneg —
  -- still the Rust operations underneath)
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- **`FeQ` is a mathlib `Field`** — the punchline instance: the transpiled
    Rust curve25519 field code, packaged as the literal field-of-mathlib
    structure (inverse = the Rust `invert` addition chain). -/
noncomputable instance instFieldFeQ : Field FeQ :=
  { instCommRingFeQ with
    inv := qinv
    exists_pair_ne := ⟨qzero, qone, qzero_ne_qone⟩
    mul_inv_cancel := qmul_inv_cancel
    inv_zero := qinv_qzero
    nnqsmul := _
    qsmul := _ }

/-! Denotation equations restated against the INSTANCE notation (+, *, -, ⁻¹,
0, 1 now resolve through the `Field FeQ` instance; definitionally these are
the q-operations, so the §5 lemmas transfer verbatim).  Tagged `@[simp]` —
they make `denoteQ` a `simp`-transparent field homomorphism. -/

/-- MATH: denoteQ (x + y) = denoteQ x + denoteQ y (instance `+` = qadd). -/
@[simp] theorem denoteQ_add (x y : FeQ) :
    denoteQ (x + y) = denoteQ x + denoteQ y := denoteQ_qadd x y

/-- MATH: denoteQ (x − y) = denoteQ x − denoteQ y (instance `-` = qsub). -/
@[simp] theorem denoteQ_sub (x y : FeQ) :
    denoteQ (x - y) = denoteQ x - denoteQ y := denoteQ_qsub x y

/-- MATH: denoteQ (x · y) = denoteQ x · denoteQ y (instance `*` = qmul). -/
@[simp] theorem denoteQ_mul (x y : FeQ) :
    denoteQ (x * y) = denoteQ x * denoteQ y := denoteQ_qmul x y

/-- MATH: denoteQ (−x) = −denoteQ x (instance `-` = qneg). -/
@[simp] theorem denoteQ_neg (x : FeQ) : denoteQ (-x) = -denoteQ x :=
  denoteQ_qneg x

/-- MATH: denoteQ x⁻¹ = (denoteQ x)⁻¹ (instance `⁻¹` = qinv). -/
@[simp] theorem denoteQ_inv (x : FeQ) : denoteQ x⁻¹ = (denoteQ x)⁻¹ :=
  denoteQ_qinv x

/-- MATH: denoteQ 0 = 0 (instance `0` = ⟦Rust ZERO⟧). -/
@[simp] theorem denoteQ_zero : denoteQ (0 : FeQ) = 0 := vzero_denote

/-- MATH: denoteQ 1 = 1 (instance `1` = ⟦Rust ONE⟧). -/
@[simp] theorem denoteQ_one : denoteQ (1 : FeQ) = 1 := vone_denote

/-! ## §8  The ring isomorphism `FeQ ≃+* 𝔽_p`, finiteness, axiom audit -/

/-- **The implementation is THE field 𝔽_p**: a ring isomorphism between the
    quotiented Rust representation and mathlib's `ZMod (2²⁵⁵ − 19)`.

    MATH:  FeQ ≅ 𝔽_p  as rings (hence as fields):
           forward map  = denoteQ (read off the limbs mod p),
           backward map = the class of `encode` (write the base-2⁵¹ digits),
           mutually inverse by `denote_encode`, homomorphic by §5.

    WHY NEEDED: this single object packages the whole development — a reader
    who trusts mathlib's `ZMod` only needs this term and its axiom audit
    below to conclude the Rust field code is correct. -/
noncomputable def feQRingEquiv : FeQ ≃+* Fp where
  toFun := denoteQ
  invFun y := ⟦(⟨encode y, (encode_bnd y).mono (by norm_num)⟩ : VFe)⟧
  left_inv x := feq_ext.mpr (denote_encode (denoteQ x))
  right_inv y := denote_encode y
  map_mul' := denoteQ_mul
  map_add' := denoteQ_add

/-- Sanity check (compile-time): the `Field FeQ` instance really is in scope —
    "the Rust code is a mathlib field" type-checks. -/
noncomputable example : Field FeQ := inferInstance

/-- `FeQ` is FINITE (transport `Fintype 𝔽_p` along the isomorphism):
    together with the instance above, the Rust code is literally a FINITE
    FIELD in mathlib's vocabulary. -/
noncomputable instance : Fintype FeQ :=
  Fintype.ofEquiv Fp feQRingEquiv.symm.toEquiv

/- AXIOM AUDIT.  Expected (and verified) output, for the isomorphism AND for
   the `Field` instance itself:
     'CurveFieldProofs.feQRingEquiv' depends on axioms:
       [propext, Classical.choice, Quot.sound]
     'CurveFieldProofs.instFieldFeQ' depends on axioms:
       [propext, Classical.choice, Quot.sound]
   — Lean's three standard axioms only: no sorry, no native_decide, no custom
   axiom (in particular none of the external-function axioms of
   gen/CurveField/FunsExternal.lean). -/
#print axioms feQRingEquiv
#print axioms instFieldFeQ

end CurveFieldProofs
