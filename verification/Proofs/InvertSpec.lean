/- ───────────────────────────────────────────────────────────────────────────
   Proofs/InvertSpec.lean — Spec for the transpiled `invert`: x ↦ x^(p−2) via
   the pow22501 addition chain, which by Fermat's little theorem (p prime,
   Proofs/P25519.lean) is the multiplicative inverse in 𝔽_p (with the mathlib
   convention 0⁻¹ = 0, which the Rust code also satisfies: invert(0) = 0).

   CONTEXT. The Rust crate curve25519/solana-ed25519 implements F_p,
   p = 2^255 - 19, on 5 radix-2^51 u64 limbs (`FieldElement51`). Inversion
   never divides: since the multiplicative group of F_p has order p − 1,
   Fermat gives a^(p−1) = 1 for a ≠ 0, hence a · a^(p−2) = 1, i.e.
   a^(p−2) = a⁻¹. The Rust code (curve25519/solana-ed25519/src/field.rs)
   computes x^(p−2) with a fixed 254-squaring / 11-multiplication addition
   chain (`pow22501` + `pow2k` + `mul`), transpiled by Charon+Aeneas into
   gen/CurveField/Funs.lean (`field.FieldElement51.pow22501`, `.invert`).

   THIS FILE proves the two top-of-chain specs:
     * `pow22501_spec` — the helper returns (x^(2^250−1), x^11);
     * `invert_spec`   — `invert` is total under the 2⁵⁴ limb invariant and
                         denotes ⟪x⟫⁻¹ (covering ⟪x⟫ = 0 as well).
   plus three small `'`-wrappers around the mul/square/pow2k specs so the
   `step*`/`let*` proof automation can apply them without explicit limb lists.

   ROLE IN THE MAIN THEOREM. `invert_spec` is exactly what FieldMain.lean
   packages as `run_invert` / the `inv_ok` field of `IsFieldImplementation`,
   and what makes `impl_mul_inv_cancel` (existence of multiplicative
   inverses — the defining axiom of a FIELD as opposed to a ring) true for
   the implementation.

   Imports: MulSpec/SquareSpec (the verified mul / square / pow2k machine
   code) and Field (the `Field Fp` instance — needed for `⁻¹` and Fermat,
   via Mathlib.FieldTheory.Finite.Basic's `ZMod.pow_card_sub_one_eq_one`).
   Imported by: FieldMain.lean (the summit).
   ─────────────────────────────────────────────────────────────────────── -/
import Proofs.MulSpec
import Proofs.SquareSpec
import Proofs.Field
import Mathlib.FieldTheory.Finite.Basic
open Aeneas Aeneas.Std Result
open curve25519

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace CurveFieldProofs

/-! ## Step-friendly wrappers (no explicit limb lists in the hypotheses)

The base specs in MulSpec/SquareSpec take the 5 limbs of every argument as
explicit variables (`x0 … x4`, with a hypothesis `↑a = [x0,…,x4]`), because
their proofs compute limb by limb. The `step*`/`let*` automation that walks
a monadic body cannot invent those variables, so we re-state each spec with
the limbs existentially repackaged (via `Fe.exists_limbs`: every transpiled
`Fe`, being a Rust `[u64; 5]`, HAS some 5 limbs). `@[step]` registers each
wrapper with the automation. -/

/- RUST ANALOG: `impl Mul for FieldElement51` (the `*` operator),
   curve25519/solana-ed25519/src/backend/serial/u64/field.rs (schoolbook
   radix-2^51 multiplication with 19-folding) — verified in MulSpec.lean.
   MATH:  forall a b : Fe,  Bnd(a,2^54) and Bnd(b,2^54)  ==>
          fe_mul a b = ok r  with  Bnd(r, 2^51+2^13)  and  ⟪r⟫ = ⟪a⟫·⟪b⟫.
   LaTeX: $\mathrm{Bnd}(a,2^{54}) \wedge \mathrm{Bnd}(b,2^{54}) \Rightarrow
          \llbracket r\rrbracket = \llbracket a\rrbracket\llbracket b\rrbracket$.
   WHY NEEDED: `pow22501`'s body performs 9 multiplications; each application
   inside `step*` uses this hypothesis-light form. -/
@[step]
theorem mul_spec' (a b : Fe) (hba : Bnd a (2^54)) (hbb : Bnd b (2^54)) :
    fe_mul a b ⦃ r => Bnd r (2^51 + 2^13) ∧ ⟪r⟫ = ⟪a⟫ * ⟪b⟫ ⦄ := by
  obtain ⟨x0, x1, x2, x3, x4, ha⟩ := Fe.exists_limbs a   -- materialize a's limbs
  obtain ⟨y0, y1, y2, y3, y4, hb⟩ := Fe.exists_limbs b   -- materialize b's limbs
  exact mul_spec a b x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 ha hb hba hbb

/- RUST ANALOG: `FieldElement51::square`,
   curve25519/solana-ed25519/src/backend/serial/u64/field.rs (implemented as
   `pow2k(1)`) — verified in SquareSpec.lean.
   MATH:  Bnd(a,2^54)  ==>  fe_square a = ok r,  Bnd(r, 2^51+2^13),
          ⟪r⟫ = ⟪a⟫·⟪a⟫.
   WHY NEEDED: the first three steps of the pow22501 chain are squarings. -/
@[step]
theorem square_spec' (a : Fe) (hba : Bnd a (2^54)) :
    fe_square a ⦃ r => Bnd r (2^51 + 2^13) ∧ ⟪r⟫ = ⟪a⟫ * ⟪a⟫ ⦄ := by
  obtain ⟨x0, x1, x2, x3, x4, ha⟩ := Fe.exists_limbs a
  exact square_spec a x0 x1 x2 x3 x4 ha hba

/- RUST ANALOG: `FieldElement51::pow2k` (k successive squarings, k ≥ 1),
   curve25519/solana-ed25519/src/backend/serial/u64/field.rs — verified in
   SquareSpec.lean (loop invariant over k).
   MATH:  Bnd(a,2^54) and 1 ≤ k  ==>  fe_pow2k a k = ok r,
          Bnd(r, 2^51+2^13),  ⟪r⟫ = ⟪a⟫ ^ (2^k).
   (k = 0 is excluded: the Rust body `debug_assert!(k > 0)` panics on it,
   and indeed pow2k(0) would not return a^1 but loop zero times — the
   precondition mirrors the code's own contract.)
   WHY NEEDED: the chain's big shifts (×2^5, ×2^10, …, ×2^100) are pow2k
   calls; `invert` itself ends with a pow2k(5). -/
@[step]
theorem pow2k_spec' (a : Fe) (k : U32) (hba : Bnd a (2^54)) (hk : 1 ≤ k.val) :
    fe_pow2k a k ⦃ r => Bnd r (2^51 + 2^13) ∧ ⟪r⟫ = ⟪a⟫ ^ (2^k.val) ⦄ := by
  obtain ⟨x0, x1, x2, x3, x4, ha⟩ := Fe.exists_limbs a
  exact pow2k_spec a k x0 x1 x2 x3 x4 ha hba hk

/-- Discharge: linear arithmetic, or a `Bnd` weakening from any hypothesis.

    Every step of the chain needs its inputs bounded by 2⁵⁴, but the previous
    step only guarantees 2⁵¹ + 2¹³; this side-condition tactic closes such
    goals either by `scalar_tac` (linear arithmetic over machine integers) or
    by weakening an existing `Bnd _ c` hypothesis with `Bnd.mono` and
    `c ≤ 2⁵⁴` by `norm_num`. Passed as the discharger to `step*`/`let*`.
    WHY NEEDED: keeps the 22-step chain proof to a single `step* by bnd`. -/
macro "bnd" : tactic =>
  `(tactic| (first
      | scalar_tac
      | exact Bnd.mono (by assumption) (by norm_num)))

/-! ## The pow22501 addition chain -/

/- RUST ANALOG: `FieldElement51::pow22501`,
   curve25519/solana-ed25519/src/field.rs:141-175 (transpiled as
   `field.FieldElement51.pow22501`, gen/CurveField/Funs.lean).

   MATH:  Bnd(a,2^54)  ==>  pow22501 a = ok (t19, t3)  with
          Bnd(t19, 2^52), Bnd(t3, 2^52),
          ⟪t19⟫ = ⟪a⟫ ^ (2^250 − 1)   and   ⟪t3⟫ = ⟪a⟫ ^ 11.

   THE ADDITION CHAIN (writing x = ⟪a⟫; squaring doubles the exponent,
   pow2k(k) multiplies it by 2^k, mul adds exponents). Exponent bookkeeping,
   matching the temporaries of the Rust source line by line (the transpiler
   names t0.square().square()'s intermediate `fe`):

     t0  = x^2                                   square x
     fe  = x^4                                   square t0
     t1  = x^8                                   square fe
     t2  = x * t1   = x^9                        exps 0 + 8
     t3  = t0 * t2  = x^11                       exps 2 + 9        (output 2)
     t4  = t3^2     = x^22                       square
     t5  = t2 * t4  = x^31      = x^(2^5 − 1)    exps 9 + 22
     t6  = t5^(2^5)  = x^(2^10 − 2^5)            pow2k 5
     t7  = t6 * t5   = x^(2^10 − 1)              fill low 5 bits
     t8  = t7^(2^10) = x^(2^20 − 2^10)           pow2k 10
     t9  = t8 * t7   = x^(2^20 − 1)
     t10 = t9^(2^20) = x^(2^40 − 2^20)           pow2k 20
     t11 = t10 * t9  = x^(2^40 − 1)
     t12 = t11^(2^10) = x^(2^50 − 2^10)          pow2k 10
     t13 = t12 * t7   = x^(2^50 − 1)
     t14 = t13^(2^50) = x^(2^100 − 2^50)         pow2k 50
     t15 = t14 * t13  = x^(2^100 − 1)
     t16 = t15^(2^100) = x^(2^200 − 2^100)       pow2k 100
     t17 = t16 * t15   = x^(2^200 − 1)
     t18 = t17^(2^50)  = x^(2^250 − 2^50)        pow2k 50
     t19 = t18 * t13   = x^(2^250 − 1)                             (output 1)

   i.e. the classic "all-ones exponent" ladder: an exponent 2^n − 1 (n ones
   in binary), shifted left k places by pow2k, then ORed with a smaller
   all-ones block by one multiplication.

   Bounds: every mul/square/pow2k output is < 2^51 + 2^13 ≤ 2^52 ≤ 2^54, so
   each step's output is a legal input for the next — that is the entire
   panic-freedom argument, threaded automatically by the `bnd` discharger.

   WHY NEEDED: `invert` (below) and the Rust `pow_p58` both build on this
   helper; ⟪t19⟫ = x^(2^250−1) and ⟪t3⟫ = x^11 are exactly the two facts
   `invert_spec` combines into x^(p−2). -/
theorem pow22501_spec (a : Fe) (hba : Bnd a (2^54)) :
    field.FieldElement51.pow22501 a ⦃ rr =>
      Bnd rr.1 (2^52) ∧ Bnd rr.2 (2^52) ∧
      ⟪rr.1⟫ = ⟪a⟫ ^ (2^250 - 1) ∧ ⟪rr.2⟫ = ⟪a⟫ ^ 11 ⦄ := by
  -- expose the transpiled 22-step monadic body
  unfold field.FieldElement51.pow22501
  -- walk all 22 squarings/pow2ks/muls with the @[step] specs above;
  -- every 2^54-bound side condition is discharged by `bnd`
  step* by bnd
  -- post-condition: two bounds (Bnd.mono weakening) + two exponent equations
  refine ⟨by bnd, by bnd, ?_, ?_⟩ <;>
  · simp_all only []
    -- collapse the chain: every post is ⟪·⟫ = (earlier)^e or a product;
    -- rewrite them all, then close by exponent arithmetic.
    simp_all [← pow_mul, ← pow_add, ← pow_succ]
    try ring_nf
    try norm_num

/- RUST ANALOG: `FieldElement51::invert`,
   curve25519/solana-ed25519/src/field.rs:239-248 (transpiled as
   `field.FieldElement51.invert` = the abbrev `fe_invert`,
   gen/CurveField/Funs.lean):

     let (t19, t3) = self.pow22501();   // t19 = x^(2^250−1), t3 = x^11
     let t20 = t19.pow2k(5);            // t20 = x^(2^255−2^5)
     let t21 = &t20 * &t3;              // t21 = x^(2^255−32+11) = x^(2^255−21)

   MATH:  forall a : Fe,  Bnd(a,2^54)  ==>
          fe_invert a = ok r,  Bnd(r, 2^52),  ⟪r⟫ = ⟪a⟫⁻¹  in F_p.
   LaTeX: $\mathrm{Bnd}(a,2^{54}) \Rightarrow
          \llbracket \mathrm{invert}\,a\rrbracket = \llbracket a\rrbracket^{-1}$.

   Exponent: (2^250 − 1)·2^5 + 11 = 2^255 − 32 + 11 = 2^255 − 21 = p − 2
   (since p = 2^255 − 19).  Then:
   * if ⟪a⟫ ≠ 0: Fermat's little theorem (p prime — Proofs/P25519.lean via
     the `Fact` instance in Proofs/Field.lean) gives a^(p−1) = 1, hence
     a · a^(p−2) = a^(p−1) = 1, hence a^(p−2) = a⁻¹;
   * if ⟪a⟫ = 0: 0^(p−2) = 0 (p−2 > 0), and mathlib defines 0⁻¹ = 0 in any
     field, so the equation ⟪r⟫ = ⟪a⟫⁻¹ holds UNCONDITIONALLY — matching the
     documented Rust behavior "This function returns zero on input zero".

   Note this only fixes the exponent arithmetic and Fermat; that mul/pow2k
   really compute products/powers (95 machine ops each, carries, 19-folding)
   was proved once and for all in MulSpec/SquareSpec.

   WHY NEEDED: this is the totality + correctness of field inversion —
   packaged by FieldMain.lean as `run_invert` / `inv_ok`, the ingredient
   that upgrades "commutative ring" to "field" (`impl_mul_inv_cancel`). -/
theorem invert_spec (a : Fe) (hba : Bnd a (2^54)) :
    fe_invert a ⦃ r => Bnd r (2^52) ∧ ⟪r⟫ = ⟪a⟫⁻¹ ⦄ := by
  -- expose the 3-step transpiled body
  unfold fe_invert field.FieldElement51.invert
  -- (t19, t3) ← pow22501 a   with  ⟪t19⟫ = ⟪a⟫^(2^250−1), ⟪t3⟫ = ⟪a⟫^11
  let* ⟨ t19, t3, h1, h2, h3, h4 ⟩ ← pow22501_spec by bnd
  -- t20 ← pow2k t19 5        with  ⟪t20⟫ = ⟪t19⟫^(2^5)
  let* ⟨ t20, t20_post1, t20_post2 ⟩ ← pow2k_spec' by bnd
  -- r ← mul t20 t3           with  ⟪r⟫ = ⟪t20⟫·⟪t3⟫
  let* ⟨ r, r_post1, r_post2 ⟩ ← mul_spec' by bnd
  refine ⟨by bnd, ?_⟩
  -- ⟪r⟫ = (⟪a⟫^(2^250−1))^(2^5) · ⟪a⟫^11 = ⟪a⟫^(2^255−21) = ⟪a⟫^(P−2) = ⟪a⟫⁻¹
  rw [r_post2, t20_post2, h3, h4]
  -- merge powers: (x^m)^n = x^(m·n), x^m · x^n = x^(m+n)
  rw [← pow_mul, ← pow_add]
  -- the exponent really is p − 2 (pure numeral arithmetic)
  have hexp : (2^250 - 1) * 2^5 + 11 = P - 2 := by
    norm_num [P]
  rw [hexp]
  by_cases h0 : ⟪a⟫ = 0
  · -- zero case: 0^(P−2) = 0 = 0⁻¹ (mathlib convention, P−2 > 0)
    rw [h0]
    rw [zero_pow (by norm_num [P]), inv_zero]
  · -- Fermat: a^(P−1) = 1, hence a · a^(P−2) = 1, hence a^(P−2) = a⁻¹.
    have h1 : ⟪a⟫ ^ (P - 1) = 1 := ZMod.pow_card_sub_one_eq_one h0
    have hmul : ⟪a⟫ * ⟪a⟫ ^ (P - 2) = 1 := by
      have hsplit : ⟪a⟫ * ⟪a⟫ ^ (P - 2) = ⟪a⟫ ^ (P - 1) := by
        conv_rhs => rw [show P - 1 = (P - 2) + 1 by norm_num [P]]
        rw [pow_succ]
        ring
      rw [hsplit, h1]
    -- cancel a on the left of  a · a^(P−2) = 1 = a · a⁻¹
    exact mul_left_cancel₀ h0 (by rw [hmul, mul_inv_cancel₀ h0])

end CurveFieldProofs
