/- ─────────────────────────────────────────────────────────────────────────────
   Proofs/Square2Spec.lean — total correctness of `square2` (compute 2·a²)

   WHAT THIS FILE PROVES
     `square2_spec` (and its step-friendly wrapper `square2_spec'`):
       ASCII:  Bnd(a, 2^54)  ==>  square2 a = ok r  with
               Bnd(r, 2^53)  and  [[r]] = 2 * ([[a]] * [[a]])
       LaTeX:  $\mathrm{Bnd}(a,2^{54}) \Rightarrow
               \llbracket \mathrm{square2}(a)\rrbracket
               = 2\,\llbracket a\rrbracket^2$
   where Bnd/[[·]] = ⟪·⟫ are the invariant and denotation of Proofs/Denote.lean
   and p = 2^255 - 19. As everywhere, `f x ⦃ post ⦄` is TOTAL correctness:
   no panic/overflow — in particular the five u64 `*= 2` multiplications of the
   doubling loop are PROVED in range, not assumed.

   RUST ANALOG
   `FieldElement51::square2`, curve25519/solana-ed25519/src/backend/serial/u64/
   field.rs:566-573:
       let mut square = self.pow2k(1);
       for i in 0..5 { square.0[i] *= 2; }
       square
   i.e. one radix-2^51 squaring (pow2k with k = 1, verified in
   Proofs/SquareSpec.lean) followed by a limbwise doubling — point doubling
   (`ProjectivePoint::double`, curve_models.rs:381-397) calls it for 2·Z².
   Charon splits the Rust `for` loop into two generated items in
   gen/CurveField/Funs.lean (same shape as `add_assign`'s loop in
   Proofs/AddSpec.lean):
     * `…FieldElement51.square2_loop.body (iter, square)` — ONE iteration,
       returning a `ControlFlow` value: it calls `Iterator::next` on the
       `Range<usize>` iterator and either answers `.done square` (range
       exhausted) or doubles limb i (`Array.index_usize`, `* 2#u64`,
       `Array.update`) and answers `.cont (iter1, a)`;
     * `…FieldElement51.square2_loop` — `Aeneas.Std.loop` applied to that body;
   and `…FieldElement51.square2` itself is `pow2k self 1#u32` bound into the
   loop started at the literal range { start := 0, end := 5 }.
   (No `fe_square2` alias exists in Proofs/Denote.lean; we use the full
   generated name throughout — Denote.lean is not modified.)

   WHY THE DOUBLING LOOP CANNOT OVERFLOW
   `pow2k` outputs limbs < 2^51 + 2^13 (pow2k_spec, Proofs/SquareSpec.lean), so
   each u64 product limb·2 is < 2^52 + 2^14 < 2^64: the `*= 2` (a genuine U64
   multiplication in the generated code, `i1 * 2#u64`) is always in range.
   The output limbs are < 2^52 + 2^14 ≤ 2^53, which is the (comfortable) bound
   we expose — still strictly below the 2^54 input invariant of mul/sub/square,
   so square2's result can feed any downstream field op directly.

   PROOF ARCHITECTURE
   Exactly the AddSpec playbook for the one other `for i in 0..5` loop in this
   crate, specialized to one array instead of two:
     * `square2_loop_spec` unrolls the loop 5-fold by hand: 5 × (apply
       `loop_step` (Proofs/AddSpec.lean), substitute the generated body, run
       `range_next_lt_spec` + index/mul/update steps — the mul's side condition
       is closed from the < 2^63 limb hypothesis) and a 6th `loop_step` where
       `range_next_ge_spec` (5 ≥ 5) makes the body return `done`. The result
       array is the input overwritten at 0..4 with the doubled limbs;
       collapsing the five set operations (`Array.set_val_eq`) gives the
       limb-exact postcondition r_i = 2·s_i.
     * `square2_spec` chains pow2k_spec (k = 1, reused as-is via `spec_bind`)
       into the loop spec (`spec_mono`), then repackages:
       - bound:  r_i = 2·s_i < 2·(2^51 + 2^13) ≤ 2^53            (omega);
       - value:  feVal r = 2·feVal s EXACTLY over ℕ (the doubling is linear
         in the limbs — omega), cast into 𝔽_p, then
         ⟪r⟫ = 2·⟪s⟫ = 2·⟪a⟫^(2^1) = 2·(⟪a⟫·⟪a⟫) — the pow2k exponent 2^1 is
         bridged to the product form by `ring`, as in square_spec.
     * `square2_spec'` is the `@[step]`-registered wrapper with the limbs
       hidden (destructured internally via `Fe.exists_limbs`), so the `step` /
       `let*` machinery of downstream proofs (e.g. point doubling) can consume
       square2 in one step.

   ROLE IN THE MAIN THEOREM
   Not a field axiom itself: square2 is an EdDSA-level optimization
   (2·Z² in `ProjectivePoint::double` saves one full mul). Verifying it here,
   with the same invariant discipline as the eleven core ops, makes the
   point-doubling code symbolically executable later.
   Imports: Proofs/SquareSpec (pow2k_spec; transitively MulSpec's architecture
   and AddSpec's loop_step / range_next_*_spec machinery).
   ───────────────────────────────────────────────────────────────────────── -/
import Proofs.SquareSpec
open Aeneas Aeneas.Std Result
open curve25519

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option linter.unusedSimpArgs false

namespace CurveFieldProofs

-- the weakest-precondition layer: spec_mono / spec_bind / spec_ok used below
open Aeneas.Std.WP

/-- Limb-level spec for the doubling loop of `square2`: total (no u64
    overflow) when all input limbs are < 2⁶³, and the output limbs are
    exactly the doubled input limbs.

    Rust: the `for i in 0..5 { square.0[i] *= 2; }` loop of
    `FieldElement51::square2`,
    curve25519/solana-ed25519/src/backend/serial/u64/field.rs:568-570
    (generated as `…FieldElement51.square2_loop` = `Aeneas.Std.loop` applied
    to `…square2_loop.body`, started at the range { start := 0, end := 5 }).

    MATH:
    ASCII:  forall s : Fe,  (s_i < 2^63 for i = 0..4)  ==>
            square2_loop {0, 5} s = ok r  with  r_i = 2 * s_i  for all i.
    LaTeX:  $\forall i,\ s_i < 2^{63} \Rightarrow \exists r,\
            \mathrm{loop}(s) = \mathrm{ok}\ r \wedge \forall i,\ r_i = 2 s_i$.
    The hypothesis is exactly the panic condition of the Rust `*= 2` on u64
    (s_i·2 < 2^64 iff s_i < 2^63); the caller instantiates it with the much
    stronger pow2k output bound 2^51 + 2^13.

    WHY NEEDED: the strongest (limb-exact) description of the loop, consumed
    by `square2_spec` below; as in AddSpec, keeping the 6-fold `loop_step`
    unrolling separate from the feVal/Bnd repackaging keeps both readable.   -/
theorem square2_loop_spec (s : Fe) (s0 s1 s2 s3 s4 : U64)
    (hs : (↑s : List U64) = [s0, s1, s2, s3, s4])
    (hbnd : s0.val < 2^63 ∧ s1.val < 2^63 ∧ s2.val < 2^63 ∧
            s3.val < 2^63 ∧ s4.val < 2^63) :
    backend.serial.u64.field.FieldElement51.square2_loop
      { start := 0#usize, «end» := 5#usize } s
      ⦃ r => ∃ r0 r1 r2 r3 r4 : U64,
        (↑r : List U64) = [r0, r1, r2, r3, r4] ∧
        r0.val = 2 * s0.val ∧ r1.val = 2 * s1.val ∧ r2.val = 2 * s2.val ∧
        r3.val = 2 * s3.val ∧ r4.val = 2 * s4.val ⦄ := by
  obtain ⟨hbnd0, hbnd1, hbnd2, hbnd3, hbnd4⟩ := hbnd
  -- expose the loop combinator (gen/CurveField/Funs.lean)
  unfold backend.serial.u64.field.FieldElement51.square2_loop
  -- Iteration 1 (i = 0)
  -- Pattern repeated for each of the 5 iterations (cf. add_limbs_spec):
  --   loop_step            — peel one iteration of the loop combinator,
  --   simp only [..body]   — substitute the loop body's definition,
  --   step with range_next_lt_spec — Iterator::next yields some i, range
  --                          advances by one,
  --   step                 — read square[i] (x_k),
  --   step                 — u64 multiply by 2#u64; its overflow side
  --                          condition is closed by hbnd_i (x_k < 2^63),
  --   step                 — write the doubled limb back (array update t_k),
  --   spec_ok              — the body returns `cont` with the updated state.
  -- hv_k records v_k = s_k · 2; hd_k records the updated array for the next
  -- round's get-after-set bookkeeping.
  apply loop_step
  simp only [backend.serial.u64.field.FieldElement51.square2_loop.body]
  step with range_next_lt_spec as ⟨o1, iter1, ho1, hs1, he1⟩
  simp only [ho1]
  step as ⟨x1, hx1⟩
  simp [hs] at hx1
  step as ⟨v0, hv0⟩
  rw [hx1] at hv0
  step as ⟨t1, hd1⟩
  try simp only [spec_ok]
  -- Iteration 2 (i = 1) — the simp at hx2 additionally rewrites through
  -- iteration 1's array update (hd1 + Array.set_val_eq: get-after-set) so the
  -- read still refers to the ORIGINAL limb s1.
  apply loop_step
  simp only [backend.serial.u64.field.FieldElement51.square2_loop.body]
  step with range_next_lt_spec as ⟨o2, iter2, ho2, hs2, he2⟩
  simp only [ho2]
  step as ⟨x2, hx2⟩
  simp [hd1, Array.set_val_eq, hs, hs1, he1] at hx2
  step as ⟨v1, hv1⟩
  rw [hx2] at hv1
  step as ⟨t2, hd2⟩
  try simp only [spec_ok]
  -- Iteration 3 (i = 2)
  apply loop_step
  simp only [backend.serial.u64.field.FieldElement51.square2_loop.body]
  step with range_next_lt_spec as ⟨o3, iter3, ho3, hs3, he3⟩
  simp only [ho3]
  step as ⟨x3, hx3⟩
  simp [hd1, hd2, Array.set_val_eq, hs, hs1, he1, hs2, he2] at hx3
  step as ⟨v2, hv2⟩
  rw [hx3] at hv2
  step as ⟨t3, hd3⟩
  try simp only [spec_ok]
  -- Iteration 4 (i = 3)
  apply loop_step
  simp only [backend.serial.u64.field.FieldElement51.square2_loop.body]
  step with range_next_lt_spec as ⟨o4, iter4, ho4, hs4, he4⟩
  simp only [ho4]
  step as ⟨x4, hx4⟩
  simp [hd1, hd2, hd3, Array.set_val_eq, hs, hs1, he1, hs2, he2, hs3, he3] at hx4
  step as ⟨v3, hv3⟩
  rw [hx4] at hv3
  step as ⟨t4, hd4⟩
  try simp only [spec_ok]
  -- Iteration 5 (i = 4)
  apply loop_step
  simp only [backend.serial.u64.field.FieldElement51.square2_loop.body]
  step with range_next_lt_spec as ⟨o5, iter5, ho5, hs5, he5⟩
  simp only [ho5]
  step as ⟨x5, hx5⟩
  simp [hd1, hd2, hd3, hd4, Array.set_val_eq, hs, hs1, he1, hs2, he2, hs3, he3,
    hs4, he4] at hx5
  step as ⟨v4, hv4⟩
  rw [hx5] at hv4
  step as ⟨t5, hd5⟩
  try simp only [spec_ok]
  -- Iteration 6 (range exhausted: 5 ≥ 5) — next returns none, body answers
  -- `done` with the accumulated element
  apply loop_step
  simp only [backend.serial.u64.field.FieldElement51.square2_loop.body]
  step with range_next_ge_spec as ⟨o6, iter6, ho6, hr6⟩
  simp only [ho6]
  try simp only [spec_ok]
  -- Final: exhibit the limbs — the result array is s's array overwritten at
  -- 0..4 with v0..v4; collapsing the five set operations (Array.set_val_eq)
  -- gives [v0,...,v4]; each value equation v_k = 2·s_k is hv_k (scalar_tac
  -- normalizes the (2#u64).val literal and the multiplication order).
  refine ⟨v0, v1, v2, v3, v4, ?_, by scalar_tac, by scalar_tac, by scalar_tac,
    by scalar_tac, by scalar_tac⟩
  simp [hd1, hd2, hd3, hd4, hd5, Array.set_val_eq, hs, hs1, hs2, hs3, hs4]

/-- Main spec for `square2`: under the 2⁵⁴ invariant, no panic, output limbs
    < 2⁵³, and the denotation is twice the square in 𝔽_p.

    Rust: `FieldElement51::square2`,
    curve25519/solana-ed25519/src/backend/serial/u64/field.rs:566-573
    (`pow2k(1)` followed by `for i in 0..5 { square.0[i] *= 2; }`).
    MATH (ASCII):  Bnd(a, 2^54)  ==>  square2 a = ok r  with
      Bnd(r, 2^53)  and  [[r]] = 2 * ([[a]] * [[a]]).
    LaTeX:  $\llbracket r\rrbracket = 2\,\llbracket a\rrbracket^2$.
    PROOF: chain pow2k_spec at k = 1 (Proofs/SquareSpec.lean) — yielding s
    with Bnd(s, 2^51 + 2^13) and ⟪s⟫ = ⟪a⟫^(2^1) — into `square2_loop_spec`
    (2^51 + 2^13 < 2^63 keeps every `*= 2` in u64 range). The doubled limbs
    give, EXACTLY over ℕ, feVal r = 2·feVal s (the radix-2^51 value is linear
    in the limbs), hence ⟪r⟫ = 2·⟪s⟫ after the cast into 𝔽_p; the exponent
    bridge ⟪a⟫^(2^1) = ⟪a⟫·⟪a⟫ is `ring`, exactly as in square_spec. Bounds:
    r_i = 2·s_i < 2^52 + 2^14 ≤ 2^53 — comfortably re-usable, since every
    downstream op only asks for < 2^54.
    WHY NEEDED: 2·Z² in point doubling (`ProjectivePoint::double`,
    curve_models.rs:381-397, generated right below square2 in Funs.lean).    -/
theorem square2_spec (a : Fe) (x0 x1 x2 x3 x4 : U64)
    (ha : (↑a : List U64) = [x0, x1, x2, x3, x4])
    (hba : Bnd a (2^54)) :
    backend.serial.u64.field.FieldElement51.square2 a
      ⦃ r => Bnd r (2^53) ∧ ⟪r⟫ = 2 * (⟪a⟫ * ⟪a⟫) ⦄ := by
  unfold backend.serial.u64.field.FieldElement51.square2
  -- run pow2k at the literal 1#u32 (its debug_assert!(k > 0) is discharged
  -- inside pow2k_spec); s carries Bnd(s, 2^51+2^13) and ⟪s⟫ = ⟪a⟫^(2^1)
  apply spec_bind (pow2k_spec a 1#u32 x0 x1 x2 x3 x4 ha hba (by scalar_tac))
  rintro s ⟨hbs, hvs⟩
  -- name the limbs of the squared element and turn its invariant into the
  -- five explicit inequalities s_i < 2^51 + 2^13
  obtain ⟨s0, s1, s2, s3, s4, hsl⟩ := Fe.exists_limbs s
  rw [Bnd_eq s s0 s1 s2 s3 s4 _ hsl] at hbs
  -- run the doubling loop: 2^51 + 2^13 < 2^63, so no u64 overflow
  apply spec_mono (square2_loop_spec s s0 s1 s2 s3 s4 hsl
    ⟨by omega, by omega, by omega, by omega, by omega⟩)
  rintro r ⟨r0, r1, r2, r3, r4, hrl, h0, h1, h2, h3, h4⟩
  -- value over ℕ: doubling every limb doubles the radix-2^51 value EXACTLY
  have hval : feVal r = 2 * feVal s := by
    rw [feVal_eq r r0 r1 r2 r3 r4 hrl, feVal_eq s s0 s1 s2 s3 s4 hsl]
    simp only [limbsVal]
    omega
  refine ⟨?_, ?_⟩
  -- bound: r_i = 2·s_i < 2·(2^51 + 2^13) = 2^52 + 2^14 ≤ 2^53
  · rw [Bnd_eq r r0 r1 r2 r3 r4 _ hrl]
    refine ⟨by omega, by omega, by omega, by omega, by omega⟩
  -- denotation: cast the exact ℕ equation into 𝔽_p, then bridge ⟪a⟫^(2^1)
  -- to ⟪a⟫·⟪a⟫ (cf. square_spec)
  · have hr2 : ⟪r⟫ = 2 * ⟪s⟫ := by
      simp only [denote]
      rw [hval]
      push_cast
      ring
    have h1v : (1#u32).val = 1 := by scalar_tac
    rw [hr2, hvs, h1v]
    ring

/-- Step-friendly wrapper for `square2_spec`: same statement with the limbs
    hidden (no `ha` hypothesis), registered with `@[step]`.

    MATH: identical to square2_spec —
      Bnd(a, 2^54)  ==>  square2 a = ok r  with  Bnd(r, 2^53)  and
      [[r]] = 2 * ([[a]] * [[a]]).
    PROOF: destructure the limbs internally via `Fe.exists_limbs` and apply
    `square2_spec`.
    WHY NEEDED: the `step`/`let*` machinery matches spec lemmas against the
    goal syntactically; a lemma whose hypotheses mention existentially-found
    limbs x0..x4 cannot be applied automatically, this one can. Downstream
    proofs about point doubling consume square2 through this lemma in one
    `let*` step.                                                            -/
@[step]
theorem square2_spec' (a : Fe) (hba : Bnd a (2^54)) :
    backend.serial.u64.field.FieldElement51.square2 a
      ⦃ r => Bnd r (2^53) ∧ ⟪r⟫ = 2 * (⟪a⟫ * ⟪a⟫) ⦄ := by
  obtain ⟨x0, x1, x2, x3, x4, ha⟩ := Fe.exists_limbs a
  exact square2_spec a x0 x1 x2 x3 x4 ha hba

end CurveFieldProofs
