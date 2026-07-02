/- ───────────────────────────────────────────────────────────────────────────
   Proofs/EdAddProjNiels.lean — coordinate-level specs for the MIXED
   addition/subtraction kernels  EdwardsPoint ± ProjectiveNielsPoint →
   CompletedPoint, and for projective-niels negation.

   CONTEXT.  The Rust crate curve25519/solana-ed25519 adds points in
   extended coordinates against a precomputed "niels" cache
   (Y+X, Y−X, Z, T·2d) using the Hisil–Wong–Carter–Dawson mixed-addition
   formulas (src/backend/serial/curve_models.rs:411-452):

       add:  PP   = (Y₁+X₁)·(Y₂+X₂)        sub:  PM   = (Y₁+X₁)·(Y₂−X₂)
             MM   = (Y₁−X₁)·(Y₂−X₂)              MP   = (Y₁−X₁)·(Y₂+X₂)
             TT2d = T₁·(T₂·2d)                   TT2d = T₁·(T₂·2d)
             ZZ   = Z₁·Z₂,  ZZ2 = ZZ+ZZ          ZZ   = Z₁·Z₂,  ZZ2 = ZZ+ZZ
             X' = PP−MM   Y' = PP+MM             X' = PM−MP   Y' = PM+MP
             Z' = ZZ2+TT2d  T' = ZZ2−TT2d        Z' = ZZ2−TT2d  T' = ZZ2+TT2d

   The result lives in the ℙ¹×ℙ¹ "completed" model ((X':Z'), (Y':T')).
   Charon+Aeneas transpiled both bodies (and the `Neg` impl for the niels
   cache, curve_models.rs:500-511) into gen/CurveField/Funs.lean.

   THIS FILE proves, for each of the three kernels, TOTAL correctness at the
   COORDINATE level (the statement policy of the point-op phase):

     * hypotheses  — only the EdDenote validity predicates (`ExtValid`,
       `ProjNielsValid`), which carry the limb bounds making the field ops
       panic-free, plus ⟪Z⟫ ≠ 0 side facts;
     * conclusions — per-output-field `Bnd` bounds (exactly what the field-op
       chain yields: `fe_sub`/`fe_mul` outputs are reduced ≤ 2⁵², a single
       unreduced `fe_add` of reduced inputs gives 2⁵³, and the stacked add
       ZZ2 + TT2d gives 2⁵⁴) AND the four coordinate equations over 𝔽_p,
       phrased STRICTLY in the input struct-field denotations, e.g.
           ⟪r.Z⟫ = 2·⟪P.Z⟫·⟪N.Z⟫ + ⟪P.T⟫·⟪N.T2d⟫.
       No curve constants, no division, no `OnCurve` here — identifying these
       limb-level equations with the Edwards group law (via `IsNielsOf` and
       the d-characterization of EdDenote.lean) happens in a later file.

   PROOF TECHNIQUE.  Identical to Proofs/InvertSpec.lean: `unfold` the
   transpiled monadic body, then walk it with `let* ⟨x, post…⟩ ← spec by edis`
   — one field operation per line, the named postconditions accumulating in
   the context — and close the four coordinate equations by `rw`+`ring`.
   The `edis` side-condition macro (re-declared here; macros do not travel
   across files) discharges every `Bnd _ (2⁵²/2⁵³/2⁵⁴)` obligation by
   `assumption` or by weakening an existing bound (`Bnd.mono`).  Because the
   base specs `sub_spec`/`neg_spec`/`add_spec` (SubNegSpec.lean/AddSpec.lean)
   take explicit limb variables, this file first re-packages them limb-free
   (`sub_spec'`, `neg_spec'`, `add52_spec`, `add53_spec`) via
   `Fe.exists_limbs`, mirroring `mul_spec'` (InvertSpec.lean).

   Imports: Proofs/EdDenote.lean (point predicates + mk-projection simps)
   and Proofs/Square2Spec.lean (the point-op phase's common field-op stock).
   Imported by: the forthcoming algebra-law packaging file (EdCurve phase).
   ─────────────────────────────────────────────────────────────────────── -/
import Proofs.EdDenote
import Proofs.Square2Spec
open Aeneas Aeneas.Std Result
open curve25519

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace CurveFieldProofs

-- the weakest-precondition layer: spec_mono / spec_ok used below
open Aeneas.Std.WP

/-! ## Limb-free wrappers for the unreduced add, sub, and negate

    The base specs (AddSpec.lean / SubNegSpec.lean) name all five limbs of
    every argument explicitly because their proofs compute limb by limb; the
    `let*` automation cannot invent those variables.  As with `mul_spec'`
    (InvertSpec.lean), we re-state each spec with the limbs repackaged via
    `Fe.exists_limbs`.  `fe_add` performs NO reduction (limbwise `aᵢ+bᵢ`), so
    its output bound genuinely doubles the input bound — we expose the two
    instances this file needs (2⁵²→2⁵³ and 2⁵³→2⁵⁴) of one parametric lemma. -/

/-- Parametric limb-free `fe_add` spec.

    Rust: `impl Add<&FieldElement51> for &FieldElement51`, u64/field.rs:68-72
    (limbwise sum, no carry, no reduction) — verified in Proofs/AddSpec.lean.

    MATH:  c ≤ 2⁶³, Bnd(a,c), Bnd(b,c)  ==>  fe_add a b = ok r  with
           Bnd(r, 2c)  and  ⟪r⟫ = ⟪a⟫ + ⟪b⟫.
    The hypothesis c ≤ 2⁶³ makes every limbwise sum aᵢ + bᵢ < 2c ≤ 2⁶⁴ —
    exactly the u64 no-overflow side condition of `add_spec`, i.e. the
    panic-freedom of the unreduced add.  The value clause is `add_spec`'s
    exact ℕ equation `feVal r = feVal a + feVal b` pushed through the mod-p
    cast (additions commute with ℕ → 𝔽_p).

    WHY NEEDED: parent of the two fixed-bound instances below; stated
    parametrically so the bound bookkeeping is proved once.
    (`private`: Proofs/EdConvert.lean exports a different `add_spec''` under
    the same name; this one is only consumed in-file, so privacy avoids the
    duplicate-declaration clash without changing any statement.) -/
private theorem add_spec'' (c : ℕ) (hc : c ≤ 2^63) (a b : Fe)
    (hba : Bnd a c) (hbb : Bnd b c) :
    fe_add a b ⦃ r => Bnd r (2*c) ∧ ⟪r⟫ = ⟪a⟫ + ⟪b⟫ ⦄ := by
  -- materialize the limbs of both arguments and their per-limb bounds
  obtain ⟨a0, a1, a2, a3, a4, hA⟩ := Fe.exists_limbs a
  obtain ⟨b0, b1, b2, b3, b4, hB⟩ := Fe.exists_limbs b
  have hA' := (Bnd_eq a a0 a1 a2 a3 a4 c hA).mp hba
  have hB' := (Bnd_eq b b0 b1 b2 b3 b4 c hB).mp hbb
  -- run the base spec; each pairwise sum < 2c ≤ 2⁶⁴ closes by omega
  apply spec_mono (add_spec a b a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 hA hB
    ⟨by omega, by omega, by omega, by omega, by omega⟩)
  rintro r ⟨-, hval, hbnd⟩
  -- bound: the "doubles any common bound" law at c; value: one cast to 𝔽_p
  exact ⟨hbnd c hba hbb, by simp [denote, hval]⟩

/-- `fe_add` on two REDUCED (2⁵²) inputs: output bound 2⁵³.

    MATH:  Bnd(a,2⁵²), Bnd(b,2⁵²)  ==>  fe_add a b = ok r,  Bnd(r,2⁵³),
           ⟪r⟫ = ⟪a⟫ + ⟪b⟫.
    WHY NEEDED: the three "first-generation" adds of the kernels below
    (Y₁+X₁ on the 2⁵²-bounded extended coordinates, ZZ+ZZ and PP+MM on
    2⁵²-bounded mul outputs) all fit this instance. -/
theorem add52_spec (a b : Fe) (hba : Bnd a (2^52)) (hbb : Bnd b (2^52)) :
    fe_add a b ⦃ r => Bnd r (2^53) ∧ ⟪r⟫ = ⟪a⟫ + ⟪b⟫ ⦄ := by
  apply spec_mono (add_spec'' (2^52) (by norm_num) a b hba hbb)
  rintro r ⟨h1, h2⟩
  exact ⟨h1.mono (by norm_num), h2⟩  -- 2·2⁵² = 2⁵³

/-- `fe_add` on two 2⁵³-bounded inputs: output bound 2⁵⁴ (still a legal
    input for every field op — the dalek 2⁵⁴ discipline's outer edge).

    MATH:  Bnd(a,2⁵³), Bnd(b,2⁵³)  ==>  fe_add a b = ok r,  Bnd(r,2⁵⁴),
           ⟪r⟫ = ⟪a⟫ + ⟪b⟫.
    WHY NEEDED: the "second-generation" add ZZ2 + TT2d stacks on top of the
    unreduced ZZ2 (Bnd 2⁵³), so it needs this wider instance. -/
theorem add53_spec (a b : Fe) (hba : Bnd a (2^53)) (hbb : Bnd b (2^53)) :
    fe_add a b ⦃ r => Bnd r (2^54) ∧ ⟪r⟫ = ⟪a⟫ + ⟪b⟫ ⦄ := by
  apply spec_mono (add_spec'' (2^53) (by norm_num) a b hba hbb)
  rintro r ⟨h1, h2⟩
  exact ⟨h1.mono (by norm_num), h2⟩  -- 2·2⁵³ = 2⁵⁴

/-- Limb-free `fe_sub` spec (the "+16p then subtract, then reduce" trick).

    Rust: `impl Sub<&FieldElement51> for &FieldElement51`,
    u64/field.rs:84-101 — verified in Proofs/SubNegSpec.lean.
    MATH:  Bnd(a,2⁵⁴), Bnd(b,2⁵⁴)  ==>  fe_sub a b = ok r,  Bnd(r,2⁵²),
           ⟪r⟫ = ⟪a⟫ − ⟪b⟫.
    WHY NEEDED: the kernels below subtract four times each (Y₁−X₁, PP−MM /
    PM−MP, ZZ2−TT2d); this is `sub_spec` with the limbs repackaged so `let*`
    can apply it. -/
theorem sub_spec' (a b : Fe) (hba : Bnd a (2^54)) (hbb : Bnd b (2^54)) :
    fe_sub a b ⦃ r => Bnd r (2^52) ∧ ⟪r⟫ = ⟪a⟫ - ⟪b⟫ ⦄ := by
  obtain ⟨a0, a1, a2, a3, a4, hA⟩ := Fe.exists_limbs a
  obtain ⟨b0, b1, b2, b3, b4, hB⟩ := Fe.exists_limbs b
  exact sub_spec a b a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 hA hB hba hbb

/-- Limb-free `fe_neg` spec (16p − a, then reduce).

    Rust: `FieldElement51::negate`, u64/field.rs:276-286 — verified in
    Proofs/SubNegSpec.lean.
    MATH:  Bnd(a,2⁵⁴)  ==>  fe_neg a = ok r,  Bnd(r,2⁵²),  ⟪r⟫ = −⟪a⟫.
    WHY NEEDED: `ProjectiveNielsPoint::neg` (below) negates the T2d field. -/
theorem neg_spec' (a : Fe) (hba : Bnd a (2^54)) :
    fe_neg a ⦃ r => Bnd r (2^52) ∧ ⟪r⟫ = -⟪a⟫ ⦄ := by
  obtain ⟨a0, a1, a2, a3, a4, hA⟩ := Fe.exists_limbs a
  exact neg_spec a a0 a1 a2 a3 a4 hA hba

/-- Discharge macro for the `let*` side conditions of this file (the `bnd`
    pattern of InvertSpec.lean, re-declared because macros are local to
    their file): every obligation is a `Bnd _ c` goal, closed either by an
    exact hypothesis (`assumption`) or by weakening a tighter bound from the
    context (`Bnd.mono` + `norm_num` on the ≤ between the two numerals);
    `scalar_tac` mops up any residual linear-arithmetic goal.
    (`name :=` disambiguates the generated syntax-kind declaration from the
    sibling files' `edis` macros so they can all be imported together.) -/
macro (name := edisProjNiels) "edis" : tactic =>
  `(tactic| (first
      | assumption
      | exact Bnd.mono (by assumption) (by norm_num)
      | scalar_tac))

/-! ## 1. Mixed addition:  EdwardsPoint + &ProjectiveNielsPoint → CompletedPoint -/

/-- Rust: `impl Add<&ProjectiveNielsPoint> for &EdwardsPoint`,
    src/backend/serial/curve_models.rs:411-430; transpiled at
    gen/CurveField/Funs.lean (`Shared0EdwardsPoint.Insts.
    CoreOpsArithAddSharedAProjectiveNielsPointCompletedPoint.add`).

    MATH (HWCD08 mixed addition, ℙ¹×ℙ¹ output):  for an extended point P
    (ExtValid: all coords Bnd 2⁵², ⟪Z⟫ ≠ 0, X·Y = Z·T) and a niels cache N
    (ProjNielsValid: Y±X Bnd 2⁵³, Z/T2d Bnd 2⁵², ⟪Z⟫ ≠ 0), the kernel is
    TOTAL (every intermediate field op stays inside the 2⁵⁴ discipline:
    the 20 + … machine-op side conditions are discharged step by step) and
    the completed-point output r satisfies

      Bnd r.X 2⁵²  (PP − MM:    reduced sub output)
      Bnd r.Y 2⁵³  (PP + MM:    one unreduced add of two ≤2⁵² mul outputs)
      Bnd r.Z 2⁵⁴  (ZZ2 + TT2d: add stacked on the unreduced ZZ2 ≤ 2⁵³)
      Bnd r.T 2⁵²  (ZZ2 − TT2d: reduced sub output)

      ⟪r.X⟫ = (⟪P.Y⟫+⟪P.X⟫)·⟪N.Y_plus_X⟫ − (⟪P.Y⟫−⟪P.X⟫)·⟪N.Y_minus_X⟫
      ⟪r.Y⟫ = (⟪P.Y⟫+⟪P.X⟫)·⟪N.Y_plus_X⟫ + (⟪P.Y⟫−⟪P.X⟫)·⟪N.Y_minus_X⟫
      ⟪r.Z⟫ = 2·⟪P.Z⟫·⟪N.Z⟫ + ⟪P.T⟫·⟪N.T2d⟫
      ⟪r.T⟫ = 2·⟪P.Z⟫·⟪N.Z⟫ − ⟪P.T⟫·⟪N.T2d⟫

    — the computation order of the Rust source (PP, MM, TT2d, ZZ, ZZ2 = ZZ+ZZ,
    then X' = PP−MM, Y' = PP+MM, Z' = ZZ2+TT2d, T' = ZZ2−TT2d) verbatim, with
    each intermediate eliminated.  Deliberately NO curve constant, division
    or group-law claim here: combined with `IsNielsOf N Q` (EdDenote.lean)
    the right-hand sides become the HWCD08 addition formulas for P + Q, which
    the algebra-law packaging file exploits.

    WHY NEEDED: this is the workhorse of scalar multiplication — every
    table-lookup addition in the double-and-add ladder goes through it. -/
theorem add_projniels_spec (Pt : EdPoint) (N : ProjNiels)
    (hPt : ExtValid Pt) (hN : ProjNielsValid N) :
    Shared0EdwardsPoint.Insts.CoreOpsArithAddSharedAProjectiveNielsPointCompletedPoint.add
      Pt N ⦃ r =>
      Bnd r.X (2^52) ∧ Bnd r.Y (2^53) ∧ Bnd r.Z (2^54) ∧ Bnd r.T (2^52) ∧
      ⟪r.X⟫ = (⟪Pt.Y⟫ + ⟪Pt.X⟫) * ⟪N.Y_plus_X⟫
                - (⟪Pt.Y⟫ - ⟪Pt.X⟫) * ⟪N.Y_minus_X⟫ ∧
      ⟪r.Y⟫ = (⟪Pt.Y⟫ + ⟪Pt.X⟫) * ⟪N.Y_plus_X⟫
                + (⟪Pt.Y⟫ - ⟪Pt.X⟫) * ⟪N.Y_minus_X⟫ ∧
      ⟪r.Z⟫ = 2 * ⟪Pt.Z⟫ * ⟪N.Z⟫ + ⟪Pt.T⟫ * ⟪N.T2d⟫ ∧
      ⟪r.T⟫ = 2 * ⟪Pt.Z⟫ * ⟪N.Z⟫ - ⟪Pt.T⟫ * ⟪N.T2d⟫ ⦄ := by
  -- unpack the validity predicates into named Bnd facts for `edis`
  obtain ⟨hPX, hPY, hPZ, hPT, _hPZ0, _hPcoh⟩ := hPt
  obtain ⟨hNyp, hNym, hNZ, hNT, _hNZ0⟩ := hN
  -- expose the transpiled 11-step monadic body
  unfold Shared0EdwardsPoint.Insts.CoreOpsArithAddSharedAProjectiveNielsPointCompletedPoint.add
  -- Y₁+X₁ : unreduced add of two reduced coordinates (Bnd 2⁵³);
  -- preconditions are verbatim hypotheses, found by `let*` itself
  let* ⟨ Y_plus_X, Ypx_bnd, Ypx_val ⟩ ← add52_spec
  -- Y₁−X₁ : reduced sub (Bnd 2⁵²)
  let* ⟨ Y_minus_X, Ymx_bnd, Ymx_val ⟩ ← sub_spec' by edis
  -- PP = (Y₁+X₁)·N.Y_plus_X
  let* ⟨ PP, PP_bnd, PP_val ⟩ ← mul_spec' by edis
  -- MM = (Y₁−X₁)·N.Y_minus_X
  let* ⟨ MM, MM_bnd, MM_val ⟩ ← mul_spec' by edis
  -- TT2d = T₁·N.T2d
  let* ⟨ TT2d, TT_bnd, TT_val ⟩ ← mul_spec' by edis
  -- ZZ = Z₁·N.Z
  let* ⟨ ZZ, ZZ_bnd, ZZ_val ⟩ ← mul_spec' by edis
  -- ZZ2 = ZZ + ZZ (unreduced doubling, Bnd 2⁵³)
  let* ⟨ ZZ2, ZZ2_bnd, ZZ2_val ⟩ ← add52_spec by edis
  -- X' = PP − MM
  let* ⟨ rX, rX_bnd, rX_val ⟩ ← sub_spec' by edis
  -- Y' = PP + MM
  let* ⟨ rY, rY_bnd, rY_val ⟩ ← add52_spec by edis
  -- Z' = ZZ2 + TT2d (the stacked add, Bnd 2⁵⁴)
  let* ⟨ rZ, rZ_bnd, rZ_val ⟩ ← add53_spec by edis
  -- T' = ZZ2 − TT2d
  let* ⟨ rT, rT_bnd, rT_val ⟩ ← sub_spec' by edis
  -- `let*` already collapsed the final `ok {…}` constructor's projections;
  -- bounds are the recorded step posts; equations close by rewriting the
  -- chain of step values and (for Z/T) merging ZZ+ZZ into 2·ZZ by ring
  refine ⟨rX_bnd, rY_bnd, rZ_bnd, rT_bnd, ?_, ?_, ?_, ?_⟩
  · rw [rX_val, PP_val, MM_val, Ypx_val, Ymx_val]
  · rw [rY_val, PP_val, MM_val, Ypx_val, Ymx_val]
  · rw [rZ_val, ZZ2_val, ZZ_val, TT_val]; ring
  · rw [rT_val, ZZ2_val, ZZ_val, TT_val]; ring

/-! ## 2. Mixed subtraction:  EdwardsPoint − &ProjectiveNielsPoint → CompletedPoint -/

/-- Rust: `impl Sub<&ProjectiveNielsPoint> for &EdwardsPoint`,
    src/backend/serial/curve_models.rs:433-452; transpiled at
    gen/CurveField/Funs.lean (`…SubSharedAProjectiveNielsPointCompletedPoint.sub`).

    MATH:  same hypotheses and totality as `add_projniels_spec`; the body is
    the addition kernel with the cache's Y_plus_X/Y_minus_X CROSSED
    (PM = (Y₁+X₁)·(Y₂−X₂), MP = (Y₁−X₁)·(Y₂+X₂)) and the Z'/T' roles of
    ZZ2 ± TT2d swapped — algebraically, addition of the NEGATED niels point
    (cf. `projniels_neg_spec` below: negation swaps Y±X and flips T2d):

      Bnd r.X 2⁵²,  Bnd r.Y 2⁵³,  Bnd r.Z 2⁵²,  Bnd r.T 2⁵⁴
      (Z' is now the reduced SUB ZZ2−TT2d and T' the stacked ADD ZZ2+TT2d,
       so the 2⁵²/2⁵⁴ bounds trade places relative to `add_projniels_spec`)

      ⟪r.X⟫ = (⟪P.Y⟫+⟪P.X⟫)·⟪N.Y_minus_X⟫ − (⟪P.Y⟫−⟪P.X⟫)·⟪N.Y_plus_X⟫
      ⟪r.Y⟫ = (⟪P.Y⟫+⟪P.X⟫)·⟪N.Y_minus_X⟫ + (⟪P.Y⟫−⟪P.X⟫)·⟪N.Y_plus_X⟫
      ⟪r.Z⟫ = 2·⟪P.Z⟫·⟪N.Z⟫ − ⟪P.T⟫·⟪N.T2d⟫
      ⟪r.T⟫ = 2·⟪P.Z⟫·⟪N.Z⟫ + ⟪P.T⟫·⟪N.T2d⟫

    WHY NEEDED: the signed-digit (NAF) scalar-multiplication ladder
    subtracts table entries as often as it adds them. -/
theorem sub_projniels_spec (Pt : EdPoint) (N : ProjNiels)
    (hPt : ExtValid Pt) (hN : ProjNielsValid N) :
    Shared0EdwardsPoint.Insts.CoreOpsArithSubSharedAProjectiveNielsPointCompletedPoint.sub
      Pt N ⦃ r =>
      Bnd r.X (2^52) ∧ Bnd r.Y (2^53) ∧ Bnd r.Z (2^52) ∧ Bnd r.T (2^54) ∧
      ⟪r.X⟫ = (⟪Pt.Y⟫ + ⟪Pt.X⟫) * ⟪N.Y_minus_X⟫
                - (⟪Pt.Y⟫ - ⟪Pt.X⟫) * ⟪N.Y_plus_X⟫ ∧
      ⟪r.Y⟫ = (⟪Pt.Y⟫ + ⟪Pt.X⟫) * ⟪N.Y_minus_X⟫
                + (⟪Pt.Y⟫ - ⟪Pt.X⟫) * ⟪N.Y_plus_X⟫ ∧
      ⟪r.Z⟫ = 2 * ⟪Pt.Z⟫ * ⟪N.Z⟫ - ⟪Pt.T⟫ * ⟪N.T2d⟫ ∧
      ⟪r.T⟫ = 2 * ⟪Pt.Z⟫ * ⟪N.Z⟫ + ⟪Pt.T⟫ * ⟪N.T2d⟫ ⦄ := by
  obtain ⟨hPX, hPY, hPZ, hPT, _hPZ0, _hPcoh⟩ := hPt
  obtain ⟨hNyp, hNym, hNZ, hNT, _hNZ0⟩ := hN
  unfold Shared0EdwardsPoint.Insts.CoreOpsArithSubSharedAProjectiveNielsPointCompletedPoint.sub
  -- Y₁+X₁, Y₁−X₁ — same prologue as the addition kernel
  let* ⟨ Y_plus_X, Ypx_bnd, Ypx_val ⟩ ← add52_spec
  let* ⟨ Y_minus_X, Ymx_bnd, Ymx_val ⟩ ← sub_spec' by edis
  -- PM = (Y₁+X₁)·N.Y_minus_X   (crossed relative to `add`)
  let* ⟨ PM, PM_bnd, PM_val ⟩ ← mul_spec' by edis
  -- MP = (Y₁−X₁)·N.Y_plus_X
  let* ⟨ MP, MP_bnd, MP_val ⟩ ← mul_spec' by edis
  -- TT2d = T₁·N.T2d,  ZZ = Z₁·N.Z,  ZZ2 = ZZ+ZZ
  let* ⟨ TT2d, TT_bnd, TT_val ⟩ ← mul_spec' by edis
  let* ⟨ ZZ, ZZ_bnd, ZZ_val ⟩ ← mul_spec' by edis
  let* ⟨ ZZ2, ZZ2_bnd, ZZ2_val ⟩ ← add52_spec by edis
  -- X' = PM − MP,  Y' = PM + MP
  let* ⟨ rX, rX_bnd, rX_val ⟩ ← sub_spec' by edis
  let* ⟨ rY, rY_bnd, rY_val ⟩ ← add52_spec by edis
  -- Z' = ZZ2 − TT2d,  T' = ZZ2 + TT2d  (roles swapped relative to `add`)
  let* ⟨ rZ, rZ_bnd, rZ_val ⟩ ← sub_spec' by edis
  let* ⟨ rT, rT_bnd, rT_val ⟩ ← add53_spec by edis
  refine ⟨rX_bnd, rY_bnd, rZ_bnd, rT_bnd, ?_, ?_, ?_, ?_⟩
  · rw [rX_val, PM_val, MP_val, Ypx_val, Ymx_val]
  · rw [rY_val, PM_val, MP_val, Ypx_val, Ymx_val]
  · rw [rZ_val, ZZ2_val, ZZ_val, TT_val]; ring
  · rw [rT_val, ZZ2_val, ZZ_val, TT_val]; ring

/-! ## 3. Negation of a projective-niels cache point -/

/-- Rust: `impl Neg for &ProjectiveNielsPoint`,
    src/backend/serial/curve_models.rs:500-511; transpiled at
    gen/CurveField/Funs.lean (`Shared0ProjectiveNielsPoint.Insts.
    CoreOpsArithNegProjectiveNielsPoint.neg`).

    MATH:  negating an Edwards point (x,y) ↦ (−x,y) sends the cache
    (Y+X, Y−X, Z, T·2d) to (Y−X, Y+X, Z, −T·2d): the two sum/difference
    fields SWAP, Z is untouched, and T2d is negated through the (total,
    `neg_spec'`) field negation.  Hence for ProjNielsValid N:

      neg N = ok r,  ProjNielsValid r   (swap preserves the 2⁵³/2⁵³ bounds,
        ⟪r.Z⟫ = ⟪N.Z⟫ ≠ 0, and fe_neg outputs a reduced 2⁵² T2d), and

      ⟪r.Y_plus_X⟫ = ⟪N.Y_minus_X⟫,   ⟪r.Y_minus_X⟫ = ⟪N.Y_plus_X⟫,
      ⟪r.Z⟫ = ⟪N.Z⟫,                  ⟪r.T2d⟫ = −⟪N.T2d⟫.

    (Field-wise relational form, matching the statement policy: combined
    with `IsNielsOf N Q` these four equations say exactly `IsNielsOf r (−Q)`
    — e.g. 121666·⟪r.T2d⟫ = −121666·⟪N.T2d⟫ = 243330·⟪Q.T⟫ = −243330·(−⟪Q.T⟫)
    — which the packaging file derives.)

    WHY NEEDED: the NAF ladder materializes negative table digits through
    this kernel; it also explains `sub_projniels_spec` as
    "add the negation". -/
theorem projniels_neg_spec (N : ProjNiels) (hN : ProjNielsValid N) :
    Shared0ProjectiveNielsPoint.Insts.CoreOpsArithNegProjectiveNielsPoint.neg
      N ⦃ r =>
      ProjNielsValid r ∧
      ⟪r.Y_plus_X⟫ = ⟪N.Y_minus_X⟫ ∧ ⟪r.Y_minus_X⟫ = ⟪N.Y_plus_X⟫ ∧
      ⟪r.Z⟫ = ⟪N.Z⟫ ∧ ⟪r.T2d⟫ = -⟪N.T2d⟫ ⦄ := by
  obtain ⟨hNyp, hNym, hNZ, hNT, hNZ0⟩ := hN
  -- expose the body; the inner `…NegFieldElement51.neg` is a direct call to
  -- `FieldElement51::negate` (= fe_neg), so unfold both layers
  unfold Shared0ProjectiveNielsPoint.Insts.CoreOpsArithNegProjectiveNielsPoint.neg
    Shared0FieldElement51.Insts.CoreOpsArithNegFieldElement51.neg
  -- t2d = −N.T2d (total: Bnd 2⁵² ≤ 2⁵⁴; output reduced to 2⁵²)
  let* ⟨ t2d, t2d_bnd, t2d_val ⟩ ← neg_spec' by edis
  -- `let*` collapsed the `{ N with … }` constructor's projections and already
  -- closed the three definitional field equations (Y±X swap, Z untouched);
  -- remaining: validity (swapped bounds + Z ≠ 0 + reduced new T2d) and the
  -- T2d value clause (= neg's post)
  exact ⟨⟨hNym, hNyp, hNZ, t2d_bnd, hNZ0⟩, t2d_val⟩

end CurveFieldProofs
