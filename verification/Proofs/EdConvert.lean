/- ───────────────────────────────────────────────────────────────────────────
   Proofs/EdConvert.lean — coordinate-level specs for the REPRESENTATION
   CONVERSIONS between the four point models of curve25519/solana-ed25519.

   CONTEXT.  The Rust crate keeps Edwards points in four internal models
   (see the header of Proofs/EdDenote.lean): extended ℙ³ (`EdwardsPoint`,
   x = X/Z, y = Y/Z, Segre coherence X·Y = Z·T), projective ℙ²
   (`ProjectivePoint`, x = X/Z, y = Y/Z), completed ℙ¹×ℙ¹
   (`CompletedPoint`, x = X/Z, y = Y/T) and the readily-addable niels
   caches (`ProjectiveNielsPoint` = (Y+X, Y−X, Z, T·2d),
   `AffineNielsPoint`).  The add/double kernels produce COMPLETED points;
   the conversion methods specified here move the result back into the
   model the next operation wants — each one is a handful of field
   mul/square/add/sub calls and NOTHING else (no division ever happens at
   runtime; the affine value is preserved because numerator and denominator
   are multiplied by the same nonzero factor).

   THIS FILE proves one spec per conversion, coordinate-level ONLY:

     * `proj_as_extended_spec`           — ProjectivePoint.as_extended
           (X:Y:Z) ↦ (XZ : YZ : Z² : XY)        [curve_models.rs:338-345]
     * `compl_as_projective_spec`        — CompletedPoint.as_projective
           ((X:Z),(Y:T)) ↦ (XT : YZ : ZT)       [curve_models.rs:353-359]
     * `compl_as_extended_spec`          — CompletedPoint.as_extended
           ((X:Z),(Y:T)) ↦ (XT : YZ : ZT : XY)  [curve_models.rs:365-372]
     * `edwards_as_projective_niels_spec`— EdwardsPoint.as_projective_niels
           (X:Y:Z:T) ↦ (Y+X, Y−X, Z, T·2d)      [edwards.rs:528-535]
     * `edwards_neg_spec`                — Neg for &EdwardsPoint
           (X:Y:Z:T) ↦ (−X : Y : Z : −T)        [edwards.rs:844-851]

   Each spec asserts, under the input validity predicate of EdDenote:
   TOTALITY (the triple — every limb stays inside the dalek 2⁵²/2⁵⁴
   discipline, so no u64/u128 overflow, no panic), the output VALIDITY
   predicate (limb bounds + the Z ≠ 0 obligation that the Rust code never
   states + Segre coherence where applicable), the per-field COORDINATE
   EQUATIONS over 𝔽_p strictly in terms of the input struct-field
   denotations (e.g. ⟪r.X⟫ = ⟪p.X⟫·⟪p.Z⟫ — no curve constants, no
   division), and the resulting DENOTATION identities (edX/edY/projX/
   projY/complX/complY agree across the conversion, resp. `IsNielsOf`).
   The algebra-law packaging (group laws, OnCurve preservation) happens in
   a later file (EdMain), which composes exactly these posts.

   FUTURE WORK (deliberately skipped here):
     * `EdwardsPoint.as_affine_niels` (edwards.rs:551-561) and
       `to_affine`-style code — both run `invert` (a 254-squaring Fermat
       chain); their specs belong next to the scalar-mul layer and need
       `invert_spec` composition with the validity predicates.

   PROOF TECHNIQUE.  Identical to Proofs/InvertSpec.lean: unfold the
   transpiled body, walk every field-op bind with `let* ⟨x, posts⟩ ← spec`
   (the Aeneas step machinery), discharging each 2⁵⁴-bound side condition
   with the `edis` macro below, then close the terminal `ok {…}` with
   `spec_ok` and prove the conjunction — bound goals by `Bnd.mono`/
   `norm_num`, value goals by rewriting the step posts and `ring`, and the
   division identities by cross-multiplying with `fp_div_eq_div_iff`
   (EdDenote) over the nonzero denominators.

   Imports: Proofs/EdDenote.lean (validity predicates, denotations, the
   EDWARDS_D2 characterization, division helpers) and Proofs/Square2Spec
   (square2_spec' — not used by the conversions themselves, but imported
   here so this file sits at the same layer as the doubling specs that
   need it, keeping the downstream import graph linear).
   Imported by: the forthcoming point-operation files (EdMain).
   ─────────────────────────────────────────────────────────────────────── -/
import Proofs.EdDenote
import Proofs.Square2Spec
open Aeneas Aeneas.Std Result
open Aeneas.Std.WP
open curve25519

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace CurveFieldProofs

/-! ## Step-friendly wrappers for the remaining field ops

    `mul_spec'`/`square_spec'`/`pow2k_spec'` (InvertSpec.lean) and
    `square2_spec'` (Square2Spec.lean) are already `@[step]`-registered.
    The point bodies additionally call `fe_add`, `fe_sub` and the
    borrowed-`Neg` wrapper; their base specs (AddSpec.lean, SubNegSpec.lean)
    take explicit limb lists, which the step machinery cannot invent, so —
    exactly as in InvertSpec — we re-state them with the limbs repackaged
    via `Fe.exists_limbs` and register the wrappers with `@[step]`. -/

/-- Step-friendly `fe_add` spec at the REDUCED input level.

    Rust: `impl Add<&FieldElement51> for &FieldElement51`, u64/field.rs:58-73
    (limbwise `a[i] + b[i]`, NO carry, NO reduction — Proofs/AddSpec.lean).

    MATH:  Bnd(a,2⁵²) and Bnd(b,2⁵²)  ==>  fe_add a b = ok r  with
           Bnd(r, 2⁵³)  and  ⟪r⟫ = ⟪a⟫ + ⟪b⟫  in 𝔽_p.

    The 2⁵² → 2⁵³ instantiation is the one the point code lives on: every
    `Y + X` in a niels-cache construction adds two REDUCED coordinates, and
    the doubled bound 2⁵³ < 2⁵⁴ keeps the sum a legal input for any
    subsequent mul/sub.  Derived from `add_spec` (AddSpec.lean): its
    pairwise-overflow hypothesis holds since a_i + b_i < 2⁵² + 2⁵² = 2⁵³
    < 2⁶⁴; its generic bound law `∀ c, Bnd a c → Bnd b c → Bnd r (2c)` is
    instantiated at c = 2⁵²; its EXACT ℕ value equation
    `feVal r = feVal a + feVal b` is cast into 𝔽_p by `push_cast`.

    WHY NEEDED: `as_projective_niels` below computes Y_plus_X with this
    unreduced add; the addition/doubling kernels of the next file do too. -/
@[step]
theorem add_spec'' (a b : Fe) (hba : Bnd a (2^52)) (hbb : Bnd b (2^52)) :
    fe_add a b ⦃ r => Bnd r (2^53) ∧ ⟪r⟫ = ⟪a⟫ + ⟪b⟫ ⦄ := by
  -- materialize the limbs of both inputs and restate the bounds limbwise
  obtain ⟨a0, a1, a2, a3, a4, ha⟩ := Fe.exists_limbs a
  obtain ⟨b0, b1, b2, b3, b4, hb⟩ := Fe.exists_limbs b
  have hba' := hba
  have hbb' := hbb
  rw [Bnd_eq a a0 a1 a2 a3 a4 _ ha] at hba'
  rw [Bnd_eq b b0 b1 b2 b3 b4 _ hb] at hbb'
  -- run the base spec; the 5 pairwise sums are < 2⁵³ < 2⁶⁴ (omega)
  apply spec_mono (add_spec a b a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 ha hb
    ⟨by omega, by omega, by omega, by omega, by omega⟩)
  rintro r ⟨-, hval, hbnd⟩
  constructor
  · -- bound: the generic law at c = 2⁵² gives 2·2⁵² = 2⁵³
    exact (hbnd _ hba hbb).mono (by norm_num)
  · -- value: cast the exact ℕ equation feVal r = feVal a + feVal b to 𝔽_p
    simp only [denote]
    rw [hval]
    push_cast
    ring

/-- Step-friendly `fe_sub` spec (limbs hidden, `@[step]`-registered).

    Rust: `impl Sub<&FieldElement51> for &FieldElement51`,
    u64/field.rs:84-101 (adds the constant 16p limbwise before subtracting
    so u64 subtraction cannot underflow, then reduces —
    Proofs/SubNegSpec.lean).

    MATH:  Bnd(a,2⁵⁴) and Bnd(b,2⁵⁴)  ==>  fe_sub a b = ok r  with
           Bnd(r, 2⁵²)  and  ⟪r⟫ = ⟪a⟫ − ⟪b⟫  in 𝔽_p.

    WHY NEEDED: `Y − X` in the niels-cache construction below; the
    addition/doubling kernels of the next file subtract throughout. -/
@[step]
theorem sub_spec'' (a b : Fe) (hba : Bnd a (2^54)) (hbb : Bnd b (2^54)) :
    fe_sub a b ⦃ r => Bnd r (2^52) ∧ ⟪r⟫ = ⟪a⟫ - ⟪b⟫ ⦄ := by
  obtain ⟨a0, a1, a2, a3, a4, ha⟩ := Fe.exists_limbs a
  obtain ⟨b0, b1, b2, b3, b4, hb⟩ := Fe.exists_limbs b
  exact sub_spec a b a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 ha hb hba hbb

/-- Step-friendly spec for the borrowed-`Neg` wrapper.

    Rust: `impl Neg for &FieldElement51 { fn neg }`, u64/field.rs:218-222 —
    literally `self.negate()`; transpiled at gen/CurveField/Funs.lean:1732
    as a one-line `do`-wrapper around `FieldElement51.negate`
    (= `fe_neg`, verified in Proofs/SubNegSpec.lean).

    MATH:  Bnd(a,2⁵⁴)  ==>  neg a = ok r  with  Bnd(r, 2⁵²)  and
           ⟪r⟫ = −⟪a⟫  in 𝔽_p.

    Stated about the WRAPPER (the name the point bodies actually call) so
    the step machinery matches it syntactically.
    WHY NEEDED: `EdwardsPoint::neg` below negates X and T through it. -/
@[step]
theorem neg_spec'' (a : Fe) (hba : Bnd a (2^54)) :
    Shared0FieldElement51.Insts.CoreOpsArithNegFieldElement51.neg a
      ⦃ r => Bnd r (2^52) ∧ ⟪r⟫ = -⟪a⟫ ⦄ := by
  -- the wrapper body is exactly `negate self`
  unfold Shared0FieldElement51.Insts.CoreOpsArithNegFieldElement51.neg
  obtain ⟨a0, a1, a2, a3, a4, ha⟩ := Fe.exists_limbs a
  exact neg_spec a a0 a1 a2 a3 a4 ha hba

/-- Discharge macro for the step side conditions of this file (local copy of
    InvertSpec's `bnd` — tactic macros do not travel across files): every
    field-op step demands `Bnd · (2⁵⁴)` (or 2⁵² for `add_spec''`) on its
    inputs while the context holds the tighter validity bounds (2⁵²/2⁵³
    from the predicates, 2⁵¹+2¹³ from previous steps); close such goals by
    direct assumption, by `scalar_tac`, or by weakening any `Bnd`
    hypothesis with `Bnd.mono` + `norm_num`.
    (`name :=` disambiguates the generated syntax-kind declaration from the
    sibling files' `edis` macros so they can all be imported together.) -/
macro (name := edisConvert) "edis" : tactic =>
  `(tactic| (first
      | assumption
      | scalar_tac
      | exact Bnd.mono (by assumption) (by norm_num)))

/-! ## 1. ProjectivePoint → EdwardsPoint -/

/-- Rust: `ProjectivePoint::as_extended`, curve_models.rs:338-345 —
    "Convert this point from the ℙ² model to the ℙ³ model.  This costs
    3M + 1S."; transpiled at gen/CurveField/Funs.lean:1360.

    CODE:  X' = X·Z,  Y' = Y·Z,  Z' = Z²,  T' = X·Y.

    MATH:  ProjValid p  ==>  as_extended p = ok r  with
      * ExtValid r — all four outputs are mul/square outputs (bound
        2⁵¹+2¹³ ≤ 2⁵²); ⟪r.Z⟫ = ⟪p.Z⟫² ≠ 0 since ⟪p.Z⟫ ≠ 0; Segre holds
        BY CONSTRUCTION: (XZ)·(YZ) = (Z²)·(XY) — pure `ring`;
      * the four coordinate equations
            ⟪r.X⟫ = ⟪p.X⟫·⟪p.Z⟫,  ⟪r.Y⟫ = ⟪p.Y⟫·⟪p.Z⟫,
            ⟪r.Z⟫ = ⟪p.Z⟫·⟪p.Z⟫,  ⟪r.T⟫ = ⟪p.X⟫·⟪p.Y⟫;
      * the affine point is UNCHANGED:  edX r = projX p, edY r = projY p
        (numerator and denominator both gained the factor ⟪p.Z⟫ ≠ 0:
        (XZ)/(Z²) = X/Z, cross-multiplied via `fp_div_eq_div_iff`).

    WHY NEEDED: `double_and_add`-style chains re-extend the running
    projective point before each extended-coordinates addition. -/
theorem proj_as_extended_spec (p : ProjPoint) (hp : ProjValid p) :
    backend.serial.curve_models.ProjectivePoint.as_extended p ⦃ r =>
      ExtValid r ∧
      ⟪r.X⟫ = ⟪p.X⟫ * ⟪p.Z⟫ ∧ ⟪r.Y⟫ = ⟪p.Y⟫ * ⟪p.Z⟫ ∧
      ⟪r.Z⟫ = ⟪p.Z⟫ * ⟪p.Z⟫ ∧ ⟪r.T⟫ = ⟪p.X⟫ * ⟪p.Y⟫ ∧
      edX r = projX p ∧ edY r = projY p ⦄ := by
  obtain ⟨hX, hY, hZ, hZ0⟩ := hp
  -- expose the 4-step transpiled body
  unfold backend.serial.curve_models.ProjectivePoint.as_extended
  -- fe  ← mul X Z   with  ⟪fe⟫  = ⟪p.X⟫·⟪p.Z⟫
  let* ⟨ fe, fe_post1, fe_post2 ⟩ ← mul_spec' by edis
  -- fe1 ← mul Y Z   with  ⟪fe1⟫ = ⟪p.Y⟫·⟪p.Z⟫
  let* ⟨ fe1, fe1_post1, fe1_post2 ⟩ ← mul_spec' by edis
  -- fe2 ← square Z  with  ⟪fe2⟫ = ⟪p.Z⟫·⟪p.Z⟫
  let* ⟨ fe2, fe2_post1, fe2_post2 ⟩ ← square_spec' by edis
  -- fe3 ← mul X Y   with  ⟪fe3⟫ = ⟪p.X⟫·⟪p.Y⟫
  let* ⟨ fe3, fe3_post1, fe3_post2 ⟩ ← mul_spec' by edis
  -- the terminal `ok {X := fe, Y := fe1, Z := fe2, T := fe3}` was already
  -- consumed by the step machinery (projections collapsed); unfold the
  -- predicate and the four denotations to expose the conjunction
  simp only [ExtValid, edX, edY, projX, projY]
  -- the new denominator ⟪fe2⟫ = ⟪p.Z⟫² is nonzero
  have hrZ : ⟪fe2⟫ ≠ 0 := by
    rw [fe2_post2]; exact mul_ne_zero hZ0 hZ0
  refine ⟨⟨fe_post1.mono (by norm_num), fe1_post1.mono (by norm_num),
           fe2_post1.mono (by norm_num), fe3_post1.mono (by norm_num),
           hrZ, ?_⟩,
          fe_post2, fe1_post2, fe2_post2, fe3_post2, ?_, ?_⟩
  · -- Segre coherence:  (XZ)·(YZ) = (Z²)·(XY)
    rw [fe_post2, fe1_post2, fe2_post2, fe3_post2]; ring
  · -- x preserved:  (XZ)/(Z²) = X/Z  ⟺  (XZ)·Z = X·Z²
    rw [fp_div_eq_div_iff hrZ hZ0, fe_post2, fe2_post2]; ring
  · -- y preserved:  (YZ)/(Z²) = Y/Z  ⟺  (YZ)·Z = Y·Z²
    rw [fp_div_eq_div_iff hrZ hZ0, fe1_post2, fe2_post2]; ring

/-! ## 2. CompletedPoint → ProjectivePoint -/

/-- Rust: `CompletedPoint::as_projective`, curve_models.rs:353-359 —
    "Convert this point from the ℙ¹×ℙ¹ model to the ℙ² model.  This costs
    3M."; transpiled at gen/CurveField/Funs.lean:1379.

    CODE:  X' = X·T,  Y' = Y·Z,  Z' = Z·T.

    MATH:  ComplValid p  ==>  as_projective p = ok r  with
      * ProjValid r — three mul outputs (≤ 2⁵²), and
        ⟪r.Z⟫ = ⟪p.Z⟫·⟪p.T⟫ ≠ 0 because BOTH completed denominators are
        nonzero (`mul_ne_zero`);
      * the coordinate equations  ⟪r.X⟫ = ⟪p.X⟫·⟪p.T⟫,
        ⟪r.Y⟫ = ⟪p.Y⟫·⟪p.Z⟫,  ⟪r.Z⟫ = ⟪p.Z⟫·⟪p.T⟫;
      * the affine point is UNCHANGED:  projX r = complX p  (the x-fraction
        X/Z was multiplied through by T) and  projY r = complY p  (the
        y-fraction Y/T was multiplied through by Z) — the two ℙ¹ lines are
        put over the COMMON denominator Z·T.

    WHY NEEDED: every doubling step of a scalar-mul ladder feeds the
    completed output back as a projective point through this conversion. -/
theorem compl_as_projective_spec (p : ComplPoint) (hp : ComplValid p) :
    backend.serial.curve_models.CompletedPoint.as_projective p ⦃ r =>
      ProjValid r ∧
      ⟪r.X⟫ = ⟪p.X⟫ * ⟪p.T⟫ ∧ ⟪r.Y⟫ = ⟪p.Y⟫ * ⟪p.Z⟫ ∧
      ⟪r.Z⟫ = ⟪p.Z⟫ * ⟪p.T⟫ ∧
      projX r = complX p ∧ projY r = complY p ⦄ := by
  obtain ⟨hX, hY, hZ, hT, hZ0, hT0⟩ := hp
  -- expose the 3-step transpiled body
  unfold backend.serial.curve_models.CompletedPoint.as_projective
  -- fe  ← mul X T   with  ⟪fe⟫  = ⟪p.X⟫·⟪p.T⟫
  let* ⟨ fe, fe_post1, fe_post2 ⟩ ← mul_spec' by edis
  -- fe1 ← mul Y Z   with  ⟪fe1⟫ = ⟪p.Y⟫·⟪p.Z⟫
  let* ⟨ fe1, fe1_post1, fe1_post2 ⟩ ← mul_spec' by edis
  -- fe2 ← mul Z T   with  ⟪fe2⟫ = ⟪p.Z⟫·⟪p.T⟫
  let* ⟨ fe2, fe2_post1, fe2_post2 ⟩ ← mul_spec' by edis
  -- the terminal `ok {X := fe, Y := fe1, Z := fe2}` was already consumed by
  -- the step machinery (projections collapsed); unfold predicate/denotations
  simp only [ProjValid, projX, projY, complX, complY]
  -- the common denominator ⟪fe2⟫ = ⟪p.Z⟫·⟪p.T⟫ is nonzero
  have hrZ : ⟪fe2⟫ ≠ 0 := by
    rw [fe2_post2]; exact mul_ne_zero hZ0 hT0
  refine ⟨⟨fe_post1.mono (by norm_num), fe1_post1.mono (by norm_num),
           fe2_post1.mono (by norm_num), hrZ⟩,
          fe_post2, fe1_post2, fe2_post2, ?_, ?_⟩
  · -- x preserved:  (XT)/(ZT) = X/Z  ⟺  (XT)·Z = X·(ZT)
    rw [fp_div_eq_div_iff hrZ hZ0, fe_post2, fe2_post2]; ring
  · -- y preserved:  (YZ)/(ZT) = Y/T  ⟺  (YZ)·T = Y·(ZT)
    rw [fp_div_eq_div_iff hrZ hT0, fe1_post2, fe2_post2]; ring

/-! ## 3. CompletedPoint → EdwardsPoint -/

/-- Rust: `CompletedPoint::as_extended`, curve_models.rs:365-372 —
    "Convert this point from the ℙ¹×ℙ¹ model to the ℙ³ model.  This costs
    4M."; transpiled at gen/CurveField/Funs.lean:1397.

    CODE:  X' = X·T,  Y' = Y·Z,  Z' = Z·T,  T' = X·Y.

    MATH:  ComplValid p  ==>  as_extended p = ok r  with
      * ExtValid r — four mul outputs (≤ 2⁵²); ⟪r.Z⟫ = ⟪p.Z⟫·⟪p.T⟫ ≠ 0
        (`mul_ne_zero` on the two completed denominators); Segre BY
        CONSTRUCTION:  (XT)·(YZ) = (ZT)·(XY) — pure `ring` (this is
        exactly why the extended T-cache is computed as X·Y here:
        T'/Z' = (X/Z)·(Y/T) = x·y);
      * the coordinate equations  ⟪r.X⟫ = ⟪p.X⟫·⟪p.T⟫,
        ⟪r.Y⟫ = ⟪p.Y⟫·⟪p.Z⟫,  ⟪r.Z⟫ = ⟪p.Z⟫·⟪p.T⟫,  ⟪r.T⟫ = ⟪p.X⟫·⟪p.Y⟫;
      * the affine point is UNCHANGED:  edX r = complX p,
        edY r = complY p  (same common-denominator argument as
        `compl_as_projective_spec`).

    WHY NEEDED: the result of a point addition (a completed point) is
    re-extended through this conversion whenever the next operation needs
    the T-cache (e.g. another addition or a niels-cache build). -/
theorem compl_as_extended_spec (p : ComplPoint) (hp : ComplValid p) :
    backend.serial.curve_models.CompletedPoint.as_extended p ⦃ r =>
      ExtValid r ∧
      ⟪r.X⟫ = ⟪p.X⟫ * ⟪p.T⟫ ∧ ⟪r.Y⟫ = ⟪p.Y⟫ * ⟪p.Z⟫ ∧
      ⟪r.Z⟫ = ⟪p.Z⟫ * ⟪p.T⟫ ∧ ⟪r.T⟫ = ⟪p.X⟫ * ⟪p.Y⟫ ∧
      edX r = complX p ∧ edY r = complY p ⦄ := by
  obtain ⟨hX, hY, hZ, hT, hZ0, hT0⟩ := hp
  -- expose the 4-step transpiled body
  unfold backend.serial.curve_models.CompletedPoint.as_extended
  -- fe  ← mul X T   with  ⟪fe⟫  = ⟪p.X⟫·⟪p.T⟫
  let* ⟨ fe, fe_post1, fe_post2 ⟩ ← mul_spec' by edis
  -- fe1 ← mul Y Z   with  ⟪fe1⟫ = ⟪p.Y⟫·⟪p.Z⟫
  let* ⟨ fe1, fe1_post1, fe1_post2 ⟩ ← mul_spec' by edis
  -- fe2 ← mul Z T   with  ⟪fe2⟫ = ⟪p.Z⟫·⟪p.T⟫
  let* ⟨ fe2, fe2_post1, fe2_post2 ⟩ ← mul_spec' by edis
  -- fe3 ← mul X Y   with  ⟪fe3⟫ = ⟪p.X⟫·⟪p.Y⟫
  let* ⟨ fe3, fe3_post1, fe3_post2 ⟩ ← mul_spec' by edis
  -- the terminal `ok {X := fe, Y := fe1, Z := fe2, T := fe3}` was already
  -- consumed by the step machinery (projections collapsed); unfold
  -- predicate/denotations
  simp only [ExtValid, edX, edY, complX, complY]
  -- the common denominator ⟪fe2⟫ = ⟪p.Z⟫·⟪p.T⟫ is nonzero
  have hrZ : ⟪fe2⟫ ≠ 0 := by
    rw [fe2_post2]; exact mul_ne_zero hZ0 hT0
  refine ⟨⟨fe_post1.mono (by norm_num), fe1_post1.mono (by norm_num),
           fe2_post1.mono (by norm_num), fe3_post1.mono (by norm_num),
           hrZ, ?_⟩,
          fe_post2, fe1_post2, fe2_post2, fe3_post2, ?_, ?_⟩
  · -- Segre coherence:  (XT)·(YZ) = (ZT)·(XY)
    rw [fe_post2, fe1_post2, fe2_post2, fe3_post2]; ring
  · -- x preserved:  (XT)/(ZT) = X/Z  ⟺  (XT)·Z = X·(ZT)
    rw [fp_div_eq_div_iff hrZ hZ0, fe_post2, fe2_post2]; ring
  · -- y preserved:  (YZ)/(ZT) = Y/T  ⟺  (YZ)·T = Y·(ZT)
    rw [fp_div_eq_div_iff hrZ hT0, fe1_post2, fe2_post2]; ring

/-! ## 4. EdwardsPoint → ProjectiveNielsPoint -/

/-- Rust: `EdwardsPoint::as_projective_niels`, edwards.rs:528-535 —
    "Convert to a ProjectiveNielsPoint"; transpiled at
    gen/CurveField/Funs.lean:3165.

    CODE:  Y_plus_X = Y + X,  Y_minus_X = Y − X,  Z = Z,
           T2d = T · EDWARDS_D2.

    MATH:  ExtValid P  ==>  as_projective_niels P = ok r  with
      * ProjNielsValid r — Y_plus_X is the single UNREDUCED add of two
        reduced coordinates (bound 2⁵³, `add_spec''`), Y_minus_X a reduced
        sub output (2⁵² ≤ 2⁵³), Z is P.Z verbatim (2⁵²), T2d a mul output
        (≤ 2⁵²); ⟪r.Z⟫ = ⟪P.Z⟫ ≠ 0 carries over;
      * IsNielsOf r P — the cache really derives from P (the EXACT shape
        EdDenote fixed):
            ⟪r.Y_plus_X⟫  = ⟪P.Y⟫ + ⟪P.X⟫,
            ⟪r.Y_minus_X⟫ = ⟪P.Y⟫ − ⟪P.X⟫,
            ⟪r.Z⟫         = ⟪P.Z⟫,
            121666·⟪r.T2d⟫ = −243330·⟪P.T⟫
        (the last is the denominator-free characterization of
        ⟪r.T2d⟫ = ⟪P.T⟫·2d: the EDWARDS_D2 step yields the table entry D2
        with 121666·⟪D2⟫ = −243330 (`edwards_d2_spec`, EdDenote) and the
        mul step yields ⟪r.T2d⟫ = ⟪P.T⟫·⟪D2⟫; multiply the latter by
        121666 and substitute).

    WHY NEEDED: every extended-coordinates point addition `P + Q` first
    caches Q in this form; the next file's add/sub specs consume exactly
    `ProjNielsValid` + `IsNielsOf`. -/
theorem edwards_as_projective_niels_spec (P : EdPoint) (hP : ExtValid P) :
    edwards.EdwardsPoint.as_projective_niels P ⦃ r =>
      ProjNielsValid r ∧ IsNielsOf r P ⦄ := by
  obtain ⟨hX, hY, hZ, hT, hZ0, -⟩ := hP
  -- expose the 4-step transpiled body
  unfold edwards.EdwardsPoint.as_projective_niels
  -- fe  ← add Y X            with  ⟪fe⟫  = ⟪P.Y⟫ + ⟪P.X⟫,  Bnd 2⁵³
  -- (no discharge needed: the 2⁵² preconditions are hypotheses verbatim)
  let* ⟨ fe, fe_post1, fe_post2 ⟩ ← add_spec''
  -- fe1 ← sub Y X            with  ⟪fe1⟫ = ⟪P.Y⟫ − ⟪P.X⟫,  Bnd 2⁵²
  let* ⟨ fe1, fe1_post1, fe1_post2 ⟩ ← sub_spec'' by edis
  -- fe2 ← EDWARDS_D2         with  121666·⟪fe2⟫ = −243330  (the 2d table
  -- entry; a closed constant — no preconditions to discharge)
  let* ⟨ fe2, fe2_post1, fe2_post2 ⟩ ← edwards_d2_spec
  -- fe3 ← mul T fe2          with  ⟪fe3⟫ = ⟪P.T⟫·⟪fe2⟫
  let* ⟨ fe3, fe3_post1, fe3_post2 ⟩ ← mul_spec' by edis
  -- the terminal `ok {…}` was already consumed by the step machinery (which
  -- also collapsed the constructor projections, so the ⟪r.Z⟫ = ⟪P.Z⟫
  -- conjunct is already `True`); unfold the two predicates to expose the
  -- conjunction
  simp only [ProjNielsValid, IsNielsOf]
  refine ⟨⟨fe_post1, fe1_post1.mono (by norm_num), hZ,
           fe3_post1.mono (by norm_num), hZ0⟩,
          fe_post2, fe1_post2, trivial, ?_⟩
  -- T2d characterization: 121666·(⟪P.T⟫·⟪fe2⟫) = ⟪P.T⟫·(121666·⟪fe2⟫)
  --                       = ⟪P.T⟫·(−243330) = −243330·⟪P.T⟫
  calc (121666 : Fp) * ⟪fe3⟫
      = ⟪P.T⟫ * ((121666 : Fp) * ⟪fe2⟫) := by rw [fe3_post2]; ring
    _ = -243330 * ⟪P.T⟫ := by rw [fe2_post2]; ring

/-! ## 5. Negation of an EdwardsPoint -/

/-- Rust: `impl Neg for &EdwardsPoint { fn neg }`, edwards.rs:844-851 —
    negate X and T, keep Y and Z; transpiled at
    gen/CurveField/Funs.lean:3371.

    CODE:  r = (−X : Y : Z : −T).

    MATH:  ExtValid P  ==>  neg P = ok r  with
      * ExtValid r — the two negate outputs are reduced (2⁵²,
        `neg_spec''`), Y/Z are P's verbatim; ⟪r.Z⟫ = ⟪P.Z⟫ ≠ 0 carries
        over; Segre is PRESERVED: (−X)·Y = Z·(−T) follows from
        X·Y = Z·T by negating both sides;
      * the coordinate equations  ⟪r.X⟫ = −⟪P.X⟫,  ⟪r.Y⟫ = ⟪P.Y⟫,
        ⟪r.Z⟫ = ⟪P.Z⟫,  ⟪r.T⟫ = −⟪P.T⟫;
      * the denoted affine point is the EDWARDS NEGATIVE:
        edX r = −(edX P)  (−X/Z = −(X/Z), `neg_div`)  and  edY r = edY P
        — on a twisted Edwards curve −(x, y) = (−x, y).

    WHY NEEDED: subtraction `P − Q` is implemented as `P + (−Q)`; the
    group-law layer (EdMain) packages this spec as the implementation of
    `edNeg` (EdCurve.lean). -/
theorem edwards_neg_spec (P : EdPoint) (hP : ExtValid P) :
    Shared0EdwardsPoint.Insts.CoreOpsArithNegEdwardsPoint.neg P ⦃ r =>
      ExtValid r ∧
      ⟪r.X⟫ = -⟪P.X⟫ ∧ ⟪r.Y⟫ = ⟪P.Y⟫ ∧ ⟪r.Z⟫ = ⟪P.Z⟫ ∧ ⟪r.T⟫ = -⟪P.T⟫ ∧
      edX r = -(edX P) ∧ edY r = edY P ⦄ := by
  obtain ⟨hX, hY, hZ, hT, hZ0, hSeg⟩ := hP
  -- expose the 2-step transpiled body
  unfold Shared0EdwardsPoint.Insts.CoreOpsArithNegEdwardsPoint.neg
  -- fe  ← neg X   with  ⟪fe⟫  = −⟪P.X⟫,  Bnd 2⁵²
  let* ⟨ fe, fe_post1, fe_post2 ⟩ ← neg_spec'' by edis
  -- fe1 ← neg T   with  ⟪fe1⟫ = −⟪P.T⟫,  Bnd 2⁵²
  let* ⟨ fe1, fe1_post1, fe1_post2 ⟩ ← neg_spec'' by edis
  -- the terminal `ok { P with X := fe, T := fe1 }` (= ok (mk fe P.Y P.Z fe1))
  -- was already consumed by the step machinery, which also collapsed the
  -- projections: the Y/Z coordinate equations and `edY r = edY P` are
  -- already `True`; unfold the predicate/denotation defs to expose the rest
  simp only [ExtValid, edX, edY]
  refine ⟨⟨fe_post1, hY, hZ, fe1_post1, hZ0, ?_⟩,
          fe_post2, fe1_post2, ?_, trivial⟩
  · -- Segre preserved:  (−X)·Y = −(X·Y) = −(Z·T) = Z·(−T)
    rw [fe_post2, fe1_post2, neg_mul, hSeg, mul_neg]
  · -- x negated:  ⟪fe⟫/⟪P.Z⟫ = (−⟪P.X⟫)/⟪P.Z⟫ = −(⟪P.X⟫/⟪P.Z⟫)
    rw [fe_post2, neg_div]

end CurveFieldProofs
