/- ───────────────────────────────────────────────────────────────────────────
   Proofs/EdMain.lean — TIER-1 MAIN THEOREM: the transpiled curve25519 point
   operations implement the COMPLETE twisted Edwards addition law on the
   curve  −x² + y² = 1 + d·x²·y²  over 𝔽_p, p = 2²⁵⁵ − 19.

   WHAT THIS FILE PROVES.  Proofs/FieldMain.lean established that the
   transpiled `FieldElement51` code implements the field 𝔽_p; the Ed* files
   established, coordinate by coordinate, what every transpiled POINT
   operation computes (EdDouble/EdAddProjNiels/EdAddAffNiels/EdConvert) and
   what the pure MATHEMATICS of the curve says (EdCurve: the curve constant
   d, the Bernstein–Lange completeness theorem, the group-operation laws).
   This file welds the two layers together.  Writing `edPt P` for the affine
   point (edX P, edY P) ∈ 𝔽_p × 𝔽_p denoted by an extended point P and
   `OnCurveExt P` for "edPt P satisfies the curve equation", we prove that
   for valid on-curve inputs each public `EdwardsPoint` operation

     * RUNS (returns `ok` — every limb stays inside the dalek 2⁵²/2⁵⁴
       discipline, no u64/u128 overflow, no panic),
     * PRESERVES the representation invariant (`ExtValid`: limb bounds,
       Z ≢ 0, the Segre coherence X·Y = Z·T) and the curve membership
       (`OnCurveExt` — via the mathematical closure theorem), and
     * DENOTES the mathematical operation:

           identity ↦ edId            neg P ↦ edNeg (edPt P)
           add P Q  ↦ edAdd (edPt P) (edPt Q)
           sub P Q  ↦ edAdd (edPt P) (edNeg (edPt Q))
           double P ↦ edAdd (edPt P) (edPt P)

       where `edAdd` is THE complete twisted Edwards addition law of
       Proofs/EdCurve.lean — one branch-free formula, total on the curve
       because d is not a square (`completeness`).

   The results are packaged as the certificate `IsEdwardsImplementation`
   and THE MAIN THEOREM `edwardsImplementation`, mirroring the
   `IsFieldImplementation`/`fieldImplementation` pair of FieldMain.lean,
   followed by implementation-level corollaries (`impl_add_comm_ed`,
   `impl_add_id_ed`, `impl_add_neg_ed`) deriving the group-ish laws by
   actually RUNNING the transpiled code.

   PROOF ARCHITECTURE (bottom-up):

     1. DENOTATION BRIDGES.  `ext_X_eq`/`ext_Y_eq`/`ext_T_eq` recover the
        projective coordinates from the affine ones (X = x·Z, Y = y·Z,
        T = x·y·Z — the last from the Segre coherence), `ext_oncurve_poly`
        clears the denominators of the curve equation once and for all, and
        `niels_T2d_eq`/`affniels_xy2d_eq` convert the denominator-free
        121666-characterizations of the cached T·2d / 2d·x·y fields into
        honest equations over the canonical curve constant `edD` (cancelling
        the unit 121666 against `edD_char`).

     2. THE CENTRAL ALGEBRA LEMMA `add_law_fractions`.  Every HWCD08 mixed
        addition kernel produces a completed point whose four fields are a
        COMMON NONZERO FACTOR s times the four canonical quantities

            x₁y₂ + x₂y₁,   y₁y₂ + x₁x₂,   1 + d·x₁x₂y₁y₂,   1 − d·x₁x₂y₁y₂.

        Given those factorizations the lemma concludes: both denominators
        are nonzero (Bernstein–Lange `completeness` kills the parenthesized
        factors, s ≠ 0 the rest) and the two quotients are EXACTLY the two
        components of `edAdd (x₁,y₁) (x₂,y₂)`.

     3. KERNEL LAWS.  For each of the four mixed kernels (add/sub against a
        projective or affine niels cache) a triple `*_law` composes the
        coordinate spec with the bridges of step 1 — substituting X = x·Z
        etc. turns each coordinate post into the s-factorization required by
        step 2, with `ring` doing the bookkeeping — and concludes that the
        completed output denotes the edAdd of the inputs (negated second
        argument for the sub kernels, since the crossed cache fields are
        precisely the cache of the negated point).

     4. TOP-LEVEL LAWS.  The public `EdwardsPoint` API is run end to end:
        `add`/`sub` = as_projective_niels ∘ kernel ∘ as_extended (composed
        with `spec_bind`, the re-extension handled by a relaxed-bound
        version of EdConvert's `compl_as_extended_spec`, since the kernel
        outputs carry 2⁵³/2⁵⁴ bounds); `double` consumes EdDouble's already-
        composed Segre products, where the curve equation rewrites the
        doubling denominators y² − x² and 2 − (y² − x²) into 1 ± d·x²y²;
        `neg` and `identity` are direct.  Curve membership of every output
        is `edAdd_closure`/`onCurve_neg`/`onCurve_id` — pure mathematics.

     5. PACKAGING + COROLLARIES, as described above.

   AXIOM HYGIENE: `#print axioms edwardsImplementation` (kept live at the
   bottom of this file) reports exactly [propext, Classical.choice,
   Quot.sound] — Lean's standard axioms; no sorry, no native_decide, no
   custom axiom.  Nothing in gen/ (the transpiled code) is modified.

   Imports: Proofs/EdCurve (mathematics), Proofs/EdDenote (denotations),
   Proofs/EdDouble + EdAddProjNiels + EdAddAffNiels + EdConvert (coordinate
   specs); these pull in FieldMain and the whole field layer transitively.
   Imported by: nothing — this is the root of the point-law development.
   ─────────────────────────────────────────────────────────────────────── -/
import Proofs.EdCurve
import Proofs.EdDenote
import Proofs.EdDouble
import Proofs.EdAddProjNiels
import Proofs.EdAddAffNiels
import Proofs.EdConvert
open Aeneas Aeneas.Std Aeneas.Std.WP Result
open curve25519

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace CurveFieldProofs

/-! ## 0. The denoted affine point and the curve-membership predicate -/

/-- The affine point denoted by an extended (ℙ³) point:
    `edPt P = (edX P, edY P) = (⟪P.X⟫/⟪P.Z⟫, ⟪P.Y⟫/⟪P.Z⟫) ∈ 𝔽_p × 𝔽_p`.

    This is the object the MATHEMATICAL layer (Proofs/EdCurve.lean) speaks
    about: `edAdd`/`edNeg`/`edId` act on such pairs.  Meaningful under
    `ExtValid P` (division by ⟪Z⟫ ≠ 0).  `noncomputable` because 𝔽_p
    division goes through the classical field instance — never executed. -/
noncomputable def edPt (P : EdPoint) : Fp × Fp := (edX P, edY P)

/-- Curve membership of an extended point, stated on its DENOTATION:

    MATH:  OnCurveExt P  :<=>  −(edX P)² + (edY P)² = 1 + d·(edX P)²·(edY P)².

    This is the semantic invariant the Rust `EdwardsPoint` type maintains
    implicitly (every constructor — identity, decompression, the arithmetic
    proved below — establishes it; no run-time check exists).  Deliberately
    NOT part of `ExtValid`: representation validity (limb bounds, Z ≠ 0,
    Segre) and curve membership are independent concerns, threaded as two
    separate hypotheses throughout. -/
def OnCurveExt (P : EdPoint) : Prop := OnCurve (edX P) (edY P)

/-! ## 1. Denotation bridges: projective coordinates from affine ones

    The coordinate specs of the Ed* files speak in the struct-field
    denotations ⟪P.X⟫, ⟪P.Y⟫, ⟪P.Z⟫, ⟪P.T⟫; the mathematics speaks in the
    affine pair (edX P, edY P).  These lemmas translate: every field is the
    corresponding affine coordinate times ⟪P.Z⟫ (T carrying the PRODUCT
    x·y, by the Segre coherence). -/

/-- MATH:  ⟪P.Z⟫ ≠ 0  ==>  ⟪P.X⟫ = edX P · ⟪P.Z⟫   (clear the denominator
    of edX P = ⟪P.X⟫/⟪P.Z⟫).
    WHY NEEDED: the kernel-law proofs substitute this everywhere to turn
    the coordinate posts into polynomials in (edX, edY, ⟪Z⟫). -/
theorem ext_X_eq (P : EdPoint) (hZ0 : ⟪P.Z⟫ ≠ 0) : ⟪P.X⟫ = edX P * ⟪P.Z⟫ := by
  unfold edX
  rw [div_mul_cancel₀ _ hZ0]

/-- MATH:  ⟪P.Z⟫ ≠ 0  ==>  ⟪P.Y⟫ = edY P · ⟪P.Z⟫.  Mirror of `ext_X_eq`. -/
theorem ext_Y_eq (P : EdPoint) (hZ0 : ⟪P.Z⟫ ≠ 0) : ⟪P.Y⟫ = edY P * ⟪P.Z⟫ := by
  unfold edY
  rw [div_mul_cancel₀ _ hZ0]

/-- The T-denotation lemma.

    MATH:  ⟪P.Z⟫ ≠ 0  and  ⟪P.X⟫·⟪P.Y⟫ = ⟪P.Z⟫·⟪P.T⟫  (the Segre/extended
    coherence carried by `ExtValid`)  ==>  ⟪P.T⟫ = edX P · edY P · ⟪P.Z⟫.

    I.e. the cached fourth coordinate T really carries the PRODUCT of the
    affine coordinates (T/Z = x·y) — the property that lets the mixed
    addition kernels charge the d·x₁x₂y₁y₂ term to a single multiplication
    T₁·(T₂·2d).  Proof: substitute X = x·Z, Y = y·Z into Segre and cancel
    one ⟪P.Z⟫ ≠ 0. -/
theorem ext_T_eq (P : EdPoint) (hZ0 : ⟪P.Z⟫ ≠ 0)
    (hSeg : ⟪P.X⟫ * ⟪P.Y⟫ = ⟪P.Z⟫ * ⟪P.T⟫) :
    ⟪P.T⟫ = edX P * edY P * ⟪P.Z⟫ := by
  apply mul_left_cancel₀ hZ0
  rw [← hSeg, ext_X_eq P hZ0, ext_Y_eq P hZ0]
  ring

/-- Quotient form of `ext_T_eq`:  ⟪P.T⟫ / ⟪P.Z⟫ = edX P · edY P.
    WHY NEEDED: the reader-friendly statement of "T caches x·y"; not used
    by the proofs below (they prefer the denominator-free `ext_T_eq`). -/
theorem ext_T_div (P : EdPoint) (hZ0 : ⟪P.Z⟫ ≠ 0)
    (hSeg : ⟪P.X⟫ * ⟪P.Y⟫ = ⟪P.Z⟫ * ⟪P.T⟫) :
    ⟪P.T⟫ / ⟪P.Z⟫ = edX P * edY P := by
  rw [fp_div_eq_iff hZ0, ext_T_eq P hZ0 hSeg]

/-- The curve equation with the denominators cleared ONCE.

    MATH:  for ⟪P.Z⟫ ≠ 0,
      OnCurveExt P  <=>  (−⟪P.X⟫² + ⟪P.Y⟫²)·⟪P.Z⟫² = ⟪P.Z⟫⁴ + d·⟪P.X⟫²·⟪P.Y⟫²

    — the PROJECTIVE (homogeneous-degree-4) form of −x² + y² = 1 + d·x²y²
    under x = X/Z, y = Y/Z.  Both directions are a single `linear_combination`
    over the nonzero scalar ⟪P.Z⟫⁴.
    WHY NEEDED: the limb-level bridge for curve membership — e.g. a future
    `is_valid`/decompression spec checks exactly this polynomial; the law
    proofs below mostly use the affine form directly. -/
theorem ext_oncurve_poly (P : EdPoint) (hZ0 : ⟪P.Z⟫ ≠ 0) :
    OnCurveExt P ↔
      (-(⟪P.X⟫^2) + ⟪P.Y⟫^2) * ⟪P.Z⟫^2 = ⟪P.Z⟫^4 + edD * ⟪P.X⟫^2 * ⟪P.Y⟫^2 := by
  have hX := ext_X_eq P hZ0
  have hY := ext_Y_eq P hZ0
  have hZ4 : ⟪P.Z⟫^4 ≠ 0 := pow_ne_zero 4 hZ0
  unfold OnCurveExt OnCurve
  constructor
  · -- affine ⇒ projective: multiply the affine equation by ⟪P.Z⟫⁴
    intro h
    rw [hX, hY]
    linear_combination ⟪P.Z⟫^4 * h
  · -- projective ⇒ affine: both sides are ⟪P.Z⟫⁴ times the affine sides
    intro h
    rw [hX, hY] at h
    apply mul_left_cancel₀ hZ4
    linear_combination h

/-- The T2d-cache conversion.

    MATH:  IsNielsOf N Q  ==>  ⟪N.T2d⟫ = 2·d·⟪Q.T⟫.

    `IsNielsOf` (Proofs/EdDenote.lean) characterizes the cached field
    denominator-free as 121666·⟪N.T2d⟫ = −243330·⟪Q.T⟫ (so that file needs
    no `edD`); combined with the canonical characterization
    121666·d = −121665 (`edD_char`, Proofs/EdCurve.lean) and the
    invertibility of 121666 (`c121666_ne_zero`) this pins the cache to the
    honest field element 2·d·⟪Q.T⟫.
    WHY NEEDED: lets the projective-niels kernel laws name the d-term of
    the addition formulas through the canonical constant `edD`. -/
theorem niels_T2d_eq {N : ProjNiels} {Q : EdPoint} (hN : IsNielsOf N Q) :
    ⟪N.T2d⟫ = 2 * edD * ⟪Q.T⟫ := by
  obtain ⟨-, -, -, h⟩ := hN
  -- cancel the unit 121666 on both sides
  apply mul_left_cancel₀ c121666_ne_zero
  rw [h]
  -- −243330·T = 121666·(2·d·T) because 121666·d = −121665 (edD_char)
  linear_combination (-2 * ⟪Q.T⟫) * edD_char

/-- The xy2d-cache conversion (affine analogue of `niels_T2d_eq`).

    MATH:  IsAffNielsOf N x y  ==>  ⟪N.xy2d⟫ = 2·d·(x·y).
    Same 121666-cancellation against `edD_char`. -/
theorem affniels_xy2d_eq {N : AffNiels} {x y : Fp} (hN : IsAffNielsOf N x y) :
    ⟪N.xy2d⟫ = 2 * edD * (x * y) := by
  obtain ⟨-, -, h⟩ := hN
  apply mul_left_cancel₀ c121666_ne_zero
  rw [h]
  linear_combination (-2 * (x * y)) * edD_char

/-! ## 2. The central algebra lemma

    Each HWCD08 mixed-addition kernel returns a completed (ℙ¹×ℙ¹) point
    whose four fields share a common nonzero factor s (s = 2·Z₁·Z₂ for the
    projective-niels kernels, s = 2·Z₁ for the affine ones, the second
    input negated for the sub kernels).  Everything that is specific to a
    kernel is establishing those four factorizations; everything they have
    in COMMON — completeness of the denominators and the identification
    with `edAdd` — is this one lemma. -/

/-- CENTRAL ALGEBRA LEMMA.  If the four fields of a completed point are a
    common nonzero factor s times the four canonical addition-law
    quantities of the curve points (x₁,y₁), (x₂,y₂), then the point's two
    denominators are NONZERO and its two quotients are EXACTLY the complete
    twisted Edwards sum `edAdd (x₁,y₁) (x₂,y₂)`.

    MATH:  s ≠ 0, OnCurve x₁ y₁, OnCurve x₂ y₂,
           rX = s·(x₁y₂ + x₂y₁),        rY = s·(y₁y₂ + x₁x₂),
           rZ = s·(1 + d·x₁x₂y₁y₂),     rT = s·(1 − d·x₁x₂y₁y₂)
       ==> rZ ≠ 0 ∧ rT ≠ 0 ∧ rX/rZ = (edAdd (x₁,y₁) (x₂,y₂)).1
                          ∧ rY/rT = (edAdd (x₁,y₁) (x₂,y₂)).2.

    The nonvanishing is the Bernstein–Lange COMPLETENESS theorem
    (Proofs/EdCurve.lean): d is not a square, hence 1 ± d·x₁x₂y₁y₂ ≠ 0 at
    EVERY pair of curve points — no exceptional cases, which is precisely
    why the branch-free Rust code is correct as written.  The quotient
    identities are then division-cancellation of s (cross-multiplication
    + `ring`). -/
theorem add_law_fractions {x1 y1 x2 y2 s rX rY rZ rT : Fp}
    (hs : s ≠ 0) (hc1 : OnCurve x1 y1) (hc2 : OnCurve x2 y2)
    (hX : rX = s * (x1 * y2 + x2 * y1))
    (hY : rY = s * (y1 * y2 + x1 * x2))
    (hZ : rZ = s * (1 + edD * x1 * x2 * y1 * y2))
    (hT : rT = s * (1 - edD * x1 * x2 * y1 * y2)) :
    rZ ≠ 0 ∧ rT ≠ 0 ∧
      rX / rZ = (edAdd (x1, y1) (x2, y2)).1 ∧
      rY / rT = (edAdd (x1, y1) (x2, y2)).2 := by
  -- Bernstein–Lange: both parenthesized denominators are units on the curve
  obtain ⟨hp, hm⟩ := completeness hc1 hc2
  have hZ0 : rZ ≠ 0 := by rw [hZ]; exact mul_ne_zero hs hp
  have hT0 : rT ≠ 0 := by rw [hT]; exact mul_ne_zero hs hm
  refine ⟨hZ0, hT0, ?_, ?_⟩
  · -- x-component: cancel s from numerator and denominator
    show rX / rZ = (x1 * y2 + x2 * y1) / (1 + edD * x1 * x2 * y1 * y2)
    rw [fp_div_eq_div_iff hZ0 hp, hX, hZ]
    ring
  · -- y-component: same cancellation against the "−" denominator
    show rY / rT = (y1 * y2 + x1 * x2) / (1 - edD * x1 * x2 * y1 * y2)
    rw [fp_div_eq_div_iff hT0 hm, hY, hT]
    ring

/-! ## 3. Kernel laws: the four mixed add/sub kernels denote `edAdd`

    Each law upgrades the corresponding coordinate spec (EdAddProjNiels /
    EdAddAffNiels) from "these polynomials in the struct fields" to "the
    completed output DENOTES the Edwards sum", threading the nonzero
    denominators that the conversion back to ℙ³ will need.  The bounds in
    the postconditions are those of the coordinate specs, verbatim. -/

/-- LAW for the projective-niels mixed ADDITION kernel
    (`EdwardsPoint + &ProjectiveNielsPoint → CompletedPoint`,
    curve_models.rs:411-430).

    MATH: for an extended point P₁ and the niels cache N of an extended
    point P₂ — both valid, both ON THE CURVE — the kernel runs and its
    completed output r satisfies, beyond the limb bounds of
    `add_projniels_spec`:
        ⟪r.Z⟫ ≠ 0,  ⟪r.T⟫ ≠ 0   (completeness — the ℙ¹×ℙ¹ point is honest),
        (complX r, complY r) = edAdd (edPt P₁) (edPt P₂).
    Proof: substitute Xᵢ = xᵢZᵢ, Yᵢ = yᵢZᵢ, Tᵢ = xᵢyᵢZᵢ (the §1 bridges)
    into the four coordinate posts; `ring` reshapes them into the common
    factorization s = 2·Z₁·Z₂ required by `add_law_fractions`. -/
theorem add_projniels_law (P1 : EdPoint) (N : ProjNiels) {P2 : EdPoint}
    (hN : IsNielsOf N P2) (h1 : ExtValid P1) (h2 : ExtValid P2)
    (hc1 : OnCurveExt P1) (hc2 : OnCurveExt P2) (hNv : ProjNielsValid N) :
    Shared0EdwardsPoint.Insts.CoreOpsArithAddSharedAProjectiveNielsPointCompletedPoint.add
      P1 N ⦃ r =>
      Bnd r.X (2^52) ∧ Bnd r.Y (2^53) ∧ Bnd r.Z (2^54) ∧ Bnd r.T (2^52) ∧
      ⟪r.Z⟫ ≠ 0 ∧ ⟪r.T⟫ ≠ 0 ∧
      complX r = (edAdd (edPt P1) (edPt P2)).1 ∧
      complY r = (edAdd (edPt P1) (edPt P2)).2 ⦄ := by
  -- run the coordinate-level spec and strengthen its post
  apply spec_mono (add_projniels_spec P1 N h1 hNv)
  rintro r ⟨hbX, hbY, hbZ, hbT, hrX, hrY, hrZ, hrT⟩
  -- the cache fields in terms of P2's coordinates (incl. the d-term)
  have hN2d := niels_T2d_eq hN
  obtain ⟨hNyp, hNym, hNZ, -⟩ := hN
  -- the §1 bridges for both inputs
  obtain ⟨-, -, -, -, hZ1, hSeg1⟩ := h1
  obtain ⟨-, -, -, -, hZ2, hSeg2⟩ := h2
  have hX1 := ext_X_eq P1 hZ1
  have hY1 := ext_Y_eq P1 hZ1
  have hT1 := ext_T_eq P1 hZ1 hSeg1
  have hX2 := ext_X_eq P2 hZ2
  have hY2 := ext_Y_eq P2 hZ2
  have hT2 := ext_T_eq P2 hZ2 hSeg2
  have hc1' : OnCurve (edX P1) (edY P1) := hc1
  have hc2' : OnCurve (edX P2) (edY P2) := hc2
  -- the common factor s = 2·Z₁·Z₂ is a unit
  have hs : (2 : Fp) * ⟪P1.Z⟫ * ⟪P2.Z⟫ ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero' hZ1) hZ2
  -- the four s-factorizations (HWCD08 algebra, certified by `ring`)
  have eX : ⟪r.X⟫ = 2 * ⟪P1.Z⟫ * ⟪P2.Z⟫ *
      (edX P1 * edY P2 + edX P2 * edY P1) := by
    rw [hrX, hNyp, hNym, hX1, hY1, hX2, hY2]; ring
  have eY : ⟪r.Y⟫ = 2 * ⟪P1.Z⟫ * ⟪P2.Z⟫ *
      (edY P1 * edY P2 + edX P1 * edX P2) := by
    rw [hrY, hNyp, hNym, hX1, hY1, hX2, hY2]; ring
  have eZ : ⟪r.Z⟫ = 2 * ⟪P1.Z⟫ * ⟪P2.Z⟫ *
      (1 + edD * edX P1 * edX P2 * edY P1 * edY P2) := by
    rw [hrZ, hNZ, hN2d, hT1, hT2]; ring
  have eT : ⟪r.T⟫ = 2 * ⟪P1.Z⟫ * ⟪P2.Z⟫ *
      (1 - edD * edX P1 * edX P2 * edY P1 * edY P2) := by
    rw [hrT, hNZ, hN2d, hT1, hT2]; ring
  -- the central lemma does the rest
  obtain ⟨hZ0, hT0, hxd, hyd⟩ := add_law_fractions hs hc1' hc2' eX eY eZ eT
  exact ⟨hbX, hbY, hbZ, hbT, hZ0, hT0, hxd, hyd⟩

/-- LAW for the projective-niels mixed SUBTRACTION kernel
    (`EdwardsPoint − &ProjectiveNielsPoint → CompletedPoint`,
    curve_models.rs:433-452).

    MATH: under the same hypotheses as `add_projniels_law`, the sub kernel
    computes  edAdd (edPt P₁) (edNeg (edPt P₂))  — subtraction IS addition
    of the negated point.  The crossed cache fields (Y₂∓X₂ in place of
    Y₂±X₂) and the flipped sign of the T·2d term are exactly the cache of
    (−x₂, y₂): the SAME factorizations as the add law emerge, with the
    central lemma instantiated at (−edX P₂, edY P₂), whose curve membership
    is `onCurve_neg`. -/
theorem sub_projniels_law (P1 : EdPoint) (N : ProjNiels) {P2 : EdPoint}
    (hN : IsNielsOf N P2) (h1 : ExtValid P1) (h2 : ExtValid P2)
    (hc1 : OnCurveExt P1) (hc2 : OnCurveExt P2) (hNv : ProjNielsValid N) :
    Shared0EdwardsPoint.Insts.CoreOpsArithSubSharedAProjectiveNielsPointCompletedPoint.sub
      P1 N ⦃ r =>
      Bnd r.X (2^52) ∧ Bnd r.Y (2^53) ∧ Bnd r.Z (2^52) ∧ Bnd r.T (2^54) ∧
      ⟪r.Z⟫ ≠ 0 ∧ ⟪r.T⟫ ≠ 0 ∧
      complX r = (edAdd (edPt P1) (edNeg (edPt P2))).1 ∧
      complY r = (edAdd (edPt P1) (edNeg (edPt P2))).2 ⦄ := by
  apply spec_mono (sub_projniels_spec P1 N h1 hNv)
  rintro r ⟨hbX, hbY, hbZ, hbT, hrX, hrY, hrZ, hrT⟩
  have hN2d := niels_T2d_eq hN
  obtain ⟨hNyp, hNym, hNZ, -⟩ := hN
  obtain ⟨-, -, -, -, hZ1, hSeg1⟩ := h1
  obtain ⟨-, -, -, -, hZ2, hSeg2⟩ := h2
  have hX1 := ext_X_eq P1 hZ1
  have hY1 := ext_Y_eq P1 hZ1
  have hT1 := ext_T_eq P1 hZ1 hSeg1
  have hX2 := ext_X_eq P2 hZ2
  have hY2 := ext_Y_eq P2 hZ2
  have hT2 := ext_T_eq P2 hZ2 hSeg2
  have hc1' : OnCurve (edX P1) (edY P1) := hc1
  -- the second point of the addition is the NEGATION (−x₂, y₂)
  have hc2' : OnCurve (-(edX P2)) (edY P2) := onCurve_neg hc2
  have hs : (2 : Fp) * ⟪P1.Z⟫ * ⟪P2.Z⟫ ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero' hZ1) hZ2
  -- factorizations at (x₁,y₁), (−x₂,y₂): the crossed products supply the
  -- sign flips, `ring` checks them
  have eX : ⟪r.X⟫ = 2 * ⟪P1.Z⟫ * ⟪P2.Z⟫ *
      (edX P1 * edY P2 + -(edX P2) * edY P1) := by
    rw [hrX, hNyp, hNym, hX1, hY1, hX2, hY2]; ring
  have eY : ⟪r.Y⟫ = 2 * ⟪P1.Z⟫ * ⟪P2.Z⟫ *
      (edY P1 * edY P2 + edX P1 * -(edX P2)) := by
    rw [hrY, hNyp, hNym, hX1, hY1, hX2, hY2]; ring
  have eZ : ⟪r.Z⟫ = 2 * ⟪P1.Z⟫ * ⟪P2.Z⟫ *
      (1 + edD * edX P1 * -(edX P2) * edY P1 * edY P2) := by
    rw [hrZ, hNZ, hN2d, hT1, hT2]; ring
  have eT : ⟪r.T⟫ = 2 * ⟪P1.Z⟫ * ⟪P2.Z⟫ *
      (1 - edD * edX P1 * -(edX P2) * edY P1 * edY P2) := by
    rw [hrT, hNZ, hN2d, hT1, hT2]; ring
  obtain ⟨hZ0, hT0, hxd, hyd⟩ := add_law_fractions hs hc1' hc2' eX eY eZ eT
  exact ⟨hbX, hbY, hbZ, hbT, hZ0, hT0, hxd, hyd⟩

/-- LAW for the affine-niels mixed ADDITION kernel
    (`EdwardsPoint + &AffineNielsPoint → CompletedPoint`,
    curve_models.rs:458-472).

    MATH: for valid on-curve P₁ and the affine cache N of a curve point
    (x₂, y₂) (implicit Z₂ = 1), the kernel's completed output denotes
    edAdd (edPt P₁) (x₂, y₂).  Identical algebra to `add_projniels_law`
    with Z₂ := 1, common factor s = 2·Z₁. -/
theorem add_affniels_law (P1 : EdPoint) (N : AffNiels) {x2 y2 : Fp}
    (hN : IsAffNielsOf N x2 y2) (h1 : ExtValid P1)
    (hc1 : OnCurveExt P1) (hc2 : OnCurve x2 y2) (hNv : AffNielsValid N) :
    Shared0EdwardsPoint.Insts.CoreOpsArithAddSharedAAffineNielsPointCompletedPoint.add
      P1 N ⦃ r =>
      Bnd r.X (2^52) ∧ Bnd r.Y (2^53) ∧ Bnd r.Z (2^54) ∧ Bnd r.T (2^52) ∧
      ⟪r.Z⟫ ≠ 0 ∧ ⟪r.T⟫ ≠ 0 ∧
      complX r = (edAdd (edPt P1) (x2, y2)).1 ∧
      complY r = (edAdd (edPt P1) (x2, y2)).2 ⦄ := by
  apply spec_mono (add_affniels_spec P1 N h1 hNv)
  rintro r ⟨hbX, hbY, hbZ, hbT, hrX, hrY, hrZ, hrT⟩
  have hxy2d := affniels_xy2d_eq hN
  obtain ⟨hNyp, hNym, -⟩ := hN
  obtain ⟨-, -, -, -, hZ1, hSeg1⟩ := h1
  have hX1 := ext_X_eq P1 hZ1
  have hY1 := ext_Y_eq P1 hZ1
  have hT1 := ext_T_eq P1 hZ1 hSeg1
  have hc1' : OnCurve (edX P1) (edY P1) := hc1
  -- common factor s = 2·Z₁ (the affine cache has implicit Z₂ = 1)
  have hs : (2 : Fp) * ⟪P1.Z⟫ ≠ 0 := mul_ne_zero two_ne_zero' hZ1
  have eX : ⟪r.X⟫ = 2 * ⟪P1.Z⟫ * (edX P1 * y2 + x2 * edY P1) := by
    rw [hrX, hNyp, hNym, hX1, hY1]; ring
  have eY : ⟪r.Y⟫ = 2 * ⟪P1.Z⟫ * (edY P1 * y2 + edX P1 * x2) := by
    rw [hrY, hNyp, hNym, hX1, hY1]; ring
  have eZ : ⟪r.Z⟫ = 2 * ⟪P1.Z⟫ * (1 + edD * edX P1 * x2 * edY P1 * y2) := by
    rw [hrZ, hxy2d, hT1]; ring
  have eT : ⟪r.T⟫ = 2 * ⟪P1.Z⟫ * (1 - edD * edX P1 * x2 * edY P1 * y2) := by
    rw [hrT, hxy2d, hT1]; ring
  obtain ⟨hZ0, hT0, hxd, hyd⟩ := add_law_fractions hs hc1' hc2 eX eY eZ eT
  exact ⟨hbX, hbY, hbZ, hbT, hZ0, hT0, hxd, hyd⟩

/-- LAW for the affine-niels mixed SUBTRACTION kernel
    (`EdwardsPoint − &AffineNielsPoint → CompletedPoint`,
    curve_models.rs:479-493).

    MATH: the sub kernel denotes  edAdd (edPt P₁) (−x₂, y₂)  — addition of
    the negated cached point, exactly as in `sub_projniels_law` (crossed
    products + flipped Txy2d sign), at Z₂ = 1. -/
theorem sub_affniels_law (P1 : EdPoint) (N : AffNiels) {x2 y2 : Fp}
    (hN : IsAffNielsOf N x2 y2) (h1 : ExtValid P1)
    (hc1 : OnCurveExt P1) (hc2 : OnCurve x2 y2) (hNv : AffNielsValid N) :
    Shared0EdwardsPoint.Insts.CoreOpsArithSubSharedAAffineNielsPointCompletedPoint.sub
      P1 N ⦃ r =>
      Bnd r.X (2^52) ∧ Bnd r.Y (2^53) ∧ Bnd r.Z (2^52) ∧ Bnd r.T (2^54) ∧
      ⟪r.Z⟫ ≠ 0 ∧ ⟪r.T⟫ ≠ 0 ∧
      complX r = (edAdd (edPt P1) (-x2, y2)).1 ∧
      complY r = (edAdd (edPt P1) (-x2, y2)).2 ⦄ := by
  apply spec_mono (sub_affniels_spec P1 N h1 hNv)
  rintro r ⟨hbX, hbY, hbZ, hbT, hrX, hrY, hrZ, hrT⟩
  have hxy2d := affniels_xy2d_eq hN
  obtain ⟨hNyp, hNym, -⟩ := hN
  obtain ⟨-, -, -, -, hZ1, hSeg1⟩ := h1
  have hX1 := ext_X_eq P1 hZ1
  have hY1 := ext_Y_eq P1 hZ1
  have hT1 := ext_T_eq P1 hZ1 hSeg1
  have hc1' : OnCurve (edX P1) (edY P1) := hc1
  have hc2' : OnCurve (-x2) y2 := onCurve_neg hc2
  have hs : (2 : Fp) * ⟪P1.Z⟫ ≠ 0 := mul_ne_zero two_ne_zero' hZ1
  have eX : ⟪r.X⟫ = 2 * ⟪P1.Z⟫ * (edX P1 * y2 + -x2 * edY P1) := by
    rw [hrX, hNyp, hNym, hX1, hY1]; ring
  have eY : ⟪r.Y⟫ = 2 * ⟪P1.Z⟫ * (edY P1 * y2 + edX P1 * -x2) := by
    rw [hrY, hNyp, hNym, hX1, hY1]; ring
  have eZ : ⟪r.Z⟫ = 2 * ⟪P1.Z⟫ * (1 + edD * edX P1 * -x2 * edY P1 * y2) := by
    rw [hrZ, hxy2d, hT1]; ring
  have eT : ⟪r.T⟫ = 2 * ⟪P1.Z⟫ * (1 - edD * edX P1 * -x2 * edY P1 * y2) := by
    rw [hrT, hxy2d, hT1]; ring
  obtain ⟨hZ0, hT0, hxd, hyd⟩ := add_law_fractions hs hc1' hc2' eX eY eZ eT
  exact ⟨hbX, hbY, hbZ, hbT, hZ0, hT0, hxd, hyd⟩

/-! ## 4. The ℙ¹×ℙ¹ → ℙ³ re-embedding at the kernels' true bounds

    EdConvert's `compl_as_extended_spec` requires `ComplValid` (all fields
    ≤ 2⁵²), but the add/sub kernels output Y at 2⁵³ and one of Z/T at 2⁵⁴
    (the stacked unreduced add).  All four are still legal `fe_mul` inputs
    (≤ 2⁵⁴), so the conversion runs fine — we re-prove its spec at the
    relaxed bounds, walking the 4-multiplication body with `spec_bind`. -/

/-- Relaxed-bound spec for `CompletedPoint::as_extended`
    (curve_models.rs:365-372 — X' = X·T, Y' = Y·Z, Z' = Z·T, T' = X·Y).

    MATH: for any completed point with all fields ≤ 2⁵⁴ and BOTH
    denominators nonzero, the conversion runs and returns an `ExtValid`
    extended point denoting the SAME affine point (numerators and
    denominators are multiplied through by the same nonzero factors;
    Segre holds by construction: (XT)(YZ) = (ZT)(XY)). -/
theorem compl_as_extended_law (p : ComplPoint)
    (hbX : Bnd p.X (2^54)) (hbY : Bnd p.Y (2^54))
    (hbZ : Bnd p.Z (2^54)) (hbT : Bnd p.T (2^54))
    (hZ0 : ⟪p.Z⟫ ≠ 0) (hT0 : ⟪p.T⟫ ≠ 0) :
    backend.serial.curve_models.CompletedPoint.as_extended p ⦃ r =>
      ExtValid r ∧ edX r = complX p ∧ edY r = complY p ⦄ := by
  -- expose the 4-multiplication body and walk it with spec_bind
  unfold backend.serial.curve_models.CompletedPoint.as_extended
  -- fe ← X·T
  apply spec_bind (mul_spec' _ _ hbX hbT)
  rintro fe ⟨fe_b, fe_v⟩
  -- fe1 ← Y·Z
  apply spec_bind (mul_spec' _ _ hbY hbZ)
  rintro fe1 ⟨fe1_b, fe1_v⟩
  -- fe2 ← Z·T  (the new common denominator — a product of two units)
  apply spec_bind (mul_spec' _ _ hbZ hbT)
  rintro fe2 ⟨fe2_b, fe2_v⟩
  -- fe3 ← X·Y  (the new T-cache)
  apply spec_bind (mul_spec' _ _ hbX hbY)
  rintro fe3 ⟨fe3_b, fe3_v⟩
  -- terminal `ok {X := fe, Y := fe1, Z := fe2, T := fe3}`: collapse the
  -- triple with `spec_ok` and unfold the predicate/denotations (the
  -- constructor projections reduce definitionally during the unfolding)
  simp only [spec_ok, ExtValid, edX, edY, complX, complY]
  have hrZ : ⟪fe2⟫ ≠ 0 := by
    rw [fe2_v]; exact mul_ne_zero hZ0 hT0
  refine ⟨⟨fe_b.mono (by norm_num), fe1_b.mono (by norm_num),
           fe2_b.mono (by norm_num), fe3_b.mono (by norm_num), hrZ, ?_⟩,
          ?_, ?_⟩
  · -- Segre by construction: (XT)·(YZ) = (ZT)·(XY)
    rw [fe_v, fe1_v, fe2_v, fe3_v]; ring
  · -- x preserved: (XT)/(ZT) = X/Z  ⟺  (XT)·Z = X·(ZT)
    rw [fp_div_eq_div_iff hrZ hZ0, fe_v, fe2_v]; ring
  · -- y preserved: (YZ)/(ZT) = Y/T  ⟺  (YZ)·T = Y·(ZT)
    rw [fp_div_eq_div_iff hrZ hT0, fe1_v, fe2_v]; ring

/-! ## 5. Top-level laws: the public `EdwardsPoint` API -/

/-- THE ADDITION LAW for the public operator
    `impl Add<&EdwardsPoint> for &EdwardsPoint` (edwards.rs:785-787,
    transpiled at gen/CurveField/Funs.lean:3271-3283), whose body is

        let pnp ← as_projective_niels(Q);          -- cache Q
        let cp  ← P + pnp;                          -- HWCD08 mixed addition
        cp.as_extended()                            -- back to ℙ³

    MATH:  ExtValid P, ExtValid Q, OnCurveExt P, OnCurveExt Q  ==>
        add P Q = ok R  with  ExtValid R,  OnCurveExt R,  and
        edPt R = edAdd (edPt P) (edPt Q)
    — the transpiled addition IS the complete twisted Edwards addition law,
    with the representation invariant and curve membership preserved
    (the latter by the mathematical closure theorem `edAdd_closure`). -/
theorem edwards_add_law (P Q : EdPoint)
    (hP : ExtValid P) (hQ : ExtValid Q)
    (hcP : OnCurveExt P) (hcQ : OnCurveExt Q) :
    Shared0EdwardsPoint.Insts.CoreOpsArithAddSharedAEdwardsPointEdwardsPoint.add
      P Q ⦃ R =>
      ExtValid R ∧ OnCurveExt R ∧ edPt R = edAdd (edPt P) (edPt Q) ⦄ := by
  unfold Shared0EdwardsPoint.Insts.CoreOpsArithAddSharedAEdwardsPointEdwardsPoint.add
  -- pnp ← as_projective_niels Q   (EdConvert: valid cache, IsNielsOf pnp Q)
  apply spec_bind (edwards_as_projective_niels_spec Q hQ)
  rintro pnp ⟨hpnpv, hpnpn⟩
  -- cp ← P + pnp   (the kernel law: completed point denoting the edAdd)
  apply spec_bind (add_projniels_law P pnp hpnpn hP hQ hcP hcQ hpnpv)
  rintro cp ⟨cbX, cbY, cbZ, cbT, cZ0, cT0, cx, cy⟩
  -- tail: as_extended cp   (relaxed-bound conversion, §4)
  apply spec_mono (compl_as_extended_law cp (cbX.mono (by norm_num))
    (cbY.mono (by norm_num)) cbZ (cbT.mono (by norm_num)) cZ0 cT0)
  rintro R ⟨hRv, hRx, hRy⟩
  refine ⟨hRv, ?_, ?_⟩
  · -- curve membership: the denoted point IS an edAdd value, and edAdd is
    -- closed on the curve (Proofs/EdCurve.lean)
    show OnCurve (edX R) (edY R)
    rw [hRx, cx, hRy, cy]
    exact edAdd_closure (show OnCurve (edX P) (edY P) from hcP)
      (show OnCurve (edX Q) (edY Q) from hcQ)
  · -- the denotation equation, assembled componentwise
    calc edPt R = (edX R, edY R) := rfl
      _ = ((edAdd (edPt P) (edPt Q)).1, (edAdd (edPt P) (edPt Q)).2) := by
          rw [hRx, cx, hRy, cy]
      _ = edAdd (edPt P) (edPt Q) := rfl

/-- THE SUBTRACTION LAW for the public operator
    `impl Sub<&EdwardsPoint> for &EdwardsPoint` (edwards.rs:806-808,
    Funs.lean:3328-3340): same pipeline as `add` with the mixed SUB kernel.

    MATH:  on valid on-curve inputs,  sub P Q = ok R  with  ExtValid R,
    OnCurveExt R, and  edPt R = edAdd (edPt P) (edNeg (edPt Q))  — i.e.
    P − Q is P + (−Q), the group subtraction. -/
theorem edwards_sub_law (P Q : EdPoint)
    (hP : ExtValid P) (hQ : ExtValid Q)
    (hcP : OnCurveExt P) (hcQ : OnCurveExt Q) :
    Shared0EdwardsPoint.Insts.CoreOpsArithSubSharedAEdwardsPointEdwardsPoint.sub
      P Q ⦃ R =>
      ExtValid R ∧ OnCurveExt R ∧ edPt R = edAdd (edPt P) (edNeg (edPt Q)) ⦄ := by
  unfold Shared0EdwardsPoint.Insts.CoreOpsArithSubSharedAEdwardsPointEdwardsPoint.sub
  -- pnp ← as_projective_niels Q
  apply spec_bind (edwards_as_projective_niels_spec Q hQ)
  rintro pnp ⟨hpnpv, hpnpn⟩
  -- cp ← P − pnp   (kernel law: denotes edAdd with the NEGATED point)
  apply spec_bind (sub_projniels_law P pnp hpnpn hP hQ hcP hcQ hpnpv)
  rintro cp ⟨cbX, cbY, cbZ, cbT, cZ0, cT0, cx, cy⟩
  -- tail: as_extended cp  (Z here is 2⁵², T 2⁵⁴ — roles swapped vs add)
  apply spec_mono (compl_as_extended_law cp (cbX.mono (by norm_num))
    (cbY.mono (by norm_num)) (cbZ.mono (by norm_num)) cbT cZ0 cT0)
  rintro R ⟨hRv, hRx, hRy⟩
  refine ⟨hRv, ?_, ?_⟩
  · -- closure at (edPt P, edNeg (edPt Q)) — the negation stays on the curve
    show OnCurve (edX R) (edY R)
    rw [hRx, cx, hRy, cy]
    exact edAdd_closure (show OnCurve (edX P) (edY P) from hcP)
      (onCurve_neg (show OnCurve (edX Q) (edY Q) from hcQ))
  · calc edPt R = (edX R, edY R) := rfl
      _ = ((edAdd (edPt P) (edNeg (edPt Q))).1,
           (edAdd (edPt P) (edNeg (edPt Q))).2) := by
          rw [hRx, cx, hRy, cy]
      _ = edAdd (edPt P) (edNeg (edPt Q)) := rfl

/-- THE DOUBLING LAW for `EdwardsPoint::double` (edwards.rs:774-776):
    doubling denotes adding the point to itself with the COMPLETE law —
    no special doubling case distinction exists, because none is needed.

    MATH:  ExtValid P, OnCurveExt P  ==>  double P = ok R  with
        ExtValid R,  OnCurveExt R,  edPt R = edAdd (edPt P) (edPt P).

    PROOF.  `edwards_double_spec` (EdDouble.lean) already gives the four
    composed Segre products of the dbl-2008-hwcd kernel; substituting
    X = x·Z, Y = y·Z and writing u := y² − x², the curve equation
    −x² + y² = 1 + d·x²y² rewrites the doubling denominators
        u = 1 + d·x²y²        and        2 − u = 1 − d·x²y²,
    turning the products into
        ⟪R.X⟫ = Z⁴·2xy·(1 − D),     ⟪R.Y⟫ = Z⁴·(y²+x²)·(1 + D),
        ⟪R.Z⟫ = Z⁴·(1 + D)(1 − D),  (D := d·x²y²)
    whence  edX R = 2xy/(1 + D)  and  edY R = (y²+x²)/(1 − D)  — exactly
    `edAdd (x,y) (x,y)` — with ⟪R.Z⟫ ≠ 0 by completeness at ((x,y),(x,y)). -/
theorem edwards_double_law (P : EdPoint) (hP : ExtValid P) (hcP : OnCurveExt P) :
    edwards.EdwardsPoint.double P ⦃ R =>
      ExtValid R ∧ OnCurveExt R ∧ edPt R = edAdd (edPt P) (edPt P) ⦄ := by
  apply spec_mono (edwards_double_spec P hP)
  rintro R ⟨hbX, hbY, hbZ, hbT, hvX, hvY, hvZ, hvT⟩
  obtain ⟨-, -, -, -, hZ0, -⟩ := hP
  have hc : OnCurve (edX P) (edY P) := hcP
  -- completeness at the DIAGONAL pair ((x,y),(x,y)) — the doubling case
  obtain ⟨hp, hm⟩ := completeness hc hc
  have hX := ext_X_eq P hZ0
  have hY := ext_Y_eq P hZ0
  have hZ4 : ⟪P.Z⟫^4 ≠ 0 := pow_ne_zero 4 hZ0
  -- the curve equation in the doubling-friendly form  y² − x² = 1 + D
  have hcur : edY P ^ 2 - edX P ^ 2
      = 1 + edD * edX P * edX P * edY P * edY P := by
    have h := hc
    unfold OnCurve at h
    linear_combination h
  -- the three composed products, rewritten through the curve equation into
  -- Z⁴ times the canonical addition-law quantities at (x,y),(x,y)
  have eX : ⟪R.X⟫ = ⟪P.Z⟫^4 * ((edX P * edY P + edX P * edY P) *
      (1 - edD * edX P * edX P * edY P * edY P)) := by
    rw [hvX, hX, hY]
    linear_combination (-(2 * edX P * edY P * ⟪P.Z⟫^4)) * hcur
  have eY : ⟪R.Y⟫ = ⟪P.Z⟫^4 * ((edY P * edY P + edX P * edX P) *
      (1 + edD * edX P * edX P * edY P * edY P)) := by
    rw [hvY, hX, hY]
    linear_combination (⟪P.Z⟫^4 * (edY P * edY P + edX P * edX P)) * hcur
  have eZ : ⟪R.Z⟫ = ⟪P.Z⟫^4 * ((1 + edD * edX P * edX P * edY P * edY P) *
      (1 - edD * edX P * edX P * edY P * edY P)) := by
    rw [hvZ, hX, hY]
    linear_combination (⟪P.Z⟫^4 *
      (1 - edD * edX P * edX P * edY P * edY P - (edY P ^ 2 - edX P ^ 2))) * hcur
  -- the output denominator is a product of units (Z⁴ and the two complete
  -- denominators)
  have hRZ : ⟪R.Z⟫ ≠ 0 := by
    rw [eZ]
    exact mul_ne_zero hZ4 (mul_ne_zero hp hm)
  -- the two affine coordinates of the double
  have hxR : edX R = (edAdd (edPt P) (edPt P)).1 := by
    show ⟪R.X⟫ / ⟪R.Z⟫ = (edX P * edY P + edX P * edY P) /
      (1 + edD * edX P * edX P * edY P * edY P)
    rw [fp_div_eq_div_iff hRZ hp, eX, eZ]
    ring
  have hyR : edY R = (edAdd (edPt P) (edPt P)).2 := by
    show ⟪R.Y⟫ / ⟪R.Z⟫ = (edY P * edY P + edX P * edX P) /
      (1 - edD * edX P * edX P * edY P * edY P)
    rw [fp_div_eq_div_iff hRZ hm, eY, eZ]
    ring
  refine ⟨⟨hbX, hbY, hbZ, hbT, hRZ, ?_⟩, ?_, ?_⟩
  · -- Segre: (X'T')·(Y'Z') = (Z'T')·(X'Y') — pure ring on the products
    rw [hvX, hvY, hvZ, hvT]; ring
  · -- curve membership via closure at the diagonal
    show OnCurve (edX R) (edY R)
    rw [hxR, hyR]
    exact edAdd_closure hc hc
  · calc edPt R = (edX R, edY R) := rfl
      _ = ((edAdd (edPt P) (edPt P)).1, (edAdd (edPt P) (edPt P)).2) := by
          rw [hxR, hyR]
      _ = edAdd (edPt P) (edPt P) := rfl

/-- THE NEGATION LAW for `impl Neg for &EdwardsPoint` (edwards.rs:844-851):
    negation denotes the mathematical Edwards negation (x, y) ↦ (−x, y).

    MATH:  ExtValid P, OnCurveExt P  ==>  neg P = ok R  with  ExtValid R,
    OnCurveExt R (negation stays on the curve: `onCurve_neg`), and
    edPt R = edNeg (edPt P).  Direct from EdConvert's `edwards_neg_spec`. -/
theorem edwards_neg_law (P : EdPoint) (hP : ExtValid P) (hcP : OnCurveExt P) :
    Shared0EdwardsPoint.Insts.CoreOpsArithNegEdwardsPoint.neg P ⦃ R =>
      ExtValid R ∧ OnCurveExt R ∧ edPt R = edNeg (edPt P) ⦄ := by
  apply spec_mono (edwards_neg_spec P hP)
  rintro R ⟨hRv, -, -, -, -, hx, hy⟩
  refine ⟨hRv, ?_, ?_⟩
  · show OnCurve (edX R) (edY R)
    rw [hx, hy]
    exact onCurve_neg (show OnCurve (edX P) (edY P) from hcP)
  · calc edPt R = (edX R, edY R) := rfl
      _ = (-(edX P), edY P) := by rw [hx, hy]
      _ = edNeg (edPt P) := rfl

/-- THE IDENTITY LAW: the transpiled `EdwardsPoint::identity()` constant
    (0 : 1 : 1 : 0) runs, is valid, LIES ON THE CURVE (`onCurve_id`), and
    denotes the neutral element edId = (0, 1).  Packaging of EdDenote's
    `run_edwards_identity` runner with the math-layer facts. -/
theorem run_edwards_identity_law :
    ∃ I : EdPoint,
      edwards.EdwardsPoint.Insts.Curve25519TraitsIdentity.identity = ok I ∧
      ExtValid I ∧ OnCurveExt I ∧ edPt I = edId := by
  obtain ⟨I, hI, hIv, hx, hy⟩ := run_edwards_identity
  refine ⟨I, hI, hIv, ?_, ?_⟩
  · show OnCurve (edX I) (edY I)
    rw [hx, hy]
    exact onCurve_id
  · calc edPt I = (edX I, edY I) := rfl
      _ = (0, 1) := by rw [hx, hy]
      _ = edId := rfl

/-! ## 6. Runners: triple → existential, FieldMain style

    One `run_*` per operation, converting the law triples into plain
    existentials `∃ R, op = ok R ∧ …` ("the machine code RUNS without
    panicking and returns R with these properties") via `spec_exists`
    (Proofs/Field.lean) — the exact shape the certificate fields use. -/

/-- Runner for the addition law (see `edwards_add_law`). -/
theorem run_edwards_add (P Q : EdPoint)
    (hP : ExtValid P) (hQ : ExtValid Q)
    (hcP : OnCurveExt P) (hcQ : OnCurveExt Q) :
    ∃ R, Shared0EdwardsPoint.Insts.CoreOpsArithAddSharedAEdwardsPointEdwardsPoint.add
        P Q = ok R ∧
      ExtValid R ∧ OnCurveExt R ∧ edPt R = edAdd (edPt P) (edPt Q) :=
  spec_exists (edwards_add_law P Q hP hQ hcP hcQ)

/-- Runner for the subtraction law (see `edwards_sub_law`). -/
theorem run_edwards_sub (P Q : EdPoint)
    (hP : ExtValid P) (hQ : ExtValid Q)
    (hcP : OnCurveExt P) (hcQ : OnCurveExt Q) :
    ∃ R, Shared0EdwardsPoint.Insts.CoreOpsArithSubSharedAEdwardsPointEdwardsPoint.sub
        P Q = ok R ∧
      ExtValid R ∧ OnCurveExt R ∧ edPt R = edAdd (edPt P) (edNeg (edPt Q)) :=
  spec_exists (edwards_sub_law P Q hP hQ hcP hcQ)

/-- Runner for the doubling law (see `edwards_double_law`). -/
theorem run_edwards_double (P : EdPoint)
    (hP : ExtValid P) (hcP : OnCurveExt P) :
    ∃ R, edwards.EdwardsPoint.double P = ok R ∧
      ExtValid R ∧ OnCurveExt R ∧ edPt R = edAdd (edPt P) (edPt P) :=
  spec_exists (edwards_double_law P hP hcP)

/-- Runner for the negation law (see `edwards_neg_law`). -/
theorem run_edwards_neg (P : EdPoint)
    (hP : ExtValid P) (hcP : OnCurveExt P) :
    ∃ R, Shared0EdwardsPoint.Insts.CoreOpsArithNegEdwardsPoint.neg P = ok R ∧
      ExtValid R ∧ OnCurveExt R ∧ edPt R = edNeg (edPt P) :=
  spec_exists (edwards_neg_law P hP hcP)

/-! ## 7. The Edwards-implementation certificate -/

/-- The transpiled curve25519 point code implements the complete twisted
    Edwards addition law on  −x² + y² = 1 + d·x²·y²  over 𝔽_p, through the
    denotation `edPt` on valid on-curve extended points.

    This `structure … : Prop` is a named conjunction of five claims — a
    CERTIFICATE, mirroring `IsFieldImplementation` (FieldMain.lean).
    Field by field: each transpiled operation, on inputs satisfying the
    representation invariant (`ExtValid`) and the curve equation
    (`OnCurveExt`), (1) RETURNS `ok` — no panic, every machine-arithmetic
    side condition holds; (2) re-establishes BOTH invariants on its output;
    and (3) denotes the corresponding operation of the mathematical layer
    (Proofs/EdCurve.lean): the neutral element `edId`, the negation
    `edNeg`, and the COMPLETE addition law `edAdd` (with subtraction as
    addition of the negation and doubling as self-addition — the same
    branch-free formula, total by Bernstein–Lange completeness).
    WHY THIS SHAPE: as with the field layer, a literal group instance on
    the struct is impossible (redundant projective representation, partial
    machine ops), so the laws transfer through the denotation. -/
structure IsEdwardsImplementation : Prop where
  /-- `EdwardsPoint::identity()` runs, is valid, on-curve, denotes (0,1). -/
  id_ok : ∃ I : EdPoint,
    edwards.EdwardsPoint.Insts.Curve25519TraitsIdentity.identity = ok I ∧
    ExtValid I ∧ OnCurveExt I ∧ edPt I = edId
  /-- `−P` runs and denotes the Edwards negation (x, y) ↦ (−x, y). -/
  neg_ok : ∀ P : EdPoint, ExtValid P → OnCurveExt P →
    ∃ R, Shared0EdwardsPoint.Insts.CoreOpsArithNegEdwardsPoint.neg P = ok R ∧
      ExtValid R ∧ OnCurveExt R ∧ edPt R = edNeg (edPt P)
  /-- `P + Q` runs and denotes the complete addition law `edAdd`. -/
  add_ok : ∀ P Q : EdPoint, ExtValid P → ExtValid Q →
      OnCurveExt P → OnCurveExt Q →
    ∃ R, Shared0EdwardsPoint.Insts.CoreOpsArithAddSharedAEdwardsPointEdwardsPoint.add
        P Q = ok R ∧
      ExtValid R ∧ OnCurveExt R ∧ edPt R = edAdd (edPt P) (edPt Q)
  /-- `P − Q` runs and denotes addition of the negation: P + (−Q). -/
  sub_ok : ∀ P Q : EdPoint, ExtValid P → ExtValid Q →
      OnCurveExt P → OnCurveExt Q →
    ∃ R, Shared0EdwardsPoint.Insts.CoreOpsArithSubSharedAEdwardsPointEdwardsPoint.sub
        P Q = ok R ∧
      ExtValid R ∧ OnCurveExt R ∧ edPt R = edAdd (edPt P) (edNeg (edPt Q))
  /-- `P.double()` runs and denotes self-addition with the SAME complete
      formula — no exceptional doubling case. -/
  double_ok : ∀ P : EdPoint, ExtValid P → OnCurveExt P →
    ∃ R, edwards.EdwardsPoint.double P = ok R ∧
      ExtValid R ∧ OnCurveExt R ∧ edPt R = edAdd (edPt P) (edPt P)

/-- **The transpiled code implements the complete twisted Edwards addition
    law.**

    THE TIER-1 MAIN THEOREM of the point-arithmetic development.  Every
    clause of the certificate is discharged by the corresponding runner of
    §6, which in turn packages: the per-machine-op proofs of the *Spec
    files (panic-freedom and exact field arithmetic), the coordinate-level
    kernel specs (EdDouble/EdAddProjNiels/EdConvert), the denotation
    bridges of this file, and the pure mathematics of Proofs/EdCurve.lean
    (d non-square ⇒ completeness; closure; the group identities).
    `#print axioms CurveFieldProofs.edwardsImplementation` yields exactly
    [propext, Classical.choice, Quot.sound] — Lean's standard axioms only
    (checked live at the end of this file). -/
theorem edwardsImplementation : IsEdwardsImplementation where
  id_ok := run_edwards_identity_law
  neg_ok := fun P hP hcP => run_edwards_neg P hP hcP
  add_ok := fun P Q hP hQ hcP hcQ => run_edwards_add P Q hP hQ hcP hcQ
  sub_ok := fun P Q hP hQ hcP hcQ => run_edwards_sub P Q hP hQ hcP hcQ
  double_ok := fun P hP hcP => run_edwards_double P hP hcP

/-! ## 8. Group-ish laws THROUGH the implementation

    Each corollary runs the actual transpiled operations and states the
    corresponding mathematical law up to denotation — the implementation-
    level mirror of `edAdd_comm`/`edAdd_id`/`edAdd_neg` (EdCurve.lean),
    in the style of FieldMain's `impl_*` corollaries.  As there, the limb
    vectors of the two sides generally DIFFER; only the denoted affine
    points agree, which is why the laws are stated through `edPt`. -/

/-- Commutativity at the implementation level.

    MATH: for valid on-curve P, Q both `P + Q` and `Q + P` RUN, and their
    results denote the same affine point (edAdd is symmetric —
    `edAdd_comm`). -/
theorem impl_add_comm_ed (P Q : EdPoint)
    (hP : ExtValid P) (hQ : ExtValid Q)
    (hcP : OnCurveExt P) (hcQ : OnCurveExt Q) :
    ∃ R1 R2,
      Shared0EdwardsPoint.Insts.CoreOpsArithAddSharedAEdwardsPointEdwardsPoint.add
        P Q = ok R1 ∧
      Shared0EdwardsPoint.Insts.CoreOpsArithAddSharedAEdwardsPointEdwardsPoint.add
        Q P = ok R2 ∧
      edPt R1 = edPt R2 := by
  obtain ⟨R1, h1, -, -, e1⟩ := run_edwards_add P Q hP hQ hcP hcQ
  obtain ⟨R2, h2, -, -, e2⟩ := run_edwards_add Q P hQ hP hcQ hcP
  exact ⟨R1, R2, h1, h2, by rw [e1, e2, edAdd_comm]⟩

/-- Right identity at the implementation level.

    MATH: for valid on-curve P, running the identity constant and then
    `P + identity` yields a point denoting edPt P itself (`edAdd_id`). -/
theorem impl_add_id_ed (P : EdPoint) (hP : ExtValid P) (hcP : OnCurveExt P) :
    ∃ I R,
      edwards.EdwardsPoint.Insts.Curve25519TraitsIdentity.identity = ok I ∧
      Shared0EdwardsPoint.Insts.CoreOpsArithAddSharedAEdwardsPointEdwardsPoint.add
        P I = ok R ∧
      edPt R = edPt P := by
  obtain ⟨I, hI, hIv, hIc, hIe⟩ := run_edwards_identity_law
  obtain ⟨R, hR, -, -, hRe⟩ := run_edwards_add P I hP hIv hcP hIc
  refine ⟨I, R, hI, hR, ?_⟩
  rw [hRe, hIe]
  exact edAdd_id (show OnCurve (edX P) (edY P) from hcP)

/-- Inverses at the implementation level.

    MATH: for valid on-curve P, running `−P` and then `P + (−P)` yields a
    point denoting the neutral element edId = (0, 1) (`edAdd_neg`). -/
theorem impl_add_neg_ed (P : EdPoint) (hP : ExtValid P) (hcP : OnCurveExt P) :
    ∃ N R,
      Shared0EdwardsPoint.Insts.CoreOpsArithNegEdwardsPoint.neg P = ok N ∧
      Shared0EdwardsPoint.Insts.CoreOpsArithAddSharedAEdwardsPointEdwardsPoint.add
        P N = ok R ∧
      edPt R = edId := by
  obtain ⟨N, hN, hNv, hNc, hNe⟩ := run_edwards_neg P hP hcP
  obtain ⟨R, hR, -, -, hRe⟩ := run_edwards_add P N hP hNv hcP hNc
  refine ⟨N, R, hN, hR, ?_⟩
  rw [hRe, hNe]
  exact edAdd_neg (show OnCurve (edX P) (edY P) from hcP)

/- AXIOM AUDIT (live).  Expected (and verified) output:

     'CurveFieldProofs.edwardsImplementation' depends on axioms:
     [propext, Classical.choice, Quot.sound]

   — Lean's three standard axioms only: no sorry, no native_decide, no
   custom axiom.  (The 4 axioms modeling external functions in
   gen/CurveField/FunsExternal.lean are outside the dependency cone of the
   point operations verified here.)  The command's output is informational
   and does not affect the build. -/
#print axioms edwardsImplementation

end CurveFieldProofs
