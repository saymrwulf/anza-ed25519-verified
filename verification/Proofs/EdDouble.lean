/- ───────────────────────────────────────────────────────────────────────────
   Proofs/EdDouble.lean — coordinate-level specs for POINT DOUBLING:
   `ProjectivePoint::double` (the ℙ² → ℙ¹×ℙ¹ doubling kernel) and
   `EdwardsPoint::double` (the extended-coordinates wrapper around it).

   WHAT THIS FILE PROVES
     * `as_projective_spec` — `EdwardsPoint::as_projective` is a plain
       struct rebuild: it copies X, Y, Z (dropping T), is total, and its
       output is `ProjValid` whenever the input is `ExtValid`.
     * `proj_double_spec` — for ProjValid p, `ProjectivePoint::double p`
       is total (no panic/overflow anywhere in the 9 field ops) and returns
       the completed point r with the per-field limb bounds
           Bnd r.X 2⁵², Bnd r.Y 2⁵³, Bnd r.Z 2⁵², Bnd r.T 2⁵²
       and the four COORDINATE EQUATIONS over 𝔽_p (p = 2²⁵⁵ − 19)
           ⟪r.X⟫ = 2·⟪p.X⟫·⟪p.Y⟫
           ⟪r.Y⟫ = ⟪p.Y⟫² + ⟪p.X⟫²
           ⟪r.Z⟫ = ⟪p.Y⟫² − ⟪p.X⟫²
           ⟪r.T⟫ = 2·⟪p.Z⟫² − (⟪p.Y⟫² − ⟪p.X⟫²)
       (the X equation is stated in the ring-normal form 2XY; the code
       literally computes (X+Y)² − (Y²+X²), which `ring` identifies with it).
     * `edwards_double_spec` — for ExtValid P, `EdwardsPoint::double P`
       (= as_projective ∘ ProjectivePoint::double ∘ CompletedPoint::
       as_extended) is total, all four output coordinates are reduced
       (Bnd · 2⁵²), and, writing X' Y' Z' T' for the four completed-point
       polynomials above evaluated at ⟪P.X⟫ ⟪P.Y⟫ ⟪P.Z⟫, the output denotes
           ⟪r.X⟫ = X'·T',   ⟪r.Y⟫ = Y'·Z',   ⟪r.Z⟫ = Z'·T',   ⟪r.T⟫ = X'·Y'
       — the ℙ¹×ℙ¹ → ℙ³ Segre re-embedding of the doubled point.

   STATEMENT POLICY (deliberate). Everything here is COORDINATE-LEVEL: the
   hypotheses are the validity predicates of Proofs/EdDenote.lean (limb
   bounds + ⟪Z⟫ ≠ 0), and the postconditions are limb bounds plus polynomial
   identities over 𝔽_p in the INPUT struct-field denotations. No curve
   constant, no division, no `OnCurve` appears: that r really doubles the
   denoted affine point (and that ⟪r.Z⟫ ≠ 0, which needs the curve equation)
   is the job of the algebra layer (Proofs/EdCurve.lean and the op-law
   files), which will consume these specs and `fp_div_*`/`two_ne_zero'`.

   RUST ANALOG
   `ProjectivePoint::double`, curve25519/solana-ed25519/src/backend/serial/
   curve_models.rs:381-397 (transpiled at gen/CurveField/Funs.lean:1464-1487):
       let XX          = self.X.square();
       let YY          = self.Y.square();
       let ZZ2         = self.Z.square2();
       let X_plus_Y    = &self.X + &self.Y;
       let X_plus_Y_sq = X_plus_Y.square();
       let YY_plus_XX  = &YY + &XX;
       let YY_minus_XX = &YY - &XX;
       CompletedPoint { X: &X_plus_Y_sq - &YY_plus_XX,   // = 2XY
                        Y: YY_plus_XX,
                        Z: YY_minus_XX,
                        T: &ZZ2 - &YY_minus_XX }
   — the "dbl-2008-hwcd" doubling of Hisil–Wong–Carter–Dawson 2008 §3.3
   (a = −1 twisted Edwards), with 2·Z² computed by the dedicated `square2`
   (verified in Proofs/Square2Spec.lean).
   `EdwardsPoint::double`, src/edwards.rs:774-776 (Funs.lean:3261-3265):
       self.as_projective().double().as_extended()
   with `as_projective` (edwards.rs:541-547, Funs.lean:3029-3033) the X,Y,Z
   copy and `CompletedPoint::as_extended` (curve_models.rs:365-372,
   Funs.lean:1397-1413) the four cross-multiplications
   (X·T, Y·Z, Z·T, X·Y) landing back in extended coordinates.

   PANIC-FREEDOM / BOUND BOOKKEEPING (the entire totality argument)
     square/square2 inputs need Bnd · 2⁵⁴ — satisfied by ProjValid's 2⁵²;
     fe_add on two reduced (2⁵²) inputs: limbwise sums < 2⁵³ < 2⁶⁴, output
       Bnd 2⁵³ (the one unreduced value in the body, also fine as a square /
       sub input since 2⁵³ < 2⁵⁴);
     fe_sub/fe_mul inputs need 2⁵⁴ — all arguments are ≤ 2⁵³ here;
     outputs: square/mul 2⁵¹+2¹³ (≤ 2⁵²), square2 2⁵³, sub 2⁵², add 2⁵³.
   The `edis` discharge macro below closes every such side condition.

   PROOF ARCHITECTURE — the InvertSpec playbook
   Each body is walked with the `let*` symbolic-execution steps, consuming
   one field op per line via the registered specs (`square_spec'`,
   `square2_spec'`, `mul_spec'` and the two LOCAL wrappers `add_spec''`/
   `sub_spec''` below, derived from AddSpec/SubNegSpec); the final `ok`
   struct is collapsed by `spec_ok` + the `mk_*` projection lemmas of
   EdDenote, the bound conjuncts are the step posts (weakened by Bnd.mono),
   and each coordinate equation closes by rewriting the chain of value
   posts and `ring`.

   Imports: Proofs/EdDenote (point predicates, mk_* lemmas),
            Proofs/Square2Spec (square2_spec'; transitively SquareSpec /
            MulSpec / SubNegSpec / AddSpec and the WP layer).
   Imported by: the forthcoming doubling-law file (EdCurve algebra phase).
   ─────────────────────────────────────────────────────────────────────── -/
import Proofs.EdDenote
import Proofs.Square2Spec
open Aeneas Aeneas.Std Result
open curve25519

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
-- The step machinery sometimes discharges a side condition before the
-- attached `by edis` block runs (e.g. when an exact hypothesis is already
-- in context); keeping the uniform `by edis` on every step is clearer than
-- special-casing those, so the two "unused tactic" lints are disabled.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace CurveFieldProofs

-- the weakest-precondition layer: spec_mono / spec_ok used by the wrappers
open Aeneas.Std.WP

/-- Discharge tactic for the side conditions of the doubling bodies: either
    a hypothesis verbatim (validity predicates), linear arithmetic
    (`scalar_tac`), or a `Bnd _ c ≤ Bnd _ c'` weakening from any hypothesis
    via `Bnd.mono` (e.g. a 2⁵¹+2¹³ square output fed to a 2⁵⁴-input op).
    Same pattern as `bnd` in Proofs/InvertSpec.lean (macros are file-local,
    so it is re-declared here under a fresh name).
    (`name :=` disambiguates the generated syntax-kind declaration from the
    sibling files' `edis` macros so they can all be imported together.) -/
macro (name := edisDouble) "edis" : tactic =>
  `(tactic| (first
      | assumption
      | scalar_tac
      | exact Bnd.mono (by assumption) (by norm_num)))

/-! ## Local step-friendly wrappers for `+` and `-`

The base `add_spec` (Proofs/AddSpec.lean) needs explicit limb lists and
per-limb no-overflow hypotheses, and `sub_spec` (Proofs/SubNegSpec.lean)
needs explicit limb lists; the `let*` machinery cannot invent those. The two
wrappers below repackage them with the limbs hidden (via `Fe.exists_limbs`),
exactly like `mul_spec'`/`square_spec'` in InvertSpec. They are `private`
(file-local): other op-spec files declare their own copies, and privacy
prevents name clashes when several such files are imported together. -/

/-- Rust: `impl Add for FieldElement51` (limbwise `+`, NO reduction),
    curve25519/solana-ed25519/src/backend/serial/u64/field.rs:58-73.

    MATH:  Bnd(a,2⁵²) and Bnd(b,2⁵²)  ==>  fe_add a b = ok r  with
           Bnd(r, 2⁵³)  and  ⟪r⟫ = ⟪a⟫ + ⟪b⟫.
    The 2⁵² input bound is the reduced-operand discipline: limbwise sums are
    < 2⁵³ < 2⁶⁴ (no u64 overflow), and the output bound doubles — the
    generic law `∀ c, Bnd a c → Bnd b c → Bnd r (2c)` of `add_spec`
    instantiated at c = 2⁵². The value is exact over ℕ, so it adds in 𝔽_p.
    WHY NEEDED: `double` adds X+Y and YY+XX; both arguments are reduced
    (≤ 2⁵²), and the 2⁵³ output is exactly the bound the postcondition of
    `proj_double_spec` exposes for r.Y. -/
private theorem add_spec'' (a b : Fe) (ha : Bnd a (2^52)) (hb : Bnd b (2^52)) :
    fe_add a b ⦃ r => Bnd r (2^53) ∧ ⟪r⟫ = ⟪a⟫ + ⟪b⟫ ⦄ := by
  -- name the limbs and turn the two Bnd's into per-limb inequalities
  obtain ⟨a0, a1, a2, a3, a4, hla⟩ := Fe.exists_limbs a
  obtain ⟨b0, b1, b2, b3, b4, hlb⟩ := Fe.exists_limbs b
  have hba := (Bnd_eq a a0 a1 a2 a3 a4 _ hla).mp ha
  have hbb := (Bnd_eq b b0 b1 b2 b3 b4 _ hlb).mp hb
  -- run add_spec; each pairwise sum < 2⁵² + 2⁵² = 2⁵³ < 2⁶⁴ is closed by omega
  apply spec_mono (add_spec a b a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 hla hlb
    ⟨by omega, by omega, by omega, by omega, by omega⟩)
  rintro r ⟨-, hval, hbnd⟩
  -- bound: instantiate the "doubles any common bound" law at 2⁵² (2·2⁵² = 2⁵³)
  refine ⟨by simpa using hbnd (2^52) ha hb, ?_⟩
  -- value: feVal r = feVal a + feVal b over ℕ, then push through the cast
  simp [denote, hval]

/-- Rust: `impl Sub for FieldElement51` (add 16p limbwise, subtract, reduce),
    curve25519/solana-ed25519/src/backend/serial/u64/field.rs.

    MATH:  Bnd(a,2⁵⁴) and Bnd(b,2⁵⁴)  ==>  fe_sub a b = ok r  with
           Bnd(r, 2⁵²)  and  ⟪r⟫ = ⟪a⟫ − ⟪b⟫
    — `sub_spec` (Proofs/SubNegSpec.lean) verbatim, with the limb lists
    destructured internally so `let*` can apply it.
    WHY NEEDED: `double` subtracts three times (YY−XX, (X+Y)²−(YY+XX),
    2Z²−(YY−XX)); all six arguments are ≤ 2⁵³ < 2⁵⁴ here. -/
private theorem sub_spec'' (a b : Fe) (ha : Bnd a (2^54)) (hb : Bnd b (2^54)) :
    fe_sub a b ⦃ r => Bnd r (2^52) ∧ ⟪r⟫ = ⟪a⟫ - ⟪b⟫ ⦄ := by
  obtain ⟨a0, a1, a2, a3, a4, hla⟩ := Fe.exists_limbs a
  obtain ⟨b0, b1, b2, b3, b4, hlb⟩ := Fe.exists_limbs b
  exact sub_spec a b a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 hla hlb ha hb

/-! ## The doubling kernel on ℙ² -/

/-- Coordinate-level spec for `ProjectivePoint::double`.

    Rust: curve25519/solana-ed25519/src/backend/serial/curve_models.rs:
    381-397, transpiled at gen/CurveField/Funs.lean:1464-1487 — the
    Hisil–Wong–Carter–Dawson doubling producing a COMPLETED (ℙ¹×ℙ¹) point.

    MATH:  ProjValid p  ==>  double p = ok r  with
      Bnd r.X 2⁵², Bnd r.Y 2⁵³, Bnd r.Z 2⁵², Bnd r.T 2⁵²   and, in 𝔽_p,
      ⟪r.X⟫ = 2·⟪p.X⟫·⟪p.Y⟫                (computed as (X+Y)² − (Y²+X²))
      ⟪r.Y⟫ = ⟪p.Y⟫² + ⟪p.X⟫²
      ⟪r.Z⟫ = ⟪p.Y⟫² − ⟪p.X⟫²
      ⟪r.T⟫ = 2·⟪p.Z⟫² − (⟪p.Y⟫² − ⟪p.X⟫²).
    LaTeX: $(X':Z') = (2XY : Y^2 - X^2)$, $(Y':T') = (Y^2+X^2 : 2Z^2-(Y^2-X^2))$,
    i.e. the doubled point in ℙ¹×ℙ¹ — writing x = X/Z, y = Y/Z, this encodes
    x' = 2xy/(2(Z/Z)²−(y²−x²))-style fractions whose algebra (and the
    nonvanishing of the denominators) is established in the law layer, NOT
    here.

    Bounds: r.Y is the single unreduced addition of the body (two ≤ 2⁵²
    summands ⇒ 2⁵³); the other three fields are `sub` outputs (2⁵²). All
    four are < 2⁵⁴, so the completed point can feed any field op directly
    (`as_extended`/`as_projective` consume it below / in the add file).

    WHY NEEDED: the computational core of point doubling; consumed by
    `edwards_double_spec` below and by the scalar-multiplication ladder
    specs later. -/
theorem proj_double_spec (p : ProjPoint) (hp : ProjValid p) :
    backend.serial.curve_models.ProjectivePoint.double p ⦃ r =>
      Bnd r.X (2^52) ∧ Bnd r.Y (2^53) ∧ Bnd r.Z (2^52) ∧ Bnd r.T (2^52) ∧
      ⟪r.X⟫ = 2 * ⟪p.X⟫ * ⟪p.Y⟫ ∧
      ⟪r.Y⟫ = ⟪p.Y⟫^2 + ⟪p.X⟫^2 ∧
      ⟪r.Z⟫ = ⟪p.Y⟫^2 - ⟪p.X⟫^2 ∧
      ⟪r.T⟫ = 2 * ⟪p.Z⟫^2 - (⟪p.Y⟫^2 - ⟪p.X⟫^2) ⦄ := by
  -- the limb bounds of the validity predicate (⟪Z⟫ ≠ 0 is not needed here:
  -- doubling never divides — it is carried for the law layer only)
  obtain ⟨hpX, hpY, hpZ, -⟩ := hp
  -- expose the transpiled 9-op monadic body
  unfold backend.serial.curve_models.ProjectivePoint.double
  -- XX ← square p.X            ⟪XX⟫ = ⟪p.X⟫·⟪p.X⟫,  Bnd 2⁵¹+2¹³
  let* ⟨ XX, XX_post1, XX_post2 ⟩ ← square_spec' by edis
  -- YY ← square p.Y            ⟪YY⟫ = ⟪p.Y⟫·⟪p.Y⟫
  let* ⟨ YY, YY_post1, YY_post2 ⟩ ← square_spec' by edis
  -- ZZ2 ← square2 p.Z          ⟪ZZ2⟫ = 2·(⟪p.Z⟫·⟪p.Z⟫),  Bnd 2⁵³
  let* ⟨ ZZ2, ZZ2_post1, ZZ2_post2 ⟩ ← square2_spec' by edis
  -- X_plus_Y ← p.X + p.Y       (unreduced add of two reduced values, Bnd 2⁵³)
  let* ⟨ XpY, XpY_post1, XpY_post2 ⟩ ← add_spec'' by edis
  -- X_plus_Y_sq ← square X_plus_Y
  let* ⟨ XpYsq, XpYsq_post1, XpYsq_post2 ⟩ ← square_spec' by edis
  -- YY_plus_XX ← YY + XX       (both ≤ 2⁵¹+2¹³ ≤ 2⁵², output Bnd 2⁵³ = r.Y)
  let* ⟨ YpX, YpX_post1, YpX_post2 ⟩ ← add_spec'' by edis
  -- YY_minus_XX ← YY − XX      (sub reduces: Bnd 2⁵² = r.Z)
  let* ⟨ YmX, YmX_post1, YmX_post2 ⟩ ← sub_spec'' by edis
  -- fe ← X_plus_Y_sq − YY_plus_XX        (= 2XY, the r.X numerator)
  let* ⟨ feX, feX_post1, feX_post2 ⟩ ← sub_spec'' by edis
  -- fe1 ← ZZ2 − YY_minus_XX              (= 2Z² − (Y²−X²), the r.T field)
  let* ⟨ feT, feT_post1, feT_post2 ⟩ ← sub_spec'' by edis
  -- the body returns `ok { X := feX, Y := YpX, Z := YmX, T := feT }`; the
  -- `let*` machinery already collapsed the triple on the literal and reduced
  -- the struct projections, so the goal is the bare conjunction.
  -- Bounds are the step posts verbatim; each equation is the chain of value
  -- posts followed by polynomial normalization.
  refine ⟨feX_post1, YpX_post1, YmX_post1, feT_post1, ?_, ?_, ?_, ?_⟩
  · -- ⟪r.X⟫ = (⟪p.X⟫+⟪p.Y⟫)² − (⟪p.Y⟫²+⟪p.X⟫²) = 2·⟪p.X⟫·⟪p.Y⟫
    rw [feX_post2, XpYsq_post2, XpY_post2, YpX_post2, YY_post2, XX_post2]; ring
  · -- ⟪r.Y⟫ = ⟪p.Y⟫² + ⟪p.X⟫²
    rw [YpX_post2, YY_post2, XX_post2]; ring
  · -- ⟪r.Z⟫ = ⟪p.Y⟫² − ⟪p.X⟫²
    rw [YmX_post2, YY_post2, XX_post2]; ring
  · -- ⟪r.T⟫ = 2·⟪p.Z⟫² − (⟪p.Y⟫² − ⟪p.X⟫²)
    rw [feT_post2, ZZ2_post2, YmX_post2, YY_post2, XX_post2]; ring

/-! ## The extended-coordinates wrapper -/

/-- Spec for `EdwardsPoint::as_projective`: the ℙ³ → ℙ² forgetful map is a
    plain struct rebuild copying X, Y, Z (and dropping the cached T).

    Rust: curve25519/solana-ed25519/src/edwards.rs:541-547, transpiled at
    gen/CurveField/Funs.lean:3029-3033 (a single `ok { … }`, no field op).

    MATH:  ExtValid P  ==>  as_projective P = ok pp  with  ProjValid pp  and
           pp.X = P.X,  pp.Y = P.Y,  pp.Z = P.Z   (Fe-level equality of the
    limb vectors — strictly stronger than denotation equality, which is what
    downstream rewriting uses).  ProjValid is inherited: the three copied
    fields keep their 2⁵² bounds and ⟪Z⟫ ≠ 0 is ExtValid's own clause; the
    extended coherence X·Y = Z·T is simply forgotten.
    WHY NEEDED: first step of `EdwardsPoint::double` (and of `is_valid`);
    proving it once keeps `edwards_double_spec` a three-step composition. -/
theorem as_projective_spec (P : EdPoint) (hP : ExtValid P) :
    edwards.EdwardsPoint.as_projective P ⦃ pp =>
      ProjValid pp ∧ pp.X = P.X ∧ pp.Y = P.Y ∧ pp.Z = P.Z ⦄ := by
  obtain ⟨hX, hY, hZ, -, hZ0, -⟩ := hP
  -- the body is literally `ok { X := P.X, Y := P.Y, Z := P.Z }`
  unfold edwards.EdwardsPoint.as_projective
  -- collapse the triple on the `ok` literal; the three copy equations reduce
  -- to `True` (definitional projections of the literal)
  simp only [spec_ok]
  -- validity: bounds and ⟪Z⟫ ≠ 0 are ExtValid clauses
  exact ⟨⟨hX, hY, hZ, hZ0⟩, trivial, trivial, trivial⟩

/-- Coordinate-level spec for `EdwardsPoint::double`.

    Rust: curve25519/solana-ed25519/src/edwards.rs:774-776, transpiled at
    gen/CurveField/Funs.lean:3261-3265:
        self.as_projective().double().as_extended()
    — drop to ℙ², run the doubling kernel (`proj_double_spec`), then re-embed
    the completed ℙ¹×ℙ¹ result into extended ℙ³ coordinates via
    `CompletedPoint::as_extended` (curve_models.rs:365-372, Funs.lean:
    1397-1413), which cross-multiplies (X,Y,Z,T) ↦ (X·T, Y·Z, Z·T, X·Y).

    MATH:  ExtValid P  ==>  double P = ok r  with all four fields reduced
    (Bnd · 2⁵², they are mul outputs) and, abbreviating in 𝔽_p
        X' := 2·⟪P.X⟫·⟪P.Y⟫,             Y' := ⟪P.Y⟫² + ⟪P.X⟫²,
        Z' := ⟪P.Y⟫² − ⟪P.X⟫²,           T' := 2·⟪P.Z⟫² − (⟪P.Y⟫² − ⟪P.X⟫²),
    the four SEGRE-PRODUCT equations
        ⟪r.X⟫ = X'·T',   ⟪r.Y⟫ = Y'·Z',   ⟪r.Z⟫ = Z'·T',   ⟪r.T⟫ = X'·Y'
    (spelled out below with the primed names inlined — the postcondition is
    STRICTLY a polynomial identity in ⟪P.X⟫, ⟪P.Y⟫, ⟪P.Z⟫).

    ⚠ The output is stated coordinate-only, deliberately WITHOUT ⟪r.Z⟫ ≠ 0
    and without the extended coherence ⟪r.X⟫·⟪r.Y⟫ = ⟪r.Z⟫·⟪r.T⟫ (so not as
    `ExtValid r`): the coherence is a one-line `ring` consequence of the
    four equations (X'T'·Y'Z' = Z'T'·X'Y'), and Z'·T' ≠ 0 genuinely needs
    the curve equation on (edX P, edY P) — both belong to the algebra layer
    that packages doubling as a group law.  Note the cached T of the INPUT
    is not consumed by doubling at all (as_projective drops it), so the
    equations mention only ⟪P.X⟫, ⟪P.Y⟫, ⟪P.Z⟫.

    WHY NEEDED: the public doubling entry point of the crate; the scalar
    multiplication ladder and the group-law file build directly on it. -/
theorem edwards_double_spec (P : EdPoint) (hP : ExtValid P) :
    edwards.EdwardsPoint.double P ⦃ r =>
      Bnd r.X (2^52) ∧ Bnd r.Y (2^52) ∧ Bnd r.Z (2^52) ∧ Bnd r.T (2^52) ∧
      ⟪r.X⟫ = (2 * ⟪P.X⟫ * ⟪P.Y⟫) *
              (2 * ⟪P.Z⟫^2 - (⟪P.Y⟫^2 - ⟪P.X⟫^2)) ∧
      ⟪r.Y⟫ = (⟪P.Y⟫^2 + ⟪P.X⟫^2) * (⟪P.Y⟫^2 - ⟪P.X⟫^2) ∧
      ⟪r.Z⟫ = (⟪P.Y⟫^2 - ⟪P.X⟫^2) *
              (2 * ⟪P.Z⟫^2 - (⟪P.Y⟫^2 - ⟪P.X⟫^2)) ∧
      ⟪r.T⟫ = (2 * ⟪P.X⟫ * ⟪P.Y⟫) * (⟪P.Y⟫^2 + ⟪P.X⟫^2) ⦄ := by
  -- expose the 3-step transpiled body
  unfold edwards.EdwardsPoint.double
  -- pp ← as_projective P       (copies X, Y, Z; ProjValid from ExtValid)
  let* ⟨ pp, pp_valid, ppX, ppY, ppZ ⟩ ← as_projective_spec by edis
  -- cp ← ProjectivePoint.double pp      (the kernel, spec above)
  let* ⟨ cp, cpX_b, cpY_b, cpZ_b, cpT_b, cpX_v, cpY_v, cpZ_v, cpT_v ⟩ ←
    proj_double_spec by edis
  -- the tail call: as_extended cp — four cross-multiplications
  unfold backend.serial.curve_models.CompletedPoint.as_extended
  -- rX ← cp.X * cp.T,  rY ← cp.Y * cp.Z,  rZ ← cp.Z * cp.T,  rT ← cp.X * cp.Y
  -- (every factor is ≤ 2⁵³ < 2⁵⁴ by the kernel's bounds — edis weakens)
  let* ⟨ rX, rX_post1, rX_post2 ⟩ ← mul_spec' by edis
  let* ⟨ rY, rY_post1, rY_post2 ⟩ ← mul_spec' by edis
  let* ⟨ rZ, rZ_post1, rZ_post2 ⟩ ← mul_spec' by edis
  let* ⟨ rT, rT_post1, rT_post2 ⟩ ← mul_spec' by edis
  -- final struct literal: the `let*` machinery already collapsed the triple
  -- and reduced the projections, leaving the bare conjunction.
  -- bounds: mul outputs are 2⁵¹+2¹³ ≤ 2⁵²; equations: substitute the mul
  -- posts, the kernel's coordinate equations, and the as_projective copies,
  -- then normalize
  refine ⟨rX_post1.mono (by norm_num), rY_post1.mono (by norm_num),
          rZ_post1.mono (by norm_num), rT_post1.mono (by norm_num),
          ?_, ?_, ?_, ?_⟩
  -- (after the rewrites both sides are syntactically identical, so the `rfl`
  -- built into `rw` closes each goal — no `ring` needed)
  · -- ⟪r.X⟫ = ⟪cp.X⟫·⟪cp.T⟫ = X'·T'
    rw [rX_post2, cpX_v, cpT_v, ppX, ppY, ppZ]
  · -- ⟪r.Y⟫ = ⟪cp.Y⟫·⟪cp.Z⟫ = Y'·Z'
    rw [rY_post2, cpY_v, cpZ_v, ppX, ppY]
  · -- ⟪r.Z⟫ = ⟪cp.Z⟫·⟪cp.T⟫ = Z'·T'
    rw [rZ_post2, cpZ_v, cpT_v, ppX, ppY, ppZ]
  · -- ⟪r.T⟫ = ⟪cp.X⟫·⟪cp.Y⟫ = X'·Y'
    rw [rT_post2, cpX_v, cpY_v, ppX, ppY]

end CurveFieldProofs
