/- ───────────────────────────────────────────────────────────────────────────
   Proofs/EdDenote.lean — POINT DENOTATION layer: from transpiled limb
   structures to coordinates in 𝔽_p, p = 2²⁵⁵ − 19.

   CONTEXT. The Rust crate curve25519/solana-ed25519 represents points of
   the twisted Edwards curve  −x² + y² = 1 + d·x²y²  (d = −121665/121666)
   in four internal models (src/backend/serial/curve_models.rs module docs,
   following Hisil–Wong–Carter–Dawson 2008 and the ℙ¹×ℙ¹ picture of
   Costello–Smith 2017):

     * `EdwardsPoint`          (X:Y:Z:T)  — "extended" ℙ³ coordinates with
                               x = X/Z, y = Y/Z and the Segre coherence
                               X·Y = Z·T (equivalently T = XY/Z);
     * `ProjectivePoint`       (X:Y:Z)    — ℙ² coordinates, x = X/Z, y = Y/Z;
     * `CompletedPoint`        ((X:Z),(Y:T)) ∈ ℙ¹×ℙ¹ — x = X/Z, y = Y/T
                               (NOTE: here T is the SECOND DENOMINATOR, a
                               completely different role from the extended T);
     * `ProjectiveNielsPoint`  (Y+X, Y−X, Z, T·2d) — a CACHE of readily-added
                               combinations of an extended point;
     * `AffineNielsPoint`      (y+x, y−x, 2d·x·y)  — the same cache for an
                               affine point (Z = 1).

   All coordinates are `FieldElement51` (= `Fe`) limb vectors; Charon+Aeneas
   transpiled the structures to gen/CurveField/Types.lean and the code to
   gen/CurveField/Funs.lean.  Proofs/FieldMain.lean already established that
   the FIELD layer is correct: the denotation ⟪·⟫ : Fe → 𝔽_p, the limb-bound
   invariant `Bnd`, and one `run_*` theorem per field operation.

   THIS FILE builds the corresponding layer for POINTS, in four parts:

     1. VALIDITY PREDICATES + DENOTATIONS for each representation
        (`ExtValid`/`edX`/`edY`, `ProjValid`/`projX`/`projY`,
         `ComplValid`/`complX`/`complY`, `ProjNielsValid`/`IsNielsOf`,
         `AffNielsValid`/`IsAffNielsOf`).
        ⚠ The Z ≠ 0 (resp. Z ≠ 0 ∧ T ≠ 0) side conditions are carried
        EXPLICITLY: the Rust code NEVER checks them (projective division by
        zero cannot panic — it is simply never performed; the code only
        manipulates numerators/denominators), so they must live in the
        specification layer.  Every honest production of a point (identity,
        decompression, the add/double formulas on valid inputs) maintains
        them, and the op-spec phase will thread them through.

     2. CONSTANT SPECS for the precomputed curve constants `EDWARDS_D` and
        `EDWARDS_D2` (gen/CurveField/Funs.lean).  To keep this file
        independent of the (not-yet-existing) math layer Proofs/EdCurve.lean
        — which will define the canonical `edD : Fp := -(121665:Fp)/121666` —
        the d-constant is specified in CHARACTERIZATION FORM:
            121666 · ⟪D⟫ = −121665      (d   = −121665/121666)
            121666 · ⟪D2⟫ = −243330     (2d  = −243330/121666),
        which pins the same field element without naming any quotient.
        `edwards_d2_eq_two_d` then proves ⟪D2⟫ = 2·⟪D⟫ outright.

     3. IDENTITY-CONSTANT SPECS: the generated `Identity` trait
        implementations for `ProjectivePoint` (0:1:1), `AffineNielsPoint`
        (1,1,0), `ProjectiveNielsPoint` (1,1,1,0) and `EdwardsPoint`
        (0:1:1:0) all RUN (no panic), are valid, and denote the neutral
        affine point (0, 1).

     4. SMALL FIELD HELPERS the op-spec phase needs: 2 ≠ 0 and 121666 ≠ 0
        in 𝔽_p, division-equation rewrites (`fp_div_eq_iff` etc.), the
        determinism extractor `ok_ext`, and the constructor-projection
        (`mk_*`) conveniences for the point structures.

   PROOF TECHNIQUE for the constants: identical to `sqrt_m1_spec`
   (Proofs/ConstSpecs.lean).  Each constant is `from_limbs` of 5 literal
   limbs; `simp` evaluates the denotation to a concrete ~255-bit natural
   number N, and the characterization becomes the ℕ-congruence
   (121666·N) mod p = p − 121665, which `norm_num` checks by kernel-verified
   literal arithmetic.  (Sanity-checked externally:
     N_d  = 37095705934669439343138083508754565189542113879843219016388785533085940283555,
     N_d2 = 16295367250680780974490674513165176452449235426866156013048779062215315747161,
   121666·N_d  ≡ −121665 and 121666·N_d2 ≡ −243330 (mod p), N_d2 ≡ 2·N_d.)

   Nothing in gen/ (the transpiled code) is modified; we only define
   predicates ABOUT it and run it.

   Imports: Proofs/FieldMain.lean (denotation, Bnd, run_* runners, Field 𝔽_p).
   Imported by: the forthcoming point-operation spec files.
   ─────────────────────────────────────────────────────────────────────── -/
import Proofs.FieldMain
open Aeneas Aeneas.Std Result
open curve25519

set_option maxHeartbeats 4000000

namespace CurveFieldProofs

/-! ## Short aliases for the transpiled point types

    Definitionally the generated structures (`rfl`-equal), mirroring the
    `Fe`/`fe_*` aliases of Proofs/Denote.lean.  The Rust source lines cited
    are from the generated docstrings in gen/CurveField/Types.lean. -/

/-- Rust: `pub struct EdwardsPoint { X, Y, Z, T: FieldElement51 }`,
    src/edwards.rs:390-395 — extended (ℙ³ / "extended twisted Edwards")
    coordinates. -/
abbrev EdPoint := edwards.EdwardsPoint

/-- Rust: `pub(crate) struct ProjectivePoint { X, Y, Z }`,
    src/backend/serial/curve_models.rs:154-158 — ℙ² coordinates. -/
abbrev ProjPoint := backend.serial.curve_models.ProjectivePoint

/-- Rust: `pub(crate) struct CompletedPoint { X, Y, Z, T }`,
    src/backend/serial/curve_models.rs:169-174 — ℙ¹×ℙ¹ coordinates
    ((X:Z),(Y:T)); the output type of the add/double kernels. -/
abbrev ComplPoint := backend.serial.curve_models.CompletedPoint

/-- Rust: `pub struct ProjectiveNielsPoint { Y_plus_X, Y_minus_X, Z, T2d }`,
    src/backend/serial/curve_models.rs:206-211 — readily-addable cache of an
    `EdwardsPoint`. -/
abbrev ProjNiels := backend.serial.curve_models.ProjectiveNielsPoint

/-- Rust: `pub(crate) struct AffineNielsPoint { y_plus_x, y_minus_x, xy2d }`,
    src/backend/serial/curve_models.rs:184-188 — readily-addable cache of an
    affine point (Z = 1). -/
abbrev AffNiels := backend.serial.curve_models.AffineNielsPoint

/-! ## Small 𝔽_p facts the point layer relies on

    The point denotations divide by Z (and T), and the d-constant
    characterization divides (conceptually) by 121666 and 2; these lemmas
    make those denominators usable. -/

/-- No Rust analog — arithmetic helper generalizing `natCast_P_sub_one`
    (Proofs/ConstSpecs.lean) from k = 1 to arbitrary k ≤ p.

    MATH:  ((p − k : ℕ) : 𝔽_p) = −(k : 𝔽_p)   (since p ≡ 0 in 𝔽_p).
    WHY NEEDED: the constant specs below compute (121666·N) mod p to the ℕ
    literal p − 121665 (resp. p − 243330); this lemma converts that natural
    number into the field element −121665 (resp. −243330). -/
theorem natCast_P_sub (k : ℕ) (hk : k ≤ P) : ((P - k : ℕ) : Fp) = -(k : Fp) := by
  -- k ≤ p lets Nat.cast_sub distribute the truncated subtraction
  rw [Nat.cast_sub hk, ZMod.natCast_self]
  ring

/-- No Rust analog — arithmetic helper.

    MATH:  0 < k < p  ==>  (k : 𝔽_p) ≠ 0.
    A positive natural number below the modulus does not vanish mod p:
    (k : 𝔽_p) = 0 would mean p ∣ k, forcing p ≤ k.
    WHY NEEDED: the two specific instances below (k = 2 and k = 121666);
    stated generally so the op-spec phase can produce further nonzero
    numerals (e.g. 121665, 486664) without repeating the argument. -/
theorem natCast_ne_zero_of_lt_P {k : ℕ} (h0 : 0 < k) (hk : k < P) :
    ((k : ℕ) : Fp) ≠ 0 := by
  intro h
  -- (k : ZMod p) = 0 ↔ p ∣ k, and a divisor of a positive number is ≤ it
  have hdvd : P ∣ k := (ZMod.natCast_eq_zero_iff k P).mp h
  have := Nat.le_of_dvd h0 hdvd
  omega

/-- MATH:  (2 : 𝔽_p) ≠ 0  — p = 2²⁵⁵ − 19 is an ODD prime, so the field has
    characteristic ≠ 2.

    WHY NEEDED: the projective-niels denominator is 2·Z (the cache stores
    Y+X and Y−X, whose sum/difference is 2Y/2X), so recovering coordinates
    divides by 2; also doubling formulas.  Primed to avoid clashing with
    mathlib's `two_ne_zero`. -/
theorem two_ne_zero' : (2 : Fp) ≠ 0 := by
  have h := natCast_ne_zero_of_lt_P (k := 2) (by norm_num) (by norm_num [P])
  exact_mod_cast h

/-- MATH:  (121666 : 𝔽_p) ≠ 0  (121666 = 1 − a·d⁻¹-free spelling: it is just
    a small positive integer < p).

    WHY NEEDED: the curve constant d is characterized below as the solution
    of 121666·d = −121665; this lemma makes that characterization UNIQUE
    (121666 is invertible), which `edwards_d2_eq_two_d` and the future
    EdCurve.lean bridge (d = −121665/121666) exploit. -/
theorem c121666_ne_zero : (121666 : Fp) ≠ 0 := by
  have h := natCast_ne_zero_of_lt_P (k := 121666) (by norm_num) (by norm_num [P])
  exact_mod_cast h

/-! ## 1. Validity predicates and denotations

    Each representation gets
      * a VALIDITY predicate: the limb bounds under which the transpiled
        field ops run panic-free (the dalek 2⁵²/2⁵⁴ discipline of
        Proofs/FieldMain.lean), PLUS the nonzero-denominator conditions; and
      * a DENOTATION: the affine coordinates (x, y) ∈ 𝔽_p × 𝔽_p it
        represents.

    ⚠ Z ≠ 0 IS NOT CHECKED BY THE RUST CODE.  The implementation never
    divides — it works with fractions symbolically — so nothing at runtime
    enforces a nonzero denominator, and a "point" with Z = 0 would
    silently denote garbage (0/0).  The predicate layer here is where that
    obligation lives; every constructor of points we specify (identity
    below, decompression and the arithmetic kernels in the op-spec phase)
    PROVES it, and every consumer ASSUMES it. -/

/-- Validity of an extended ("ℙ³") point P = (X : Y : Z : T).

    MATH:  all four coordinates obey the reduced limb bound 2⁵²
           (so any field op may consume them),  Z ≢ 0 (mod p),  and the
           Segre/extended coherence  X·Y ≡ Z·T (mod p)
           (i.e. T carries the product x·y: T/Z = (X/Z)·(Y/Z)).
    Rust: the *intended* invariant of `EdwardsPoint` per
    curve_models.rs module docs ("the curve is given by the pair of
    equations −W₁² + W₂² = W₃² + dW₀², W₀W₃ = W₁W₂"); the curve equation
    itself is deliberately NOT part of this predicate — it belongs to the
    math layer (Proofs/EdCurve.lean) on the denoted pair (edX, edY).
    WHY NEEDED: precondition and postcondition of every extended-point
    operation in the op-spec phase. -/
def ExtValid (Pt : EdPoint) : Prop :=
  Bnd Pt.X (2^52) ∧ Bnd Pt.Y (2^52) ∧ Bnd Pt.Z (2^52) ∧ Bnd Pt.T (2^52) ∧
  ⟪Pt.Z⟫ ≠ 0 ∧ ⟪Pt.X⟫ * ⟪Pt.Y⟫ = ⟪Pt.Z⟫ * ⟪Pt.T⟫

/-- Affine x-coordinate denoted by an extended point:  x = ⟪X⟫ / ⟪Z⟫.
    (Meaningful under `ExtValid` — division by ⟪Z⟫ ≠ 0; on Z ≡ 0 it would
    be mathlib's junk value 0.)  `noncomputable` because 𝔽_p division goes
    through the classical field instance — irrelevant, never executed. -/
noncomputable def edX (Pt : EdPoint) : Fp := ⟪Pt.X⟫ / ⟪Pt.Z⟫

/-- Affine y-coordinate denoted by an extended point:  y = ⟪Y⟫ / ⟪Z⟫. -/
noncomputable def edY (Pt : EdPoint) : Fp := ⟪Pt.Y⟫ / ⟪Pt.Z⟫

/-- Validity of a projective ("ℙ²") point P = (X : Y : Z).

    MATH:  limb bounds 2⁵² on X, Y, Z  and  Z ≢ 0 (mod p).
    No coherence equation — ℙ² has no redundant coordinate. -/
def ProjValid (Pt : ProjPoint) : Prop :=
  Bnd Pt.X (2^52) ∧ Bnd Pt.Y (2^52) ∧ Bnd Pt.Z (2^52) ∧ ⟪Pt.Z⟫ ≠ 0

/-- Affine x-coordinate denoted by a projective point:  x = ⟪X⟫ / ⟪Z⟫. -/
noncomputable def projX (Pt : ProjPoint) : Fp := ⟪Pt.X⟫ / ⟪Pt.Z⟫

/-- Affine y-coordinate denoted by a projective point:  y = ⟪Y⟫ / ⟪Z⟫. -/
noncomputable def projY (Pt : ProjPoint) : Fp := ⟪Pt.Y⟫ / ⟪Pt.Z⟫

/-- Validity of a completed ("ℙ¹×ℙ¹") point P = ((X : Z), (Y : T)).

    MATH:  limb bounds 2⁵² on all four coordinates,  Z ≢ 0  AND  T ≢ 0.
    ⚠ TWO denominators: the completed model is a product of two projective
    lines, x = X/Z on the first and y = Y/T on the second — the field T here
    plays the role of a DENOMINATOR for y, entirely unlike the extended
    model's T (which is a cached numerator product).  Both must be nonzero
    for the point to denote affine coordinates. -/
def ComplValid (Pt : ComplPoint) : Prop :=
  Bnd Pt.X (2^52) ∧ Bnd Pt.Y (2^52) ∧ Bnd Pt.Z (2^52) ∧ Bnd Pt.T (2^52) ∧
  ⟪Pt.Z⟫ ≠ 0 ∧ ⟪Pt.T⟫ ≠ 0

/-- Affine x-coordinate denoted by a completed point:  x = ⟪X⟫ / ⟪Z⟫. -/
noncomputable def complX (Pt : ComplPoint) : Fp := ⟪Pt.X⟫ / ⟪Pt.Z⟫

/-- Affine y-coordinate denoted by a completed point:  y = ⟪Y⟫ / ⟪T⟫
    (T, not Z — see `ComplValid`). -/
noncomputable def complY (Pt : ComplPoint) : Fp := ⟪Pt.Y⟫ / ⟪Pt.T⟫

/-- Limb-bound + denominator validity of a projective-niels cache point.

    MATH:  Bnd(Y_plus_X, 2⁵³), Bnd(Y_minus_X, 2⁵³), Bnd(Z, 2⁵²),
           Bnd(T2d, 2⁵²), and ⟪Z⟫ ≠ 0.
    The 2⁵³ bound on the two sum/difference fields is the natural one:
    `to_projective_niels` computes Y_plus_X with the UNREDUCED `fe_add`
    (output bound 2⁵³ — `run_add`, FieldMain.lean) from two reduced (2⁵²)
    coordinates, while Y_minus_X, Z, T2d come from `fe_sub`/`fe_mul`
    (output bound 2⁵²; stated as ≤ 2⁵³ resp. 2⁵² accordingly).  All four
    are < 2⁵⁴, so every field op may consume them directly. -/
def ProjNielsValid (N : ProjNiels) : Prop :=
  Bnd N.Y_plus_X (2^53) ∧ Bnd N.Y_minus_X (2^53) ∧ Bnd N.Z (2^52) ∧
  Bnd N.T2d (2^52) ∧ ⟪N.Z⟫ ≠ 0

/-- RELATIONAL denotation of a projective-niels point: `IsNielsOf N Pt`
    says the cache N was correctly derived from the extended point Pt.

    MATH:  ⟪Y_plus_X⟫  = ⟪Pt.Y⟫ + ⟪Pt.X⟫,
           ⟪Y_minus_X⟫ = ⟪Pt.Y⟫ − ⟪Pt.X⟫,
           ⟪Z⟫         = ⟪Pt.Z⟫,
           121666 · ⟪T2d⟫ = −243330 · ⟪Pt.T⟫     (i.e.  ⟪T2d⟫ = ⟪Pt.T⟫ · 2d,
           with 2d = −243330/121666 expressed denominator-free — the same
           characterization trick as `edwards_d_spec` below, so no `edD`
           definition is needed in this file).

    DESIGN.  We deliberately specify the niels cache RELATIONALLY rather
    than giving it standalone coordinates (which would be
    x = (⟪Y_plus_X⟫ − ⟪Y_minus_X⟫)/(2⟪Z⟫), y = (⟪Y_plus_X⟫ + ⟪Y_minus_X⟫)/(2⟪Z⟫)
    plus a cache-coherence equation for T2d): every niels point the code
    ever creates comes from `to_projective_niels` on a concrete extended
    point, and every consumer (`add`/`sub` of EdwardsPoint + ProjNiels)
    immediately recombines the fields, so the derivation facts are exactly
    the shape the op-spec proofs use.  The standalone coordinates are
    recoverable from this relation by field algebra (divide by 2⟪Z⟫ ≠ 0,
    using `two_ne_zero'` and `fp_div_eq_iff`). -/
def IsNielsOf (N : ProjNiels) (Pt : EdPoint) : Prop :=
  ⟪N.Y_plus_X⟫ = ⟪Pt.Y⟫ + ⟪Pt.X⟫ ∧
  ⟪N.Y_minus_X⟫ = ⟪Pt.Y⟫ - ⟪Pt.X⟫ ∧
  ⟪N.Z⟫ = ⟪Pt.Z⟫ ∧
  (121666 : Fp) * ⟪N.T2d⟫ = -243330 * ⟪Pt.T⟫

/-- Limb-bound validity of an affine-niels cache point.

    MATH:  Bnd(y_plus_x, 2⁵³), Bnd(y_minus_x, 2⁵³), Bnd(xy2d, 2⁵²).
    No denominator condition — the affine cache has implicit Z = 1.
    (2⁵³ on the sum/difference fields for the same `fe_add` reason as in
    `ProjNielsValid`; the precomputed basepoint tables actually store
    reduced values, which satisfy this a fortiori.) -/
def AffNielsValid (N : AffNiels) : Prop :=
  Bnd N.y_plus_x (2^53) ∧ Bnd N.y_minus_x (2^53) ∧ Bnd N.xy2d (2^52)

/-- RELATIONAL denotation of an affine-niels point: `IsAffNielsOf N x y`
    says N caches the affine point (x, y)  (implicit Z = 1).

    MATH:  ⟪y_plus_x⟫ = y + x,   ⟪y_minus_x⟫ = y − x,
           121666 · ⟪xy2d⟫ = −243330 · (x · y)    (i.e. ⟪xy2d⟫ = 2d·x·y,
           denominator-free as in `IsNielsOf`). -/
def IsAffNielsOf (N : AffNiels) (x y : Fp) : Prop :=
  ⟪N.y_plus_x⟫ = y + x ∧
  ⟪N.y_minus_x⟫ = y - x ∧
  (121666 : Fp) * ⟪N.xy2d⟫ = -243330 * (x * y)

/-! ## 2. The curve constants EDWARDS_D and EDWARDS_D2

    Rust: `constants::EDWARDS_D` ("Edwards d value, equal to
    −121665/121666 mod p") and `constants::EDWARDS_D2` (= 2·d),
    curve25519/solana-ed25519/src/backend/serial/u64/constants.rs:45-60;
    transpiled at gen/CurveField/Funs.lean:1121 and :1977 as `from_limbs`
    of 5 literal limbs each.

    The specs use the denominator-free CHARACTERIZATION
        121666 · d = −121665,
    which determines d uniquely in 𝔽_p (121666 is invertible —
    `c121666_ne_zero`), so this file needs no division and no dependence on
    the future canonical definition `edD := -(121665 : Fp)/121666` in
    Proofs/EdCurve.lean (the bridge there is one `fp_div_eq_iff` away). -/

/-- Rust: `constants::EDWARDS_D`, u64/constants.rs:45-51.

    MATH:  EDWARDS_D = ok D  with  Bnd(D, 2⁵²)  and  121666·⟪D⟫ = −121665
    in 𝔽_p — i.e. ⟪D⟫ is THE Edwards curve constant d = −121665/121666.
    The limbs [929955233495203, 466365720129213, 1662059464998953,
    2033849074728123, 1442794654840575] denote the 255-bit number
        N_d = 37095705934669439343138083508754565189542113879843219016388785533085940283555
    and the spec certifies 121666·N_d ≡ −121665 (mod p) by kernel-verified
    literal arithmetic (the `sqrt_m1_spec` technique, ConstSpecs.lean).
    (Each limb is < 2⁵¹; stated at the uniform reduced bound 2⁵².)

    WHY NEEDED: a corrupted table entry here would change the curve being
    implemented — `is_valid`, point addition (via T2d/xy2d caches) and
    decompression all multiply by this constant. -/
theorem edwards_d_spec :
    backend.serial.u64.constants.EDWARDS_D ⦃ dfe =>
      Bnd dfe (2^52) ∧ (121666 : Fp) * ⟪dfe⟫ = -121665 ⦄ := by
  unfold backend.serial.u64.constants.EDWARDS_D
    backend.serial.u64.field.FieldElement51.from_limbs
  -- simp discharges the Bnd conjunct and evaluates `feVal` to the literal
  -- N_d; the remaining goal is `(121666 : 𝔽_p) * (N_d : 𝔽_p) = -121665`.
  simp [Bnd, denote, feVal, limbsVal, Array.make]
  -- 121666·N_d ≡ p − 121665 (mod p), checked by literal arithmetic on ℕ
  -- (norm_num evaluates the ~272-bit product and the division by p in-kernel)
  have hmod :
      ((121666 *
        37095705934669439343138083508754565189542113879843219016388785533085940283555 : ℕ))
        % P = P - 121665 := by
    norm_num [P]
  -- assemble: 121666·(N_d:𝔽_p) = ((121666·N_d) mod p : 𝔽_p) = ((p−121665) : 𝔽_p) = −121665
  have key :
      ((121666 : ℕ) : Fp) *
      ((37095705934669439343138083508754565189542113879843219016388785533085940283555 : ℕ) : Fp)
        = -121665 := by
    rw [← Nat.cast_mul, ← ZMod.natCast_mod, hmod,
        natCast_P_sub 121665 (by norm_num [P])]
    norm_num
  exact_mod_cast key

/-- Rust: `constants::EDWARDS_D2` ("Edwards 2*d value, equal to
    2*(−121665/121666) mod p"), u64/constants.rs:54-60.

    MATH:  EDWARDS_D2 = ok D2  with  Bnd(D2, 2⁵²)  and
           121666·⟪D2⟫ = −243330  in 𝔽_p — the SAME characterization shape
    as `edwards_d_spec`, with −243330 = 2·(−121665), so ⟪D2⟫ = 2d
    (made explicit by `edwards_d2_eq_two_d` below).
    The limbs [1859910466990425, 932731440258426, 1072319116312658,
    1815898335770999, 633789495995903] denote
        N_d2 = 16295367250680780974490674513165176452449235426866156013048779062215315747161,
    and the spec certifies 121666·N_d2 ≡ −243330 (mod p).

    WHY NEEDED: `T2d`/`xy2d` caches are built by multiplying with this
    constant; the extended-coordinates addition formulas bake "2d" in. -/
theorem edwards_d2_spec :
    backend.serial.u64.constants.EDWARDS_D2 ⦃ d2 =>
      Bnd d2 (2^52) ∧ (121666 : Fp) * ⟪d2⟫ = -243330 ⦄ := by
  unfold backend.serial.u64.constants.EDWARDS_D2
    backend.serial.u64.field.FieldElement51.from_limbs
  simp [Bnd, denote, feVal, limbsVal, Array.make]
  -- 121666·N_d2 ≡ p − 243330 (mod p), literal arithmetic on ℕ
  have hmod :
      ((121666 *
        16295367250680780974490674513165176452449235426866156013048779062215315747161 : ℕ))
        % P = P - 243330 := by
    norm_num [P]
  have key :
      ((121666 : ℕ) : Fp) *
      ((16295367250680780974490674513165176452449235426866156013048779062215315747161 : ℕ) : Fp)
        = -243330 := by
    rw [← Nat.cast_mul, ← ZMod.natCast_mod, hmod,
        natCast_P_sub 243330 (by norm_num [P])]
    norm_num
  exact_mod_cast key

/-- The two table constants are coherent:  ⟪D2⟫ = 2 · ⟪D⟫.

    MATH:  EDWARDS_D = ok D and EDWARDS_D2 = ok D2  ==>  ⟪D2⟫ = 2·⟪D⟫.
    Phrased over ANY successful evaluations (the constants are
    deterministic, so D/D2 are forced to the spec witnesses).
    PROOF: both characterizations live over the invertible scalar 121666:
    121666·⟪D2⟫ = −243330 = 2·(−121665) = 2·(121666·⟪D⟫) = 121666·(2⟪D⟫),
    cancel 121666 (`c121666_ne_zero`).
    WHY NEEDED: the op-spec phase proves `to_projective_niels` (which
    multiplies by EDWARDS_D2) produces `IsNielsOf` facts; this lemma is the
    glue identifying the D2 table entry with "2·d" wherever the math layer
    speaks in terms of d alone. -/
theorem edwards_d2_eq_two_d {dfe d2 : Fe}
    (hd : backend.serial.u64.constants.EDWARDS_D = ok dfe)
    (hd2 : backend.serial.u64.constants.EDWARDS_D2 = ok d2) :
    ⟪d2⟫ = 2 * ⟪dfe⟫ := by
  -- materialize the spec witnesses and identify them with dfe/d2 (determinism)
  obtain ⟨d', hd', _, hdv⟩ := spec_exists edwards_d_spec
  obtain ⟨d2', hd2', _, hd2v⟩ := spec_exists edwards_d2_spec
  rw [hd'] at hd; cases hd
  rw [hd2'] at hd2; cases hd2
  -- compare the two characterizations over the common factor 121666
  have h : (121666 : Fp) * ⟪d2⟫ = (121666 : Fp) * (2 * ⟪dfe⟫) := by
    rw [hd2v, mul_left_comm, hdv]
    norm_num
  exact mul_left_cancel₀ c121666_ne_zero h

/-! ## 3. The identity constants

    Rust implements `traits::Identity` for each representation
    (curve_models.rs:229-264, edwards.rs:428-437); under Aeneas a Rust
    `fn identity()` becomes a 0-argument fallible computation built from the
    `ZERO`/`ONE` field constants, so each spec asserts TOTALITY (`= ok _`),
    VALIDITY (the predicates of §1 — in particular the Z ≠ 0 obligation the
    Rust code never states), and the DENOTATION: the neutral element of the
    Edwards group is the affine point (0, 1).

    The proofs run the constants via `run_zero`/`run_one` (FieldMain.lean)
    and evaluate the transpiled do-blocks on the resulting `ok` values. -/

/-- Rust: `impl Identity for ProjectivePoint` — (X:Y:Z) = (0:1:1),
    curve_models.rs:229-237; transpiled at gen/CurveField/Funs.lean:580.

    MATH:  identity = ok Pt,  ProjValid Pt,  (projX Pt, projY Pt) = (0, 1).
    (x = 0/1 = 0, y = 1/1 = 1 — the Edwards neutral point.) -/
theorem run_projective_identity :
    ∃ Pt : ProjPoint,
      backend.serial.curve_models.ProjectivePoint.Insts.Curve25519TraitsIdentity.identity
        = ok Pt ∧
      ProjValid Pt ∧ projX Pt = 0 ∧ projY Pt = 1 := by
  -- run the two field constants the do-block binds
  obtain ⟨z, hz, hzb, hz0⟩ := run_zero
  obtain ⟨o, ho, hob, ho1⟩ := run_one
  -- restate at the generated names (fe_zero/fe_one are reducible aliases)
  have hz' : backend.serial.u64.field.FieldElement51.ZERO = ok z := hz
  have ho' : backend.serial.u64.field.FieldElement51.ONE = ok o := ho
  refine ⟨⟨z, o, o⟩, ?_, ⟨hzb, hob, hob, ?_⟩, ?_, ?_⟩
  · -- totality: substitute the ok-values, the do-block reduces definitionally
    unfold backend.serial.curve_models.ProjectivePoint.Insts.Curve25519TraitsIdentity.identity
    rw [hz', ho']; rfl
  · -- Z ≠ 0:  ⟪Z⟫ = ⟪o⟫ = 1 ≠ 0
    show ⟪o⟫ ≠ 0
    rw [ho1]; exact one_ne_zero
  · -- x = ⟪z⟫/⟪o⟫ = 0/⟪o⟫ = 0
    show ⟪z⟫ / ⟪o⟫ = 0
    rw [hz0, zero_div]
  · -- y = ⟪o⟫/⟪o⟫ = 1/1 = 1
    show ⟪o⟫ / ⟪o⟫ = 1
    rw [ho1, div_one]

/-- Rust: `impl Identity for EdwardsPoint` — (X:Y:Z:T) = (0:1:1:0),
    edwards.rs:428-437; transpiled at gen/CurveField/Funs.lean:2998.

    MATH:  identity = ok E,  ExtValid E  (in particular the extended
    coherence X·Y = Z·T holds: 0·1 = 1·0),  (edX E, edY E) = (0, 1). -/
theorem run_edwards_identity :
    ∃ E : EdPoint,
      edwards.EdwardsPoint.Insts.Curve25519TraitsIdentity.identity = ok E ∧
      ExtValid E ∧ edX E = 0 ∧ edY E = 1 := by
  obtain ⟨z, hz, hzb, hz0⟩ := run_zero
  obtain ⟨o, ho, hob, ho1⟩ := run_one
  have hz' : backend.serial.u64.field.FieldElement51.ZERO = ok z := hz
  have ho' : backend.serial.u64.field.FieldElement51.ONE = ok o := ho
  refine ⟨⟨z, o, o, z⟩, ?_, ⟨hzb, hob, hob, hzb, ?_, ?_⟩, ?_, ?_⟩
  · unfold edwards.EdwardsPoint.Insts.Curve25519TraitsIdentity.identity
    rw [hz', ho']; rfl
  · -- Z ≠ 0
    show ⟪o⟫ ≠ 0
    rw [ho1]; exact one_ne_zero
  · -- coherence X·Y = Z·T:  ⟪z⟫·⟪o⟫ = ⟪o⟫·⟪z⟫ (commutativity, value-free)
    show ⟪z⟫ * ⟪o⟫ = ⟪o⟫ * ⟪z⟫
    ring
  · show ⟪z⟫ / ⟪o⟫ = 0
    rw [hz0, zero_div]
  · show ⟪o⟫ / ⟪o⟫ = 1
    rw [ho1, div_one]

/-- Rust: `impl Identity for AffineNielsPoint` — (y+x, y−x, 2dxy) = (1,1,0),
    curve_models.rs:256-264; transpiled at gen/CurveField/Funs.lean:636.

    MATH:  identity = ok N,  AffNielsValid N,  IsAffNielsOf N 0 1 —
    the cache of the neutral affine point (x,y) = (0,1):
    y+x = 1, y−x = 1, 2d·x·y = 0. -/
theorem run_affine_niels_identity :
    ∃ N : AffNiels,
      backend.serial.curve_models.AffineNielsPoint.Insts.Curve25519TraitsIdentity.identity
        = ok N ∧
      AffNielsValid N ∧ IsAffNielsOf N 0 1 := by
  obtain ⟨z, hz, hzb, hz0⟩ := run_zero
  obtain ⟨o, ho, hob, ho1⟩ := run_one
  have hz' : backend.serial.u64.field.FieldElement51.ZERO = ok z := hz
  have ho' : backend.serial.u64.field.FieldElement51.ONE = ok o := ho
  refine ⟨⟨o, o, z⟩, ?_,
          ⟨hob.mono (by norm_num), hob.mono (by norm_num), hzb⟩, ?_, ?_, ?_⟩
  · unfold backend.serial.curve_models.AffineNielsPoint.Insts.Curve25519TraitsIdentity.identity
    rw [ho', hz']; rfl
  · -- ⟪y_plus_x⟫ = 1 + 0
    show ⟪o⟫ = 1 + 0
    rw [ho1]; norm_num
  · -- ⟪y_minus_x⟫ = 1 − 0
    show ⟪o⟫ = 1 - 0
    rw [ho1]; norm_num
  · -- 121666·⟪xy2d⟫ = −243330·(0·1):  both sides 0
    show (121666 : Fp) * ⟪z⟫ = -243330 * (0 * 1)
    rw [hz0]; ring

/-- Rust: `impl Identity for ProjectiveNielsPoint` —
    (Y+X, Y−X, Z, T2d) = (1, 1, 1, 0), curve_models.rs:239-248; transpiled
    at gen/CurveField/Funs.lean:599.

    MATH:  both identities run, ProjNielsValid N, and N IS the niels cache
    of the extended identity:  IsNielsOf N E
    (Y+X = 1+0, Y−X = 1−0, Z = 1, 121666·0 = −243330·0).
    Stated jointly with the EdwardsPoint identity so the relational
    denotation `IsNielsOf` has its reference point in hand. -/
theorem run_projective_niels_identity :
    ∃ (N : ProjNiels) (E : EdPoint),
      backend.serial.curve_models.ProjectiveNielsPoint.Insts.Curve25519TraitsIdentity.identity
        = ok N ∧
      edwards.EdwardsPoint.Insts.Curve25519TraitsIdentity.identity = ok E ∧
      ProjNielsValid N ∧ IsNielsOf N E := by
  obtain ⟨z, hz, hzb, hz0⟩ := run_zero
  obtain ⟨o, ho, hob, ho1⟩ := run_one
  have hz' : backend.serial.u64.field.FieldElement51.ZERO = ok z := hz
  have ho' : backend.serial.u64.field.FieldElement51.ONE = ok o := ho
  refine ⟨⟨o, o, o, z⟩, ⟨z, o, o, z⟩, ?_, ?_,
          ⟨hob.mono (by norm_num), hob.mono (by norm_num), hob, hzb, ?_⟩,
          ?_, ?_, ?_, ?_⟩
  · unfold backend.serial.curve_models.ProjectiveNielsPoint.Insts.Curve25519TraitsIdentity.identity
    rw [ho', hz']; rfl
  · unfold edwards.EdwardsPoint.Insts.Curve25519TraitsIdentity.identity
    rw [hz', ho']; rfl
  · -- ⟪Z⟫ = 1 ≠ 0
    show ⟪o⟫ ≠ 0
    rw [ho1]; exact one_ne_zero
  · -- ⟪Y_plus_X⟫ = ⟪E.Y⟫ + ⟪E.X⟫:  1 = 1 + 0
    show ⟪o⟫ = ⟪o⟫ + ⟪z⟫
    rw [hz0]; ring
  · -- ⟪Y_minus_X⟫ = ⟪E.Y⟫ − ⟪E.X⟫:  1 = 1 − 0
    show ⟪o⟫ = ⟪o⟫ - ⟪z⟫
    rw [hz0]; ring
  · -- ⟪Z⟫ = ⟪E.Z⟫
    show ⟪o⟫ = ⟪o⟫
    rfl
  · -- 121666·⟪T2d⟫ = −243330·⟪E.T⟫:  both sides 0 (⟪z⟫ = 0)
    show (121666 : Fp) * ⟪z⟫ = -243330 * ⟪z⟫
    rw [hz0]; ring

/-! ## 4. Helpers for the op-spec phase

    Division-equation rewrites for the coordinate algebra (every point
    equation lives over the denominators Z, T, 2Z), a determinism
    extractor, and constructor-projection conveniences.  All thin wrappers,
    named and collected here so the op-spec files read uniformly. -/

/-- MATH:  b ≠ 0  ==>  (a / b = c  ↔  a = c·b)  in 𝔽_p.
    WHY NEEDED: turns coordinate goals like `edX P = x` (a division) into
    denominator-free multiplications that `ring` can chew on — the standard
    `field_simp` step, packaged for one denominator. -/
theorem fp_div_eq_iff {a b c : Fp} (hb : b ≠ 0) : a / b = c ↔ a = c * b :=
  div_eq_iff hb

/-- MATH:  b ≠ 0  ==>  (c = a / b  ↔  c·b = a)  in 𝔽_p (mirror image). -/
theorem fp_eq_div_iff {a b c : Fp} (hb : b ≠ 0) : c = a / b ↔ c * b = a :=
  eq_div_iff hb

/-- MATH:  b ≠ 0, d ≠ 0  ==>  (a/b = c/d  ↔  a·d = c·b)  in 𝔽_p.
    WHY NEEDED: comparing two projective representations of the same affine
    coordinate (e.g. output of `to_extended` against the input point)
    cross-multiplies exactly like this. -/
theorem fp_div_eq_div_iff {a b c d : Fp} (hb : b ≠ 0) (hd : d ≠ 0) :
    a / b = c / d ↔ a * d = c * b :=
  div_eq_div_iff hb hd

/-- MATH:  a ≠ 0  ==>  2·a ≠ 0  in 𝔽_p  (char 𝔽_p ≠ 2, `two_ne_zero'`).
    WHY NEEDED: the niels recombination denominator is 2·⟪Z⟫. -/
theorem two_mul_ne_zero {a : Fp} (ha : a ≠ 0) : 2 * a ≠ 0 :=
  mul_ne_zero two_ne_zero' ha

/-- Determinism extractor.

    MATH:  x = ok a  and  x = ok b  ==>  a = b   (a `Result` computation is
    a value, not a relation — two successful runs agree).
    WHY NEEDED: op-spec proofs constantly match a hypothesis `f p = ok r`
    (from an unfolded caller) against a `run_*`/spec witness `f p = ok r'`
    to transport facts about r' to r.  (The `rw …; cases …` idiom of
    FieldMain.lean, packaged.) -/
theorem ok_ext {α} {x : Result α} {a b : α} (h1 : x = ok a) (h2 : x = ok b) :
    a = b := by
  rw [h1] at h2
  cases h2
  rfl

/-! Constructor-projection ("denote-of-pair") conveniences: once a point is
    exhibited as a literal `⟨…⟩`, its fields are the components — `rfl`, but
    naming them lets op-spec proofs rewrite without `show`-blocks.  Marked
    `@[simp]` so `simp` collapses projections of freshly built points. -/

@[simp] theorem EdPoint.mk_X (x y z t : Fe) : (edwards.EdwardsPoint.mk x y z t).X = x := rfl
@[simp] theorem EdPoint.mk_Y (x y z t : Fe) : (edwards.EdwardsPoint.mk x y z t).Y = y := rfl
@[simp] theorem EdPoint.mk_Z (x y z t : Fe) : (edwards.EdwardsPoint.mk x y z t).Z = z := rfl
@[simp] theorem EdPoint.mk_T (x y z t : Fe) : (edwards.EdwardsPoint.mk x y z t).T = t := rfl

@[simp] theorem ProjPoint.mk_X (x y z : Fe) :
    (backend.serial.curve_models.ProjectivePoint.mk x y z).X = x := rfl
@[simp] theorem ProjPoint.mk_Y (x y z : Fe) :
    (backend.serial.curve_models.ProjectivePoint.mk x y z).Y = y := rfl
@[simp] theorem ProjPoint.mk_Z (x y z : Fe) :
    (backend.serial.curve_models.ProjectivePoint.mk x y z).Z = z := rfl

@[simp] theorem ComplPoint.mk_X (x y z t : Fe) :
    (backend.serial.curve_models.CompletedPoint.mk x y z t).X = x := rfl
@[simp] theorem ComplPoint.mk_Y (x y z t : Fe) :
    (backend.serial.curve_models.CompletedPoint.mk x y z t).Y = y := rfl
@[simp] theorem ComplPoint.mk_Z (x y z t : Fe) :
    (backend.serial.curve_models.CompletedPoint.mk x y z t).Z = z := rfl
@[simp] theorem ComplPoint.mk_T (x y z t : Fe) :
    (backend.serial.curve_models.CompletedPoint.mk x y z t).T = t := rfl

@[simp] theorem ProjNiels.mk_Y_plus_X (a b c d : Fe) :
    (backend.serial.curve_models.ProjectiveNielsPoint.mk a b c d).Y_plus_X = a := rfl
@[simp] theorem ProjNiels.mk_Y_minus_X (a b c d : Fe) :
    (backend.serial.curve_models.ProjectiveNielsPoint.mk a b c d).Y_minus_X = b := rfl
@[simp] theorem ProjNiels.mk_Z (a b c d : Fe) :
    (backend.serial.curve_models.ProjectiveNielsPoint.mk a b c d).Z = c := rfl
@[simp] theorem ProjNiels.mk_T2d (a b c d : Fe) :
    (backend.serial.curve_models.ProjectiveNielsPoint.mk a b c d).T2d = d := rfl

@[simp] theorem AffNiels.mk_y_plus_x (a b c : Fe) :
    (backend.serial.curve_models.AffineNielsPoint.mk a b c).y_plus_x = a := rfl
@[simp] theorem AffNiels.mk_y_minus_x (a b c : Fe) :
    (backend.serial.curve_models.AffineNielsPoint.mk a b c).y_minus_x = b := rfl
@[simp] theorem AffNiels.mk_xy2d (a b c : Fe) :
    (backend.serial.curve_models.AffineNielsPoint.mk a b c).xy2d = c := rfl

end CurveFieldProofs
