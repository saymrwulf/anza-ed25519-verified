/- ──────────────────────────────────────────────────────────────────────────────
   Proofs/DsmMulSpec.lean — double-scalar-mul campaign, brick 4:
   the basepoint constant and the public `vartime_double_base::mul` spec.

   · `run_basepoint` — the transpiled ED25519_BASEPOINT_POINT is a VALID
     extended point ON THE CURVE denoting the standard base point
         B = (x_B, y_B),  x_B = 15112…202,  y_B = 46316…960
     — kernel-checked literal arithmetic: the extended coherence X·Y = Z·T
     and the (121666-scaled, denominator-free) curve equation
         121666·y² + 121665·x²y² ≡ 121666 + 121666·x²  (mod p).
     A corrupted basepoint constant would be caught here.

   · `vartime_double_base_mul_spec` — THE PHASE-1 COMPUTATIONAL SPEC:
     for canonical scalars (byte values < 2^253) and a valid on-curve A,
     `mul a A b` returns a valid on-curve R with
         edPt R = dsmFold (digits of a) (digits of b) (edPt A) edBasePt edId 256
     where both digit arrays are proven NAF encodings of the scalars' exact
     byte values (existentially exposed with their NafDigits + nafSum facts).
     Composes non_adjacent_form_spec ×2, dsm_top_index_spec, naf_table_spec
     ×2 (A and the basepoint), dsm_loop_spec, proj_as_extended_spec.
     Phase 2 (reading dsmFold as [a]A + [b]B in the group) requires Edwards
     associativity — deliberately deferred and documented; nothing here
     assumes it.
   ────────────────────────────────────────────────────────────────────────────── -/
import Proofs.DsmNafSpec
open Aeneas Aeneas.Std Result ControlFlow
open curve25519

set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000
set_option exponentiation.threshold 600

namespace CurveFieldProofs

open Aeneas.Std.WP

/-- Generic mod-p witness → Fp product identity (abstract, no literal
    crunching during cast distribution). -/
theorem fp_mul_eq_of_witness (a b c : ℕ) (hmod : (a * b) % P = c % P) :
    (a : Fp) * (b : Fp) = (c : Fp) := by
  have h1 : ((a * b : ℕ) : Fp) = ((c : ℕ) : Fp) := by
    rw [← ZMod.natCast_mod, hmod, ZMod.natCast_mod]
  push_cast at h1
  exact h1

/-- Generic 121666-scaled curve-equation witness → OnCurve (abstract x, y). -/
theorem onCurve_of_witness (x y : ℕ)
    (hmod : (121666 * (y * y) + 121665 * (x * x) * (y * y)) % P
          = (121666 + 121666 * (x * x)) % P) :
    OnCurve (x : Fp) (y : Fp) := by
  have h1 : ((121666 * (y * y) + 121665 * (x * x) * (y * y) : ℕ) : Fp)
      = ((121666 + 121666 * (x * x) : ℕ) : Fp) := by
    rw [← ZMod.natCast_mod, hmod, ZMod.natCast_mod]
  push_cast at h1
  have h6 : (121666 : Fp) ≠ 0 := by
    have h : ((121666 : ℕ) : Fp) ≠ 0 := natCast_ne_zero_of_mod (by decide)
    simpa using h
  have hd := edD_char
  unfold OnCurve
  apply mul_left_cancel₀ h6
  linear_combination h1 - (x : Fp)^2 * (y : Fp)^2 * hd

/-- The standard Ed25519 base point, as ZMod literals. -/
noncomputable def edBasePt : Fp × Fp :=
  ((15112221349535400772501151409588531511454012693041857206046113283949847762202 : Fp),
   (46316835694926478169428394003475163141307993866256225615783033603165251855960 : Fp))

/-- **The transpiled basepoint constant is the standard base point** —
    valid, on-curve, kernel-audited literal arithmetic. -/
theorem run_basepoint :
    ∃ B : EdPoint,
      backend.serial.u64.constants.ED25519_BASEPOINT_POINT = ok B ∧
      ExtValid B ∧ OnCurveExt B ∧ edPt B = edBasePt := by
  -- the four coordinate denotations
  have hXv : ⟪(Array.make 5#usize [1738742601995546#u64, 1146398526822698#u64,
      2070867633025821#u64, 562264141797630#u64, 587772402128613#u64] :
      backend.serial.u64.field.FieldElement51)⟫ =
      (15112221349535400772501151409588531511454012693041857206046113283949847762202 : Fp) := by
    simp [denote, feVal, limbsVal, Array.make]
  have hYv : ⟪(Array.make 5#usize [1801439850948184#u64, 1351079888211148#u64,
      450359962737049#u64, 900719925474099#u64, 1801439850948198#u64] :
      backend.serial.u64.field.FieldElement51)⟫ =
      (46316835694926478169428394003475163141307993866256225615783033603165251855960 : Fp) := by
    simp [denote, feVal, limbsVal, Array.make]
  have hZv : ⟪(Array.make 5#usize [1#u64, 0#u64, 0#u64, 0#u64, 0#u64] :
      backend.serial.u64.field.FieldElement51)⟫ = (1 : Fp) := by
    simp [denote, feVal, limbsVal, Array.make]
  have hTv : ⟪(Array.make 5#usize [1841354044333475#u64, 16398895984059#u64,
      755974180946558#u64, 900171276175154#u64, 1821297809914039#u64] :
      backend.serial.u64.field.FieldElement51)⟫ =
      (46827403850823179245072216630277197565144205554125654976674165829533817101731 : Fp) := by
    simp [denote, feVal, limbsVal, Array.make]
  -- coherence of the affine literals: x·y = t (z = 1)
  have hco : (15112221349535400772501151409588531511454012693041857206046113283949847762202 : Fp) *
      (46316835694926478169428394003475163141307993866256225615783033603165251855960 : Fp) =
      (46827403850823179245072216630277197565144205554125654976674165829533817101731 : Fp) := by
    apply fp_mul_eq_of_witness
    norm_num [P]
  -- the curve equation for the affine literals (121666-scaled witness)
  have hcv : OnCurve
      (15112221349535400772501151409588531511454012693041857206046113283949847762202 : Fp)
      (46316835694926478169428394003475163141307993866256225615783033603165251855960 : Fp) := by
    have h := onCurve_of_witness
      15112221349535400772501151409588531511454012693041857206046113283949847762202
      46316835694926478169428394003475163141307993866256225615783033603165251855960
      (by norm_num [P])
    push_cast at h
    exact h
  refine ⟨⟨Array.make 5#usize [1738742601995546#u64, 1146398526822698#u64,
             2070867633025821#u64, 562264141797630#u64, 587772402128613#u64],
           Array.make 5#usize [1801439850948184#u64, 1351079888211148#u64,
             450359962737049#u64, 900719925474099#u64, 1801439850948198#u64],
           Array.make 5#usize [1#u64, 0#u64, 0#u64, 0#u64, 0#u64],
           Array.make 5#usize [1841354044333475#u64, 16398895984059#u64,
             755974180946558#u64, 900171276175154#u64, 1821297809914039#u64]⟩,
         ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · unfold backend.serial.u64.constants.ED25519_BASEPOINT_POINT
      backend.serial.u64.field.FieldElement51.from_limbs
    rfl
  · simp [Bnd, Array.make]
  · simp [Bnd, Array.make]
  · simp [Bnd, Array.make]
  · simp [Bnd, Array.make]
  · show ⟪_⟫ ≠ 0
    rw [hZv]; exact one_ne_zero
  · show ⟪_⟫ * ⟪_⟫ = ⟪_⟫ * ⟪_⟫
    rw [hXv, hYv, hZv, hTv, one_mul]
    exact hco
  · show OnCurve (edX _) (edY _)
    unfold edX edY
    simp only
    rw [hXv, hYv, hZv, div_one, div_one]
    exact hcv
  · show (edX _, edY _) = edBasePt
    unfold edX edY edBasePt
    simp only
    rw [hXv, hYv, hZv, div_one, div_one]

/-- **vartime_double_base::mul — the phase-1 computational specification.**
    For canonical scalars a, b (LE byte values Va, Vb < 2^253) and a valid
    on-curve A: the result is a valid on-curve point denoting the abstract
    double-and-add fold of the two proven NAF encodings over A and the
    standard base point. -/
theorem vartime_double_base_mul_spec
    (a b : scalar.Scalar) (A : EdPoint)
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 : Std.U8)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 : Std.U8)
    (hab : (↑a.bytes : List Std.U8) = [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31])
    (hbb : (↑b.bytes : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31])
    (Va Vb : ℕ)
    (hVa : Va = a0.val + a1.val * 2^8 + a2.val * 2^16 + a3.val * 2^24 + a4.val * 2^32 + a5.val * 2^40 + a6.val * 2^48 + a7.val * 2^56 + a8.val * 2^64 + a9.val * 2^72 + a10.val * 2^80 + a11.val * 2^88 + a12.val * 2^96 + a13.val * 2^104 + a14.val * 2^112 + a15.val * 2^120 + a16.val * 2^128 + a17.val * 2^136 + a18.val * 2^144 + a19.val * 2^152 + a20.val * 2^160 + a21.val * 2^168 + a22.val * 2^176 + a23.val * 2^184 + a24.val * 2^192 + a25.val * 2^200 + a26.val * 2^208 + a27.val * 2^216 + a28.val * 2^224 + a29.val * 2^232 + a30.val * 2^240 + a31.val * 2^248)
    (hVb : Vb = b0.val + b1.val * 2^8 + b2.val * 2^16 + b3.val * 2^24 + b4.val * 2^32 + b5.val * 2^40 + b6.val * 2^48 + b7.val * 2^56 + b8.val * 2^64 + b9.val * 2^72 + b10.val * 2^80 + b11.val * 2^88 + b12.val * 2^96 + b13.val * 2^104 + b14.val * 2^112 + b15.val * 2^120 + b16.val * 2^128 + b17.val * 2^136 + b18.val * 2^144 + b19.val * 2^152 + b20.val * 2^160 + b21.val * 2^168 + b22.val * 2^176 + b23.val * 2^184 + b24.val * 2^192 + b25.val * 2^200 + b26.val * 2^208 + b27.val * 2^216 + b28.val * 2^224 + b29.val * 2^232 + b30.val * 2^240 + b31.val * 2^248)
    (hValt : Va < 2^253) (hVblt : Vb < 2^253)
    (hAv : ExtValid A) (hAc : OnCurveExt A) :
    backend.serial.scalar_mul.vartime_double_base.mul a A b ⦃ R =>
      ExtValid R ∧ OnCurveExt R ∧
      ∃ (na nb : Std.Array Std.I8 256#usize),
        NafDigits na ∧ NafDigits nb ∧
        nafSum na 256 = (Va : ℤ) ∧ nafSum nb 256 = (Vb : ℤ) ∧
        edPt R = dsmFold (nafDigit na) (nafDigit nb) (edPt A) edBasePt edId 256 ⦄ := by
  obtain ⟨B, hBok, hBv, hBc, hBpt⟩ := run_basepoint
  unfold backend.serial.scalar_mul.vartime_double_base.mul
  -- the two NAF encodings
  step with (non_adjacent_form_spec a
    a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31
    hab Va hVa hValt) as ⟨na, hnaD, hnaS⟩
  step with (non_adjacent_form_spec b
    b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31
    hbb Vb hVb hVblt) as ⟨nb, hnbD, hnbS⟩
  -- the top index (constant 255)
  step with (dsm_top_index_spec na nb) as ⟨i, hi⟩
  -- table over A
  step with (naf_table_spec A hAv hAc) as
    ⟨eA0, eA1, eA2, eA3, eA4, eA5, eA6, eA7, ta, hlA, hA0, hA1, hA2, hA3, hA4, hA5, hA6, hA7⟩
  -- the basepoint constant
  rw [hBok]
  simp only [bind_tc_ok]
  -- table over B
  step with (naf_table_spec B hBv hBc) as
    ⟨eB0, eB1, eB2, eB3, eB4, eB5, eB6, eB7, tb, hlB, hB0, hB1, hB2, hB3, hB4, hB5, hB6, hB7⟩
  -- the 256-step Straus loop
  step with (dsm_loop_spec i (by rw [hi]; scalar_tac : i.val = 255) na nb ta tb A B
    ⟨eA0, eA1, eA2, eA3, eA4, eA5, eA6, eA7, hlA, hA0, hA1, hA2, hA3, hA4, hA5, hA6, hA7⟩
    ⟨eB0, eB1, eB2, eB3, eB4, eB5, eB6, eB7, hlB, hB0, hB1, hB2, hB3, hB4, hB5, hB6, hB7⟩
    hnaD hnbD) as ⟨r, hrv, hrc, hrfold⟩
  -- the final projective → extended conversion
  apply spec_mono (proj_as_extended_spec r hrv)
  rintro R ⟨hRv, -, -, -, -, hRx, hRy⟩
  refine ⟨hRv, ?_, na, nb, hnaD, hnbD, hnaS, hnbS, ?_⟩
  · show OnCurve (edX R) (edY R)
    rw [hRx, hRy]
    exact hrc
  · calc edPt R = (edX R, edY R) := rfl
      _ = (projX r, projY r) := by rw [hRx, hRy]
      _ = dsmFold (nafDigit na) (nafDigit nb) (edPt A) (edPt B) edId 256 := hrfold
      _ = dsmFold (nafDigit na) (nafDigit nb) (edPt A) edBasePt edId 256 := by
          rw [hBpt]

end CurveFieldProofs
