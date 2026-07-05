/- ──────────────────────────────────────────────────────────────────────────────
   Proofs/PointEqSpec.lean — phase 2, THE POINT-LEVEL VERIFICATION EQUATION.

   THE THEOREM (`verify_accepts_iff_point_eq`): under the half-lift's
   hypotheses, for ANY valid on-curve point Q whose canonical encoding is
   the signature's R bytes,

       verifier accepts   ⇔   Q = [k]·(−A) + [s]·B   (as denoted points).

   This closes the gap between "the bytes match" and "the points match"
   WITHOUT decompress: the canonical encoding (y-residue + x-parity bit)
   is INJECTIVE on curve points, because the curve equation determines
   x² from y — here is where the non-squareness of d (edD_not_square,
   the Bernstein–Lange completeness ingredient) does its second job:
   1 + d·y² can never vanish, so x² = (y²−1)/(1+d·y²) is well-defined —
   and the parity bit selects between the two roots (±x have different
   parities mod an odd prime, unless x = 0, where they coincide).

   Decompress (extracted this increment, proofs in the sequel) will add
   the CONSTRUCTIVE version: the accepted bytes decompress to the point.
   ────────────────────────────────────────────────────────────────────────────── -/
import Proofs.PointLiftSpec
open Aeneas Aeneas.Std Result
open curve25519

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace CurveFieldProofs

open Aeneas.Std.WP

/-- 1 + d·y² never vanishes: otherwise d = −(1/y)², and since −1 IS a
    square mod p (p ≡ 1 mod 4), d would be a square — contradicting
    `edD_not_square`. -/
theorem one_add_d_y_sq_ne_zero (y : Fp) : 1 + edD * y ^ 2 ≠ 0 := by
  intro h
  have hy : y ≠ 0 := by
    intro h0
    rw [h0] at h
    simp at h
  -- −1 is a square mod p: p % 4 = 1
  have hsq : IsSquare (-1 : Fp) := by
    rw [ZMod.exists_sq_eq_neg_one_iff]
    unfold P
    norm_num
  obtain ⟨i, hi⟩ := hsq
  -- d = −(y⁻¹)² = (i·y⁻¹)²
  apply edD_not_square
  refine ⟨i * y⁻¹, ?_⟩
  have hd : edD * y ^ 2 = -1 := by linear_combination h
  have hy2 : (y : Fp) ^ 2 ≠ 0 := pow_ne_zero 2 hy
  calc edD = edD * y ^ 2 * (y ^ 2)⁻¹ := by field_simp
    _ = -1 * (y ^ 2)⁻¹ := by rw [hd]
    _ = (i * i) * (y ^ 2)⁻¹ := by rw [← hi]
    _ = (i * y⁻¹) * (i * y⁻¹) := by
        field_simp

/-- On-curve x² is determined by y. -/
theorem x_sq_of_onCurve {x y : Fp} (h : OnCurve x y) :
    x ^ 2 * (1 + edD * y ^ 2) = y ^ 2 - 1 := by
  unfold OnCurve at h
  linear_combination -h

/-- **Canonical-encoding injectivity on the curve** (coordinate form):
    same y, same x-parity, both on-curve ⇒ same x. -/
theorem enc_inj_coord {x1 x2 y : Fp}
    (h1 : OnCurve x1 y) (h2 : OnCurve x2 y)
    (hpar : x1.val % 2 = x2.val % 2) : x1 = x2 := by
  haveI : NeZero P := ⟨by unfold P; norm_num⟩
  -- x1² = x2² from the curve equation (1 + d·y² is invertible)
  have hsq : x1 ^ 2 = x2 ^ 2 := by
    have e1 := x_sq_of_onCurve h1
    have e2 := x_sq_of_onCurve h2
    have hne := one_add_d_y_sq_ne_zero y
    have : (x1 ^ 2 - x2 ^ 2) * (1 + edD * y ^ 2) = 0 := by
      linear_combination e1 - e2
    rcases mul_eq_zero.mp this with h | h
    · linear_combination h
    · exact absurd h hne
  -- hence x1 = ±x2
  have hpm : x1 = x2 ∨ x1 = -x2 := by
    have : (x1 - x2) * (x1 + x2) = 0 := by ring_nf; linear_combination hsq
    rcases mul_eq_zero.mp this with h | h
    · left; linear_combination h
    · right; linear_combination h
  rcases hpm with h | h
  · exact h
  · -- x1 = −x2: parity separates them unless x2 = 0
    by_cases hz : x2 = 0
    · rw [h, hz]; simp
    · exfalso
      have hval : x1.val = P - x2.val := by
        rw [h, ZMod.neg_val, if_neg hz]
      have hlt : x2.val < P := ZMod.val_lt x2
      have hpos : 0 < x2.val := by
        rcases Nat.eq_zero_or_pos x2.val with h0 | h0
        · exact absurd ((ZMod.val_eq_zero x2).mp h0) hz
        · exact h0
      have hodd : P % 2 = 1 := by unfold P; norm_num
      omega

/-- **Canonical-encoding injectivity on points**: equal encodings of valid
    on-curve points force equal denoted points. -/
theorem enc_point_inj (Pt Q : EdPoint)
    (hPv : ExtValid Pt) (hPc : OnCurveExt Pt)
    (hQv : ExtValid Q) (hQc : OnCurveExt Q)
    (h : (edY Pt).val + ((edX Pt).val % 2) * 2^255
       = (edY Q).val + ((edX Q).val % 2) * 2^255) :
    edPt Pt = edPt Q := by
  haveI : NeZero P := ⟨by unfold P; norm_num⟩
  -- split the encoding: y-residues < p < 2²⁵⁵, parities ∈ {0,1}
  have hyP : (edY Pt).val < 2^255 :=
    lt_of_lt_of_le (ZMod.val_lt _) (by unfold P; norm_num)
  have hyQ : (edY Q).val < 2^255 :=
    lt_of_lt_of_le (ZMod.val_lt _) (by unfold P; norm_num)
  have hb1 := Nat.mod_two_eq_zero_or_one (edX Pt).val
  have hb2 := Nat.mod_two_eq_zero_or_one (edX Q).val
  have hkey : (edY Pt).val = (edY Q).val ∧ (edX Pt).val % 2 = (edX Q).val % 2 := by
    rcases hb1 with h1 | h1 <;> rcases hb2 with h2 | h2 <;>
      rw [h1, h2] at h <;> constructor <;> omega
  obtain ⟨hy, hpar⟩ := hkey
  have hyy : edY Pt = edY Q := ZMod.val_injective _ hy
  have hxx : edX Pt = edX Q := by
    apply enc_inj_coord (y := edY Q)
    · rw [← hyy]; exact hPc
    · exact hQc
    · exact hpar
  unfold edPt
  rw [hxx, hyy]

open ed_sigs ed_sigs.verification_key in
/-- **THE POINT-LEVEL VERIFICATION EQUATION** (anza). Under the half-lift's
    hypotheses, for any valid on-curve point Q whose canonical encoding is
    the signature's R bytes: the verifier accepts **iff** Q equals the
    recomputed point [k]·minus_A + [s]·B as denoted affine points. -/
theorem verify_accepts_iff_point_eq
    (self : verification_key.VerificationKey)
    (sig : ed25519.Signature) (msg : Slice Std.U8)
    (rb sb : Std.Array Std.U8 32#usize) (s : scalar.Scalar)
    (er : edwards.CompressedEdwardsY) (e : Std.Array Std.U8 32#usize)
    (hrb : ed25519.Signature.r_bytes sig = ok rb)
    (hsb : ed25519.Signature.s_bytes sig = ok sb)
    (hA : VerificationKey.a_bytes_nonzero self = ok true)
    (hleg : is_legacy_excluded_r rb = ok false)
    (hs : check_scalar_canonical sb = ok (core.result.Result.Ok s))
    (hrec : VerificationKey.recompute_r_sha512 self rb s msg = ok er)
    (he : edwards.CompressedEdwardsY.as_bytes er = ok e)
    (hkv : ExtValid self.minus_A) (hkc : OnCurveExt self.minus_A)
    (t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 : Std.U8)
    (hsbytes : (↑s.bytes : List Std.U8) = [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31])
    (Vs : ℕ) (hVs : Vs = t0.val + t1.val * 2^8 + t2.val * 2^16 + t3.val * 2^24 + t4.val * 2^32 + t5.val * 2^40 + t6.val * 2^48 + t7.val * 2^56 + t8.val * 2^64 + t9.val * 2^72 + t10.val * 2^80 + t11.val * 2^88 + t12.val * 2^96 + t13.val * 2^104 + t14.val * 2^112 + t15.val * 2^120 + t16.val * 2^128 + t17.val * 2^136 + t18.val * 2^144 + t19.val * 2^152 + t20.val * 2^160 + t21.val * 2^168 + t22.val * 2^176 + t23.val * 2^184 + t24.val * 2^192 + t25.val * 2^200 + t26.val * 2^208 + t27.val * 2^216 + t28.val * 2^224 + t29.val * 2^232 + t30.val * 2^240 + t31.val * 2^248)
    (hVslt : Vs < 2^253)
    (Q : EdPoint) (hQv : ExtValid Q) (hQc : OnCurveExt Q)
    (henc : bytesVal rb = (edY Q).val + ((edX Q).val % 2) * 2^255) :
    ∃ (R' : EdPoint), ExtValid R' ∧ OnCurveExt R' ∧
      (VerificationKey.verify_sha512 self sig msg = ok (core.result.Result.Ok ())
        ↔ edPt Q = edPt R') := by
  obtain ⟨R', hRv, hRc, hiff⟩ := verify_accepts_iff_point self sig msg rb sb s er e
    hrb hsb hA hleg hs hrec he hkv hkc
    t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 hsbytes Vs hVs hVslt
  refine ⟨R', hRv, hRc, ?_⟩
  rw [hiff]
  constructor
  · intro h
    exact enc_point_inj Q R' hQv hQc hRv hRc (by rw [← henc, h])
  · intro h
    have hx : edX Q = edX R' := congrArg Prod.fst h
    have hy : edY Q = edY R' := congrArg Prod.snd h
    rw [henc, hx, hy]

end CurveFieldProofs
