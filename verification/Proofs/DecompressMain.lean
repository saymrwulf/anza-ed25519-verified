/- ──────────────────────────────────────────────────────────────────────────────
   Proofs/DecompressMain.lean — phase 2, decompress step 3: THE CONSTRUCTIVE
   DECOMPRESSION THEOREM.

   `decompress_of_canonical`: for a valid on-curve point Q whose canonical
   encoding is the bytes rb, the extracted `CompressedEdwardsY::decompress`
   succeeds with `some P` — a valid on-curve point denoting exactly Q.

   The chain: from_bytes recovers the y-residue (the sign bit at 2²⁵⁵ is
   discarded — from_bytes_spec is exact below it); u = y²−1 and
   v = d·y²+1 are built by certified ops with ⟪EDWARDS_D⟫ = d
   (edwards_d_spec + edD_char, cancelled by 121666 ≠ 0); Q's own
   x-coordinate witnesses that u/v is a square (x_sq_of_onCurve), so
   sqrt_ratio_i succeeds with the even-parity root; the sign bit — Q's
   x-parity, extracted from byte 31 — selects between ±root, and the
   parity-injectivity argument (enc_inj_coord, on-curve invariance of x²)
   pins the selected root to edX Q. The result point {X, Y, 1, X·Y} is
   ExtValid, on-curve, and denotes Q.
   ────────────────────────────────────────────────────────────────────────────── -/
import Proofs.FromBytesSpec
open Aeneas Aeneas.Std Result
open curve25519

set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000

namespace CurveFieldProofs

open Aeneas.Std.WP

/-- ⟪EDWARDS_D⟫ is THE curve constant d. -/
theorem edwards_d_denote :
    backend.serial.u64.constants.EDWARDS_D ⦃ D => Bnd D (2^52) ∧ ⟪D⟫ = edD ⦄ := by
  apply spec_mono edwards_d_spec
  intro D ⟨hb, hd⟩
  refine ⟨hb, ?_⟩
  have h121666 : (121666 : Fp) ≠ 0 := by
    have h : ((121666 : ℕ) : Fp) ≠ 0 := natCast_ne_zero_of_mod (by decide)
    exact_mod_cast h
  have hchar := edD_char
  have : (121666 : Fp) * (⟪D⟫ - edD) = 0 := by linear_combination hd - hchar
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h h121666
  · linear_combination h

open ed_sigs ed_sigs.verification_key in
/-- **THE CONSTRUCTIVE DECOMPRESSION THEOREM**: canonical encodings of
    valid on-curve points decompress to them. -/
theorem decompress_of_canonical (Q : EdPoint) (hQv : ExtValid Q) (hQc : OnCurveExt Q)
    (rb : Std.Array Std.U8 32#usize)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 : Std.U8)
    (hbl : (↑rb : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31])
    (henc : bytesVal rb = (edY Q).val + ((edX Q).val % 2) * 2^255) :
    edwards.CompressedEdwardsY.decompress rb ⦃ o =>
      ∃ Pt : EdPoint, o = some Pt ∧ ExtValid Pt ∧ OnCurveExt Pt ∧ edPt Pt = edPt Q ⦄ := by
  haveI : NeZero P := ⟨by unfold P; norm_num⟩
  unfold edwards.CompressedEdwardsY.decompress curve25519.edwards.decompress.step_1
  -- as_bytes is the identity; parse y
  simp only [edwards.CompressedEdwardsY.as_bytes, bind_tc_ok]
  step with (from_bytes_spec rb b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
    b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 hbl)
    as ⟨Y, hbY, hYv⟩
  -- the parsed field element denotes edY Q
  have hyresid : (edY Q).val < 2^255 :=
    lt_of_lt_of_le (ZMod.val_lt _) (by unfold P; norm_num)
  have hparle : (edX Q).val % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
  have hYval : feVal Y = (edY Q).val := by
    rw [hYv, henc]
    have : ((edY Q).val + (edX Q).val % 2 * 2^255) % 2^255 = (edY Q).val := by
      rcases Nat.mod_two_eq_zero_or_one (edX Q).val with h | h <;> rw [h] <;> omega
    exact this
  have hYden : ⟪Y⟫ = edY Q := by
    apply ZMod.val_injective
    show (⟪Y⟫).val = (edY Q).val
    unfold denote
    rw [ZMod.val_natCast, hYval, Nat.mod_eq_of_lt (ZMod.val_lt _)]
  -- Z = 1
  step with one_spec as ⟨Z, hbZ, hZv⟩
  -- YY = y², u = y² − 1
  step with (square_spec' Y (Bnd.mono hbY (by norm_num))) as ⟨YY, hbYY, hYY⟩
  obtain ⟨yy0, yy1, yy2, yy3, yy4, hyyl⟩ := Fe.exists_limbs YY
  obtain ⟨z0, z1, z2, z3, z4, hzl⟩ := Fe.exists_limbs Z
  step with (sub_spec YY Z yy0 yy1 yy2 yy3 yy4 z0 z1 z2 z3 z4 hyyl hzl
    (Bnd.mono hbYY (by norm_num)) (Bnd.mono hbZ (by norm_num))) as ⟨u, hbu, huv⟩
  -- D, then v = d·y² + 1
  step with edwards_d_denote as ⟨D, hbD, hDv⟩
  step with (mul_spec' YY D (Bnd.mono hbYY (by norm_num)) (Bnd.mono hbD (by norm_num)))
    as ⟨vd, hbvd, hvd⟩
  step with (add_spec'' vd Z (Bnd.mono hbvd (by norm_num)) (Bnd.mono hbZ (by norm_num)))
    as ⟨v, hbv, hvv⟩
  -- interpreted u, v
  have huval : ⟪u⟫ = (edY Q)^2 - 1 := by
    rw [huv, hYY, hYden, hZv]
    ring
  have hvval : ⟪v⟫ = 1 + edD * (edY Q)^2 := by
    rw [hvv, hvd, hYY, hYden, hDv, hZv]
    ring
  -- Q's x witnesses the square; v never vanishes
  have hvne : ⟪v⟫ ≠ 0 := by rw [hvval]; exact one_add_d_y_sq_ne_zero _
  have hwit : (edX Q) ^ 2 * ⟪v⟫ = ⟪u⟫ := by
    rw [hvval, huval]
    exact x_sq_of_onCurve hQc
  -- the square root succeeds with the even-parity root
  step with (sqrt_ratio_i_sq_spec u v (Bnd.mono hbu (by norm_num))
    (Bnd.mono hbv (by norm_num)) hvne (edX Q) hwit) as ⟨sc, sr, hc1, hbr, hrsq, hrpar⟩
  -- the validity Choice converts to true
  simp only [core.convert.IntoFrom.into, Bool.Insts.CoreConvertFromChoice.from,
    bind_tc_ok]
  rw [show (sc.val != 0) = true from by simp [hc1]]
  rw [if_pos rfl]
  -- ── step_2: the sign select ──────────────────────────────────────────────
  unfold curve25519.edwards.decompress.step_2
  simp only [edwards.CompressedEdwardsY.as_bytes, bind_tc_ok]
  step as ⟨t31, ht31⟩
  simp [hbl] at ht31
  step as ⟨sgn, hsgn⟩
  simp only [subtle.Choice.Insts.CoreConvertFromU8.from, bind_tc_ok]
  -- the sign bit is Q's x-parity
  have hb31v : b31.val = (edY Q).val / 2^248 + ((edX Q).val % 2) * 2^7 := by
    have hexp : bytesVal rb = b0.val + b1.val * 2^8 + b2.val * 2^16 + b3.val * 2^24 + b4.val * 2^32 + b5.val * 2^40 + b6.val * 2^48 + b7.val * 2^56 + b8.val * 2^64 + b9.val * 2^72 + b10.val * 2^80 + b11.val * 2^88 + b12.val * 2^96 + b13.val * 2^104 + b14.val * 2^112 + b15.val * 2^120 + b16.val * 2^128 + b17.val * 2^136 + b18.val * 2^144 + b19.val * 2^152 + b20.val * 2^160 + b21.val * 2^168 + b22.val * 2^176 + b23.val * 2^184 + b24.val * 2^192 + b25.val * 2^200 + b26.val * 2^208 + b27.val * 2^216 + b28.val * 2^224 + b29.val * 2^232 + b30.val * 2^240 + b31.val * 2^248 := by
      simp only [bytesVal, hbl]
    rw [henc] at hexp
    have hB0 : b0.val < 256 := by scalar_tac
    have hB1 : b1.val < 256 := by scalar_tac
    have hB2 : b2.val < 256 := by scalar_tac
    have hB3 : b3.val < 256 := by scalar_tac
    have hB4 : b4.val < 256 := by scalar_tac
    have hB5 : b5.val < 256 := by scalar_tac
    have hB6 : b6.val < 256 := by scalar_tac
    have hB7 : b7.val < 256 := by scalar_tac
    have hB8 : b8.val < 256 := by scalar_tac
    have hB9 : b9.val < 256 := by scalar_tac
    have hB10 : b10.val < 256 := by scalar_tac
    have hB11 : b11.val < 256 := by scalar_tac
    have hB12 : b12.val < 256 := by scalar_tac
    have hB13 : b13.val < 256 := by scalar_tac
    have hB14 : b14.val < 256 := by scalar_tac
    have hB15 : b15.val < 256 := by scalar_tac
    have hB16 : b16.val < 256 := by scalar_tac
    have hB17 : b17.val < 256 := by scalar_tac
    have hB18 : b18.val < 256 := by scalar_tac
    have hB19 : b19.val < 256 := by scalar_tac
    have hB20 : b20.val < 256 := by scalar_tac
    have hB21 : b21.val < 256 := by scalar_tac
    have hB22 : b22.val < 256 := by scalar_tac
    have hB23 : b23.val < 256 := by scalar_tac
    have hB24 : b24.val < 256 := by scalar_tac
    have hB25 : b25.val < 256 := by scalar_tac
    have hB26 : b26.val < 256 := by scalar_tac
    have hB27 : b27.val < 256 := by scalar_tac
    have hB28 : b28.val < 256 := by scalar_tac
    have hB29 : b29.val < 256 := by scalar_tac
    have hB30 : b30.val < 256 := by scalar_tac
    have hB31 : b31.val < 256 := by scalar_tac
    omega
  have hsgnv : sgn.val = (edX Q).val % 2 := by
    rw [hsgn, ht31, nat_shr, hb31v]
    have : (edY Q).val / 2^248 < 2^7 := by
      have := hyresid
      omega
    omega
  -- −root, then select
  obtain ⟨r0, r1, r2, r3, r4, hrl⟩ := Fe.exists_limbs sr
  unfold Shared0FieldElement51.Insts.CoreOpsArithNegFieldElement51.neg
  step with (neg_spec sr r0 r1 r2 r3 r4 hrl (Bnd.mono hbr (by norm_num)))
    as ⟨Xn, hbXn, hXnv⟩
  obtain ⟨n0, n1, n2, n3, n4, hnl⟩ := Fe.exists_limbs Xn
  step with (fe_cond_assign_spec sr Xn sgn r0 r1 r2 r3 r4 n0 n1 n2 n3 n4 hrl hnl)
    as ⟨X1, hX1l⟩
  -- Bnd X1 first (needed by the T-multiply)
  have hbX1 : Bnd X1 (2^52) := by
    have hb1 : Bnd sr (2^52) := hbr
    have hb2 : Bnd Xn (2^52) := hbXn
    split at hX1l
    · rw [Bnd_eq X1 r0 r1 r2 r3 r4 _ (by rw [hX1l])]
      rw [Bnd_eq sr r0 r1 r2 r3 r4 _ hrl] at hb1
      exact hb1
    · rw [Bnd_eq X1 n0 n1 n2 n3 n4 _ (by rw [hX1l])]
      rw [Bnd_eq Xn n0 n1 n2 n3 n4 _ hnl] at hb2
      exact hb2
  -- T = X1·Y
  step with (mul_spec' X1 Y (Bnd.mono hbX1 (by norm_num)) (Bnd.mono hbY (by norm_num)))
    as ⟨T, hbT, hTv⟩
  try simp only [spec_ok]
  -- ── the selected root IS edX Q ───────────────────────────────────────────
  -- the root is on-curve (only x² appears in the equation)
  have hrsq' : ⟪sr⟫ ^ 2 = (edX Q) ^ 2 := by
    have h := hrsq
    rw [hwit.symm] at h
    have hcancel : (⟪sr⟫ ^ 2 - (edX Q) ^ 2) * ⟪v⟫ = 0 := by linear_combination h
    rcases mul_eq_zero.mp hcancel with h' | h'
    · linear_combination h'
    · exact absurd h' hvne
  have hronc : OnCurve ⟪sr⟫ (edY Q) := by
    show -(⟪sr⟫^2) + (edY Q)^2 = 1 + edD * ⟪sr⟫^2 * (edY Q)^2
    rw [hrsq']
    exact hQc
  have hX1den : ⟪X1⟫ = ⟪sr⟫ ∨ ⟪X1⟫ = -⟪sr⟫ := by
    split at hX1l
    · left
      unfold denote
      rw [feVal_eq X1 r0 r1 r2 r3 r4 (by rw [hX1l]),
          feVal_eq sr r0 r1 r2 r3 r4 hrl]
    · right
      have : ⟪X1⟫ = ⟪Xn⟫ := by
        unfold denote
        rw [feVal_eq X1 n0 n1 n2 n3 n4 (by rw [hX1l]),
            feVal_eq Xn n0 n1 n2 n3 n4 hnl]
      rw [this, hXnv]
  have hX1x : ⟪X1⟫ = edX Q := by
    rcases Nat.mod_two_eq_zero_or_one (edX Q).val with hx | hx
    · -- x has even parity: no flip (sgn = 0), root already matches by parity
      have hs0 : sgn.val = 0 := by rw [hsgnv, hx]
      have hkeep : ⟪X1⟫ = ⟪sr⟫ := by
        split at hX1l
        · unfold denote
          rw [feVal_eq X1 r0 r1 r2 r3 r4 (by rw [hX1l]),
              feVal_eq sr r0 r1 r2 r3 r4 hrl]
        · exact absurd hs0 (by assumption)
      rw [hkeep]
      exact enc_inj_coord hronc hQc (by rw [hrpar, hx])
    · -- x odd: the flip fires; −root has odd parity (root even, nonzero)
      have hs1 : sgn.val ≠ 0 := by rw [hsgnv, hx]; norm_num
      have hflip : ⟪X1⟫ = -⟪sr⟫ := by
        split at hX1l
        · exact absurd (by assumption) hs1
        · have : ⟪X1⟫ = ⟪Xn⟫ := by
            unfold denote
            rw [feVal_eq X1 n0 n1 n2 n3 n4 (by rw [hX1l]),
                feVal_eq Xn n0 n1 n2 n3 n4 hnl]
          rw [this, hXnv]
      have hrnz : ⟪sr⟫ ≠ 0 := by
        intro hz
        rw [hz] at hrsq'
        have hxz : edX Q = 0 := by
          have := hrsq'.symm
          have h2 : (edX Q)^2 = 0 := by linear_combination -hrsq'
          exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
        rw [hxz] at hx
        simp at hx
      have hnegonc : OnCurve (-⟪sr⟫) (edY Q) := by
        show -((-⟪sr⟫)^2) + (edY Q)^2 = 1 + edD * (-⟪sr⟫)^2 * (edY Q)^2
        have : (-⟪sr⟫)^2 = ⟪sr⟫^2 := by ring
        rw [this, hrsq']
        exact hQc
      have hnegpar : (-⟪sr⟫).val % 2 = 1 := by
        rw [ZMod.neg_val, if_neg hrnz]
        have hlt := ZMod.val_lt ⟪sr⟫
        have hpodd : P % 2 = 1 := by unfold P; norm_num
        have hpos : 0 < (⟪sr⟫).val := by
          rcases Nat.eq_zero_or_pos (⟪sr⟫).val with h | h
          · exact absurd ((ZMod.val_eq_zero _).mp h) hrnz
          · exact h
        omega
      rw [hflip]
      exact enc_inj_coord hnegonc hQc (by rw [hnegpar, hx])
  -- ── assemble the point ───────────────────────────────────────────────────
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · -- ExtValid
    refine ⟨?_, Bnd.mono hbY (by norm_num), Bnd.mono hbZ (by norm_num), ?_, ?_, ?_⟩
    · exact hbX1
    · exact Bnd.mono hbT (by norm_num)
    · rw [hZv]; norm_num
    · -- coherence X·Y = Z·T
      show ⟪X1⟫ * ⟪Y⟫ = ⟪Z⟫ * ⟪T⟫
      rw [hTv, hZv]
      ring
  · -- on-curve
    show OnCurve (⟪X1⟫ / ⟪Z⟫) (⟪Y⟫ / ⟪Z⟫)
    rw [hZv, div_one, div_one, hX1x, hYden]
    exact hQc
  · -- denotes Q
    show (⟪X1⟫ / ⟪Z⟫, ⟪Y⟫ / ⟪Z⟫) = edPt Q
    rw [hZv, div_one, div_one, hX1x, hYden]
    rfl

open ed_sigs ed_sigs.verification_key in
/-- **THE FULL POINT-LEVEL LIFT** (anza). Under the point-equation premises,
    the signature's R bytes DECOMPRESS to a valid on-curve point Pt, and the
    verifier accepts **iff** Pt equals the recomputed [k]·minus_A + [s]·B:

        accept   ⇔   decompress(R) = [k]·minus_A + [s]·B    (as points).

    This is the constructive capstone of phase 2: byte comparison ↔
    canonical-encoding equality ↔ point equality ↔ decompressed-point
    equality, every link machine-checked over the extracted code. -/
theorem verify_accepts_iff_decompress
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
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 : Std.U8)
    (hbl : (↑rb : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31])
    (henc : bytesVal rb = (edY Q).val + ((edX Q).val % 2) * 2^255) :
    ∃ (R' Pt : EdPoint), ExtValid R' ∧ OnCurveExt R' ∧
      curve25519.edwards.CompressedEdwardsY.decompress rb = ok (some Pt) ∧
      ExtValid Pt ∧ OnCurveExt Pt ∧
      (VerificationKey.verify_sha512 self sig msg = ok (core.result.Result.Ok ())
        ↔ edPt Pt = edPt R') := by
  obtain ⟨R', hRv, hRc, hiff⟩ := verify_accepts_iff_point_eq self sig msg rb sb s er e
    hrb hsb hA hleg hs hrec he hkv hkc
    t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 hsbytes Vs hVs hVslt Q hQv hQc henc
  obtain ⟨o, ho, Pt, hosome, hPv, hPc, hPQ⟩ := spec_imp_exists
    (decompress_of_canonical Q hQv hQc rb b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 hbl henc)
  refine ⟨R', Pt, hRv, hRc, ?_, hPv, hPc, ?_⟩
  · rw [ho, hosome]
  · rw [hiff, hPQ]

end CurveFieldProofs
