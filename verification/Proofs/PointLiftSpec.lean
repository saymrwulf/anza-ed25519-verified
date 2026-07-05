/- ──────────────────────────────────────────────────────────────────────────────
   Proofs/PointLiftSpec.lean — phase 2, the half-lift toward the point-level
   verification equation.

   This file assembles the connective tissue between the byte-level apex
   (SigApexSpec: accept ⇔ byte equality) and the denoted-point world:

   1. `vartime_dsm_basepoint_spec` — the public dsm entry is its serial
      implementation (the backend dispatch is REAL code under the serial
      pin: get_selected_backend = ok .Serial), so the dsm certificate
      transfers to the function the verifier actually calls.
   2. `bytesVal_inj` / `rangeEq_iff_bytesVal` — the byte-wise comparison the
      verifier performs is exactly value equality of the two encodings
      (little-endian digits are unique: peel one byte at a time).

   The recompute-chain inversion and the half-lift theorem itself build on
   these in the sequel (the sha calls are oracles — axioms cannot be walked,
   so the chain is INVERTED from the `hrec` hypothesis the apex already
   carries, exactly as the apex itself is hypothesis-parametric).
   ────────────────────────────────────────────────────────────────────────────── -/
import Proofs.CompressSpec
import Proofs.ScalarPackSpec
import Proofs.DsmMulSpec
import Proofs.SigApexSpec
open Aeneas Aeneas.Std Result
open curve25519

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000

namespace CurveFieldProofs

open Aeneas.Std.WP

/-- **The public dsm entry satisfies the dsm certificate**: the backend
    dispatch is the real constant Serial (no axiom), so
    `vartime_double_scalar_mul_basepoint` IS the certified serial path. -/
theorem vartime_dsm_basepoint_spec
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
    edwards.EdwardsPoint.vartime_double_scalar_mul_basepoint a A b ⦃ R =>
      ExtValid R ∧ OnCurveExt R ∧
      ∃ (na nb : Std.Array Std.I8 256#usize),
        NafDigits na ∧ NafDigits nb ∧
        nafSum na 256 = (Va : ℤ) ∧ nafSum nb 256 = (Vb : ℤ) ∧
        edPt R = dsmFold (nafDigit na) (nafDigit nb) (edPt A) edBasePt edId 256 ⦄ := by
  unfold edwards.EdwardsPoint.vartime_double_scalar_mul_basepoint
    backend.vartime_double_base_mul backend.get_selected_backend
  simp only [bind_tc_ok]
  exact vartime_double_base_mul_spec a b A
    a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31
    b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31
    hab hbb Va Vb hVa hVb hValt hVblt hAv hAc

/-- One digit-peeling step: equal little-endian values with byte-sized heads
    force equal heads and equal tails. -/
theorem byte_peel {b c X Y : ℕ} (hb : b < 2^8) (hc : c < 2^8)
    (h : b + 2^8 * X = c + 2^8 * Y) : b = c ∧ X = Y := by
  omega

/-- **Little-endian digits are unique**: equal `bytesVal` forces equal byte
    arrays, hence the verifier's byte-wise comparison IS value equality. -/
theorem rangeEq_iff_bytesVal (e r : Std.Array Std.U8 32#usize) :
    rangeEq e r 0 ↔ bytesVal e = bytesVal r := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15,
    e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30, e31,
    hel⟩ := Bytes32.exists_bytes e
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15,
    r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31,
    hrl⟩ := Bytes32.exists_bytes r
  constructor
  · -- pointwise equality ⇒ equal sums
    intro h
    have hpt : ∀ j, j < 32 → e.val[j]! = r.val[j]! := fun j hj => h j (Nat.zero_le _) hj
    have h0 : e0 = r0 := by simpa [hel, hrl] using hpt 0 (by norm_num)
    have h1 : e1 = r1 := by simpa [hel, hrl] using hpt 1 (by norm_num)
    have h2 : e2 = r2 := by simpa [hel, hrl] using hpt 2 (by norm_num)
    have h3 : e3 = r3 := by simpa [hel, hrl] using hpt 3 (by norm_num)
    have h4 : e4 = r4 := by simpa [hel, hrl] using hpt 4 (by norm_num)
    have h5 : e5 = r5 := by simpa [hel, hrl] using hpt 5 (by norm_num)
    have h6 : e6 = r6 := by simpa [hel, hrl] using hpt 6 (by norm_num)
    have h7 : e7 = r7 := by simpa [hel, hrl] using hpt 7 (by norm_num)
    have h8 : e8 = r8 := by simpa [hel, hrl] using hpt 8 (by norm_num)
    have h9 : e9 = r9 := by simpa [hel, hrl] using hpt 9 (by norm_num)
    have h10 : e10 = r10 := by simpa [hel, hrl] using hpt 10 (by norm_num)
    have h11 : e11 = r11 := by simpa [hel, hrl] using hpt 11 (by norm_num)
    have h12 : e12 = r12 := by simpa [hel, hrl] using hpt 12 (by norm_num)
    have h13 : e13 = r13 := by simpa [hel, hrl] using hpt 13 (by norm_num)
    have h14 : e14 = r14 := by simpa [hel, hrl] using hpt 14 (by norm_num)
    have h15 : e15 = r15 := by simpa [hel, hrl] using hpt 15 (by norm_num)
    have h16 : e16 = r16 := by simpa [hel, hrl] using hpt 16 (by norm_num)
    have h17 : e17 = r17 := by simpa [hel, hrl] using hpt 17 (by norm_num)
    have h18 : e18 = r18 := by simpa [hel, hrl] using hpt 18 (by norm_num)
    have h19 : e19 = r19 := by simpa [hel, hrl] using hpt 19 (by norm_num)
    have h20 : e20 = r20 := by simpa [hel, hrl] using hpt 20 (by norm_num)
    have h21 : e21 = r21 := by simpa [hel, hrl] using hpt 21 (by norm_num)
    have h22 : e22 = r22 := by simpa [hel, hrl] using hpt 22 (by norm_num)
    have h23 : e23 = r23 := by simpa [hel, hrl] using hpt 23 (by norm_num)
    have h24 : e24 = r24 := by simpa [hel, hrl] using hpt 24 (by norm_num)
    have h25 : e25 = r25 := by simpa [hel, hrl] using hpt 25 (by norm_num)
    have h26 : e26 = r26 := by simpa [hel, hrl] using hpt 26 (by norm_num)
    have h27 : e27 = r27 := by simpa [hel, hrl] using hpt 27 (by norm_num)
    have h28 : e28 = r28 := by simpa [hel, hrl] using hpt 28 (by norm_num)
    have h29 : e29 = r29 := by simpa [hel, hrl] using hpt 29 (by norm_num)
    have h30 : e30 = r30 := by simpa [hel, hrl] using hpt 30 (by norm_num)
    have h31 : e31 = r31 := by simpa [hel, hrl] using hpt 31 (by norm_num)
    simp only [bytesVal, hel, hrl, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31]
  · -- equal sums ⇒ pointwise equality: peel 32 bytes
    intro h
    simp only [bytesVal, hel, hrl] at h
    intro j hj0 hj32
    simp only [hel, hrl]
    -- normalize both sums into head + 2^8·tail form, peel, recurse
    have hb : ∀ x : Std.U8, x.val < 2^8 := fun x => by scalar_tac
    have hpeel : e0.val = r0.val ∧ e1.val = r1.val ∧ e2.val = r2.val ∧
        e3.val = r3.val ∧ e4.val = r4.val ∧ e5.val = r5.val ∧
        e6.val = r6.val ∧ e7.val = r7.val ∧ e8.val = r8.val ∧
        e9.val = r9.val ∧ e10.val = r10.val ∧ e11.val = r11.val ∧
        e12.val = r12.val ∧ e13.val = r13.val ∧ e14.val = r14.val ∧
        e15.val = r15.val ∧ e16.val = r16.val ∧ e17.val = r17.val ∧
        e18.val = r18.val ∧ e19.val = r19.val ∧ e20.val = r20.val ∧
        e21.val = r21.val ∧ e22.val = r22.val ∧ e23.val = r23.val ∧
        e24.val = r24.val ∧ e25.val = r25.val ∧ e26.val = r26.val ∧
        e27.val = r27.val ∧ e28.val = r28.val ∧ e29.val = r29.val ∧
        e30.val = r30.val ∧ e31.val = r31.val := by
      have hbe0 := hb e0; have hbr0 := hb r0
      have hbe1 := hb e1; have hbr1 := hb r1
      have hbe2 := hb e2; have hbr2 := hb r2
      have hbe3 := hb e3; have hbr3 := hb r3
      have hbe4 := hb e4; have hbr4 := hb r4
      have hbe5 := hb e5; have hbr5 := hb r5
      have hbe6 := hb e6; have hbr6 := hb r6
      have hbe7 := hb e7; have hbr7 := hb r7
      have hbe8 := hb e8; have hbr8 := hb r8
      have hbe9 := hb e9; have hbr9 := hb r9
      have hbe10 := hb e10; have hbr10 := hb r10
      have hbe11 := hb e11; have hbr11 := hb r11
      have hbe12 := hb e12; have hbr12 := hb r12
      have hbe13 := hb e13; have hbr13 := hb r13
      have hbe14 := hb e14; have hbr14 := hb r14
      have hbe15 := hb e15; have hbr15 := hb r15
      have hbe16 := hb e16; have hbr16 := hb r16
      have hbe17 := hb e17; have hbr17 := hb r17
      have hbe18 := hb e18; have hbr18 := hb r18
      have hbe19 := hb e19; have hbr19 := hb r19
      have hbe20 := hb e20; have hbr20 := hb r20
      have hbe21 := hb e21; have hbr21 := hb r21
      have hbe22 := hb e22; have hbr22 := hb r22
      have hbe23 := hb e23; have hbr23 := hb r23
      have hbe24 := hb e24; have hbr24 := hb r24
      have hbe25 := hb e25; have hbr25 := hb r25
      have hbe26 := hb e26; have hbr26 := hb r26
      have hbe27 := hb e27; have hbr27 := hb r27
      have hbe28 := hb e28; have hbr28 := hb r28
      have hbe29 := hb e29; have hbr29 := hb r29
      have hbe30 := hb e30; have hbr30 := hb r30
      have hbe31 := hb e31; have hbr31 := hb r31
      omega
    obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14,
      q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28,
      q29, q30, q31⟩ := hpeel
    -- j is one of 0..31: close each case with the matching byte equality
    interval_cases j <;> simp_all <;> exact UScalar.eq_of_val_eq (by assumption)

/-- List-level 32-destructure (helper for the 64-byte device). -/
theorem List.exists_len32 (l : List Std.U8) (h : l.length = 32) :
    ∃ (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 : Std.U8), l = [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31] := by
  match hl : l with
  | [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31] => exact ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31, rfl⟩
  | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] | [_,_,_,_,_] | [_,_,_,_,_,_] | [_,_,_,_,_,_,_] => simp [hl] at h
  | [_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] => simp [hl] at h
  | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] => simp [hl] at h
  | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] => simp [hl] at h
  | _::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_ => simp [hl] at h

/-- Destructuring device for 64-byte arrays (hash outputs): 32-cons prefix,
    then the list-level device on the tail. -/
theorem Bytes64.exists_bytes (s : Std.Array Std.U8 64#usize) :
    ∃ (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 c35 c36 c37 c38 c39 c40 c41 c42 c43 c44 c45 c46 c47 c48 c49 c50 c51 c52 c53 c54 c55 c56 c57 c58 c59 c60 c61 c62 c63 : Std.U8),
      (↑s : List Std.U8) = [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56, c57, c58, c59, c60, c61, c62, c63] := by
  have h : (↑s : List Std.U8).length = 64 := by
    have := s.property
    simp_all
  match hl : (↑s : List Std.U8) with
  | c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: c12 :: c13 :: c14 :: c15 :: c16 :: c17 :: c18 :: c19 :: c20 :: c21 :: c22 :: c23 :: c24 :: c25 :: c26 :: c27 :: c28 :: c29 :: c30 :: c31 :: rest =>
    have h2 : rest.length = 32 := by
      rw [hl] at h
      simp at h
      omega
    obtain ⟨c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56, c57, c58, c59, c60, c61, c62, c63, hr⟩ := List.exists_len32 rest h2
    exact ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56, c57, c58, c59, c60, c61, c62, c63, by rw [hr]⟩
  | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] | [_,_,_,_,_] | [_,_,_,_,_,_] | [_,_,_,_,_,_,_] => simp [hl] at h
  | [_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] => simp [hl] at h
  | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] => simp [hl] at h
  | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] => simp [hl] at h

/-- Generic ok-inversion of one monadic bind: a successful chain names the
    intermediate and its defining equation. -/
theorem bind_ok_inv {α β : Type} {e : Result α} {f : α → Result β} {b : β}
    (h : (do let x ← e; f x) = ok b) : ∃ a, e = ok a ∧ f a = ok b := by
  cases he : e with
  | ok v =>
    refine ⟨v, rfl, ?_⟩
    rw [he] at h
    simpa using h
  | fail err =>
    rw [he] at h
    simp [Bind.bind, Aeneas.Std.bind] at h
  | div =>
    rw [he] at h
    simp [Bind.bind, Aeneas.Std.bind] at h

/-- **Inversion of the recompute chain** (anza shape: the hash oracle is a
    single `sha512_hash3` call, `−A` is the STORED `minus_A` field — no
    negation call — and the scalar arrives already parsed). The two
    full-range slice reads are inverted anonymously alongside the oracle. -/
theorem recompute_inv (self : ed_sigs.verification_key.VerificationKey)
    (rb : Std.Array Std.U8 32#usize) (s : scalar.Scalar) (msg : Slice Std.U8)
    (er : edwards.CompressedEdwardsY)
    (hrec : ed_sigs.verification_key.VerificationKey.recompute_r_sha512 self rb s msg = ok er) :
    ∃ (hash : Std.Array Std.U8 64#usize) (k : scalar.Scalar) (ep : EdPoint),
      scalar.Scalar.from_bytes_mod_order_wide hash = ok k ∧
      edwards.EdwardsPoint.vartime_double_scalar_mul_basepoint k self.minus_A s = ok ep ∧
      edwards.EdwardsPoint.compress ep = ok er := by
  unfold ed_sigs.verification_key.VerificationKey.recompute_r_sha512 at hrec
  obtain ⟨s1, _, hrec⟩ := bind_ok_inv hrec
  obtain ⟨s2, _, hrec⟩ := bind_ok_inv hrec
  obtain ⟨hash, _, hrec⟩ := bind_ok_inv hrec
  obtain ⟨k, hk, hrec⟩ := bind_ok_inv hrec
  obtain ⟨ep, hep, hrec⟩ := bind_ok_inv hrec
  exact ⟨hash, k, ep, hk, hep, hrec⟩

open ed_sigs ed_sigs.verification_key in
/-- **THE HALF-LIFT (anza)**: under the apex's hypotheses plus validity of
    the stored `minus_A` and canonicity of the parsed scalar, the verifier
    accepts iff the signature's R bytes are the canonical encoding of the
    recomputed point R' = [k]·minus_A + [s]·B. -/
theorem verify_accepts_iff_point
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
    (hVslt : Vs < 2^253) :
    ∃ (R' : EdPoint), ExtValid R' ∧ OnCurveExt R' ∧
      (VerificationKey.verify_sha512 self sig msg = ok (core.result.Result.Ok ())
        ↔ bytesVal rb = (edY R').val + ((edX R').val % 2) * 2^255) := by
  obtain ⟨hash, k, ep, hk, hep, hcomp⟩ := recompute_inv self rb s msg er hrec
  -- k is canonical (< ℓ < 2²⁵³)
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56, c57, c58, c59, c60, c61, c62, c63, hhl⟩ := Bytes64.exists_bytes hash
  obtain ⟨k', hk', hkpost⟩ := spec_imp_exists
    (ScalarProofs.from_bytes_mod_order_wide_spec hash c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 c35 c36 c37 c38 c39 c40 c41 c42 c43 c44 c45 c46 c47 c48 c49 c50 c51 c52 c53 c54 c55 c56 c57 c58 c59 c60 c61 c62 c63 hhl _ rfl)
  rw [hk] at hk'
  have hkk : k = k' := by simpa using hk'
  subst hkk
  obtain ⟨hklt, -⟩ := hkpost
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, hkbl⟩ := Bytes32.exists_bytes k.bytes
  have hkval : bytesVal k.bytes = a0.val + a1.val * 2^8 + a2.val * 2^16 + a3.val * 2^24 + a4.val * 2^32 + a5.val * 2^40 + a6.val * 2^48 + a7.val * 2^56 + a8.val * 2^64 + a9.val * 2^72 + a10.val * 2^80 + a11.val * 2^88 + a12.val * 2^96 + a13.val * 2^104 + a14.val * 2^112 + a15.val * 2^120 + a16.val * 2^128 + a17.val * 2^136 + a18.val * 2^144 + a19.val * 2^152 + a20.val * 2^160 + a21.val * 2^168 + a22.val * 2^176 + a23.val * 2^184 + a24.val * 2^192 + a25.val * 2^200 + a26.val * 2^208 + a27.val * 2^216 + a28.val * 2^224 + a29.val * 2^232 + a30.val * 2^240 + a31.val * 2^248 := by
    simp only [bytesVal, hkbl]
  have hValt : (a0.val + a1.val * 2^8 + a2.val * 2^16 + a3.val * 2^24 + a4.val * 2^32 + a5.val * 2^40 + a6.val * 2^48 + a7.val * 2^56 + a8.val * 2^64 + a9.val * 2^72 + a10.val * 2^80 + a11.val * 2^88 + a12.val * 2^96 + a13.val * 2^104 + a14.val * 2^112 + a15.val * 2^120 + a16.val * 2^128 + a17.val * 2^136 + a18.val * 2^144 + a19.val * 2^152 + a20.val * 2^160 + a21.val * 2^168 + a22.val * 2^176 + a23.val * 2^184 + a24.val * 2^192 + a25.val * 2^200 + a26.val * 2^208 + a27.val * 2^216 + a28.val * 2^224 + a29.val * 2^232 + a30.val * 2^240 + a31.val * 2^248) < 2^253 := by
    have hEll : ScalarProofs.Ell < 2^253 := by unfold ScalarProofs.Ell; norm_num
    omega
  -- ep = [k]·minus_A + [s]·B, valid and on-curve
  obtain ⟨ep', hep', heppost⟩ := spec_imp_exists
    (vartime_dsm_basepoint_spec k s self.minus_A
      a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31
      hkbl hsbytes _ Vs rfl hVs hValt hVslt hkv hkc)
  rw [hep'] at hep
  have hee' : ep = ep' := by simpa using hep.symm
  subst hee'
  obtain ⟨hepv, hepc, -⟩ := heppost
  -- er is the canonical encoding of ep
  obtain ⟨er2, hcomp', hcpost⟩ := spec_imp_exists (ed_compress_spec ep hepv)
  rw [hcomp'] at hcomp
  have her : er = er2 := by simpa using hcomp.symm
  subst her
  -- e IS er (as_bytes is the identity)
  have hee : er = e := by
    have h0 : edwards.CompressedEdwardsY.as_bytes er = ok er := by
      simp [edwards.CompressedEdwardsY.as_bytes]
    rw [h0] at he
    simpa using he
  refine ⟨ep, hepv, hepc, ?_⟩
  rw [verify_accepts_iff self sig msg rb sb s er e hrb hsb hA hleg hs hrec he,
      rangeEq_iff_bytesVal, ← hee, hcpost]
  exact eq_comm

end CurveFieldProofs
