/- ──────────────────────────────────────────────────────────────────────────────
   Proofs/CompressSpec.lean — phase 2, brick 1: `EdwardsPoint::compress` emits
   the canonical wire encoding of the denoted affine point.

   THE THEOREM (`ed_compress_spec`): for a valid extended point Pt,
       compress Pt = ok s   with
       bytesVal s = (edY Pt).val + ((edX Pt).val % 2) · 2²⁵⁵
   — the 32 bytes are the canonical little-endian encoding of the affine
   y-coordinate with the parity ("sign") bit of the affine x-coordinate in
   bit 255. Combined with `verify_accepts_iff` (SigApexSpec), this pins the
   byte comparison of the apex to an equation on DENOTED POINTS — the
   half-lift toward the point-level verification equation.

   CHAIN (all real extracted code, all previously certified):
     to_affine  = invert Z, mul X, mul Y        (invert_spec, mul_spec')
     compress   = to_bytes y                     (to_bytes_spec — canonicity)
                  is_negative x                  (to_bytes again, bit 0)
                  s[31] ^= sign << 7             (XOR on a clear bit = +2²⁵⁵)

   The parity of the CANONICAL encoding is the standard "sign" convention:
   is_negative reads bit 0 of to_bytes, i.e. (feVal x mod p) mod 2 =
   (edX Pt).val mod 2.
   ────────────────────────────────────────────────────────────────────────────── -/
import Proofs.ToBytesSpec
import Proofs.InvertSpec
import Proofs.EdMain
open Aeneas Aeneas.Std Result
open curve25519

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000

namespace CurveFieldProofs

open Aeneas.Std.WP

/-- Premise-free restatement of `to_bytes_spec` (destructures internally). -/
theorem to_bytes_spec' (a : Fe) :
    fe_to_bytes a ⦃ s => bytesVal s = feVal a % P ⦄ := by
  obtain ⟨l0, l1, l2, l3, l4, hl⟩ := Fe.exists_limbs a
  exact to_bytes_spec a l0 l1 l2 l3 l4 hl

/-- Destructuring device for 32-byte arrays (the `Fe.exists_limbs` idiom). -/
theorem Bytes32.exists_bytes (s : Std.Array Std.U8 32#usize) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
      b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 : Std.U8,
      (↑s : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11,
        b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25,
        b26, b27, b28, b29, b30, b31] := by
  have h : (↑s : List Std.U8).length = 32 := by
    have := s.property
    simp_all
  match hl : (↑s : List Std.U8) with
  | [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15,
     c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31] =>
    exact ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15,
      c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, rfl⟩
  | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] | [_,_,_,_,_] | [_,_,_,_,_,_] | [_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] => simp [hl] at h
  | _::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_ => simp [hl] at h

/-- **`is_negative` is the parity of the canonical residue** — bit 0 of the
    canonical encoding (`Choice` is the transparent-u8 model). -/
theorem is_negative_spec (a : Fe) :
    field.FieldElement51.is_negative a ⦃ c => c.val = (feVal a % P) % 2 ⦄ := by
  unfold field.FieldElement51.is_negative
  step with (to_bytes_spec' a) as ⟨s, hs⟩
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
    b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31,
    hsl⟩ := Bytes32.exists_bytes s
  step as ⟨i, hi⟩
  simp [hsl] at hi
  step as ⟨i1, hi1⟩
  -- into Choice = the identity From instance
  simp only [core.convert.IntoFrom.into, subtle.Choice.Insts.CoreConvertFromU8,
    subtle.Choice.Insts.CoreConvertFromU8.from]
  try simp only [spec_ok]
  -- value: b0 &&& 1 = b0 % 2 = bytesVal s % 2 = (feVal a % P) % 2
  have hi1v : i1.val = b0.val % 2 := by
    rw [hi1, hi, UScalar.val_and]
    have := Nat.and_two_pow_sub_one_eq_mod b0.val 1
    norm_num at this
    simpa using this
  have hb0 : b0.val % 2 = bytesVal s % 2 := by
    simp only [bytesVal, hsl]
    omega
  rw [hi1v, hb0, hs]

/-- **`compress` on a valid extended point emits the canonical encoding**:
    the affine y-residue with the x-parity bit at position 255. -/
theorem ed_compress_spec (Pt : EdPoint) (hv : ExtValid Pt) :
    edwards.EdwardsPoint.compress Pt ⦃ s =>
      bytesVal s = (edY Pt).val + ((edX Pt).val % 2) * 2^255 ⦄ := by
  obtain ⟨hbX, hbY, hbZ, hZne, hcoh⟩ := hv
  unfold edwards.EdwardsPoint.compress edwards.EdwardsPoint.to_affine
  -- recip ← invert Z
  step with (invert_spec Pt.Z (Bnd.mono hbZ (by norm_num))) as ⟨recip, hbr, hrv⟩
  -- x ← X · recip, y ← Y · recip
  step with (mul_spec' Pt.X recip (Bnd.mono hbX (by norm_num)) (Bnd.mono hbr (by norm_num)))
    as ⟨x, hbx, hxv⟩
  step with (mul_spec' Pt.Y recip (Bnd.mono hbY (by norm_num)) (Bnd.mono hbr (by norm_num)))
    as ⟨y, hby, hyv⟩
  -- affine compress
  unfold edwards.affine.AffinePoint.compress
  step with (to_bytes_spec' y) as ⟨s, hs⟩
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
    b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31,
    hsl⟩ := Bytes32.exists_bytes s
  step with (is_negative_spec x) as ⟨c, hc⟩
  -- unwrap_u8 is the transparent-u8 identity: reduce it away
  simp only [subtle.Choice.unwrap_u8, bind_tc_ok]
  have hsignv : c.val = (feVal x % P) % 2 := hc
  -- sign << 7
  step as ⟨hi7, hhi7⟩
  have hsle : c.val ≤ 1 := by rw [hsignv]; omega
  have hhi7v : hi7.val = c.val * 2^7 := by
    rw [hhi7]
    simp only [Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (show c.val * 2^7 < U8.size by scalar_tac)]
  -- s[31]
  step as ⟨t31, ht31⟩
  simp [hsl] at ht31
  -- xor
  step as ⟨t31x, ht31x⟩
  -- update
  step as ⟨s1, hs1⟩
  have hsl1 : (↑s1 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
      b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23,
      b24, b25, b26, b27, b28, b29, b30, t31x] := by
    simp only [hs1, Array.set_val_eq, hsl]
    rfl
  try simp only [spec_ok]
  -- ── value assembly ───────────────────────────────────────────────────────
  -- the canonical y-residue is < p < 2²⁵⁵, so its top byte is < 2⁷
  have hsval : bytesVal s = feVal y % P := hs
  have hslt : bytesVal s < 2^255 := by
    rw [hsval]
    have : feVal y % P < P := Nat.mod_lt _ (by unfold P; norm_num)
    unfold P at this ⊢
    omega
  have hb31top : b31.val < 2^7 := by
    have hexp : bytesVal s = b0.val + b1.val * 2^8 + b2.val * 2^16 + b3.val * 2^24
        + b4.val * 2^32 + b5.val * 2^40 + b6.val * 2^48 + b7.val * 2^56
        + b8.val * 2^64 + b9.val * 2^72 + b10.val * 2^80 + b11.val * 2^88
        + b12.val * 2^96 + b13.val * 2^104 + b14.val * 2^112 + b15.val * 2^120
        + b16.val * 2^128 + b17.val * 2^136 + b18.val * 2^144 + b19.val * 2^152
        + b20.val * 2^160 + b21.val * 2^168 + b22.val * 2^176 + b23.val * 2^184
        + b24.val * 2^192 + b25.val * 2^200 + b26.val * 2^208 + b27.val * 2^216
        + b28.val * 2^224 + b29.val * 2^232 + b30.val * 2^240 + b31.val * 2^248 := by
      simp only [bytesVal, hsl]
    omega
  -- the xor adds sign·2⁷ to a clear bit
  have ht31xv : t31x.val = b31.val + c.val * 2^7 := by
    have hsb : c.val = 0 ∨ c.val = 1 := by
      rw [hsignv]; omega
    rw [ht31x, UScalar.val_xor, ht31, hhi7v]
    rcases hsb with h | h
    · simp [h]
    · rw [h]
      norm_num
      exact xor_top_bit b31.val hb31top
  -- reassemble: only byte 31 changed, and it grew by sign·2⁷ at weight 2²⁴⁸
  have hexp : bytesVal s = b0.val + b1.val * 2^8 + b2.val * 2^16 + b3.val * 2^24
      + b4.val * 2^32 + b5.val * 2^40 + b6.val * 2^48 + b7.val * 2^56
      + b8.val * 2^64 + b9.val * 2^72 + b10.val * 2^80 + b11.val * 2^88
      + b12.val * 2^96 + b13.val * 2^104 + b14.val * 2^112 + b15.val * 2^120
      + b16.val * 2^128 + b17.val * 2^136 + b18.val * 2^144 + b19.val * 2^152
      + b20.val * 2^160 + b21.val * 2^168 + b22.val * 2^176 + b23.val * 2^184
      + b24.val * 2^192 + b25.val * 2^200 + b26.val * 2^208 + b27.val * 2^216
      + b28.val * 2^224 + b29.val * 2^232 + b30.val * 2^240 + b31.val * 2^248 := by
    simp only [bytesVal, hsl]
  have hexp1 : bytesVal s1 = b0.val + b1.val * 2^8 + b2.val * 2^16 + b3.val * 2^24
      + b4.val * 2^32 + b5.val * 2^40 + b6.val * 2^48 + b7.val * 2^56
      + b8.val * 2^64 + b9.val * 2^72 + b10.val * 2^80 + b11.val * 2^88
      + b12.val * 2^96 + b13.val * 2^104 + b14.val * 2^112 + b15.val * 2^120
      + b16.val * 2^128 + b17.val * 2^136 + b18.val * 2^144 + b19.val * 2^152
      + b20.val * 2^160 + b21.val * 2^168 + b22.val * 2^176 + b23.val * 2^184
      + b24.val * 2^192 + b25.val * 2^200 + b26.val * 2^208 + b27.val * 2^216
      + b28.val * 2^224 + b29.val * 2^232 + b30.val * 2^240 + t31x.val * 2^248 := by
    simp only [bytesVal, hsl1]
  have hstep : bytesVal s1 = bytesVal s + c.val * 2^255 := by
    rw [hexp, hexp1, ht31xv]
    ring
  -- denotation bridges: the residues are the .val of the denoted coordinates
  haveI : NeZero P := ⟨by unfold P; norm_num⟩
  have hyval : feVal y % P = (edY Pt).val := by
    have h1 : ⟪y⟫ = edY Pt := by
      rw [hyv, hrv]
      unfold edY
      rw [div_eq_mul_inv]
    rw [← h1]
    simp [denote, ZMod.val_natCast]
  have hxval : (feVal x % P) % 2 = (edX Pt).val % 2 := by
    have h1 : ⟪x⟫ = edX Pt := by
      rw [hxv, hrv]
      unfold edX
      rw [div_eq_mul_inv]
    rw [← h1]
    simp [denote, ZMod.val_natCast]
  rw [hstep, hs, hsignv, hyval, hxval]

end CurveFieldProofs
