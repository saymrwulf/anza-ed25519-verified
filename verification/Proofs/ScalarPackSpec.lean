/- ──────────────────────────────────────────────────────────────────────────────
   Proofs/ScalarPackSpec.lean — phase 2, half-lift prerequisite: the scalar
   PACK step (`Scalar52::to_bytes` / `Scalar52::pack`) and the composed
   `Scalar::from_bytes_mod_order_wide` — the hash-to-scalar entry the
   verifier's recompute path calls.

   `Scalar52::to_bytes` is pure bit-packing (radix 2⁵² → little-endian bytes,
   NO reduction — its callers guarantee canonical limbs): 30 shift-extracts
   plus 2 limb-boundary bytes (6, 19 — the only offsets where 52j is not
   byte-aligned). `scalar_pack` (the ℕ identity) mirrors ToBytesMath's
   bytes_pack at the 52-bit offsets; the boundary ORs become additions via
   the same disjointness idiom.

   THE COMPOSED SPEC (`from_bytes_mod_order_wide_spec`): for a 64-byte input
   with value T, the returned Scalar's 32 bytes have value V with
       V < ℓ   and   (V : ZMod ℓ) = T
   — i.e. the verifier's k = SHA-512 output reduced mod ℓ, in EXACTLY the
   byte-value form the dsm certificate (`vartime_double_base_mul_spec`)
   takes as its scalar premises (V < ℓ < 2²⁵³).
   ────────────────────────────────────────────────────────────────────────────── -/
import Proofs.ToBytesSpec
import Proofs.ScalarFromBytesSpec
open Aeneas Aeneas.Std Result
open curve25519

set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000

namespace ScalarProofs

open Aeneas.Std.WP
open CurveFieldProofs (bytesVal nat_shr byte_split_0 xor_top_bit)

/-- Offset-4 byte split for 52-bit limbs (the pack's odd-offset limbs 1, 3):
    low 4 bits close the boundary byte, six whole bytes follow. -/
theorem byte_split_52_4 (f : ℕ) :
    f % 2^4 + (f / 2^4 % 2^8) * 2^4 + (f / 2^12 % 2^8) * 2^12
      + (f / 2^20 % 2^8) * 2^20 + (f / 2^28 % 2^8) * 2^28
      + (f / 2^36 % 2^8) * 2^36 + (f / 2^44) * 2^44 = f := by
  have e1 : f / 2^4 / 2^8 = f / 2^12 := by rw [Nat.div_div_eq_div_mul]; norm_num
  have e2 : f / 2^12 / 2^8 = f / 2^20 := by rw [Nat.div_div_eq_div_mul]; norm_num
  have e3 : f / 2^20 / 2^8 = f / 2^28 := by rw [Nat.div_div_eq_div_mul]; norm_num
  have e4 : f / 2^28 / 2^8 = f / 2^36 := by rw [Nat.div_div_eq_div_mul]; norm_num
  have e5 : f / 2^36 / 2^8 = f / 2^44 := by rw [Nat.div_div_eq_div_mul]; norm_num
  have d0 := Nat.div_add_mod f (2^4)
  have d1 := Nat.div_add_mod (f / 2^4) (2^8)
  have d2 := Nat.div_add_mod (f / 2^12) (2^8)
  have d3 := Nat.div_add_mod (f / 2^20) (2^8)
  have d4 := Nat.div_add_mod (f / 2^28) (2^8)
  have d5 := Nat.div_add_mod (f / 2^36) (2^8)
  omega

/-- THE 52-BIT PACKING IDENTITY: the 32 bytes `Scalar52::to_bytes` emits
    assemble to the limb value (boundary bytes 6 and 19 in additive form). -/
theorem scalar_pack (l0 l1 l2 l3 l4 : ℕ)
    (h0 : l0 < 2^52) (h1 : l1 < 2^52) (h2 : l2 < 2^52)
    (h3 : l3 < 2^52) (h4 : l4 < 2^48) :
    (l0 % 2^8)
      + (l0 / 2^8 % 2^8) * 2^8
      + (l0 / 2^16 % 2^8) * 2^16
      + (l0 / 2^24 % 2^8) * 2^24
      + (l0 / 2^32 % 2^8) * 2^32
      + (l0 / 2^40 % 2^8) * 2^40
      + (l0 / 2^48 + (l1 % 2^4) * 2^4) * 2^48
      + (l1 / 2^4 % 2^8) * 2^56
      + (l1 / 2^12 % 2^8) * 2^64
      + (l1 / 2^20 % 2^8) * 2^72
      + (l1 / 2^28 % 2^8) * 2^80
      + (l1 / 2^36 % 2^8) * 2^88
      + (l1 / 2^44 % 2^8) * 2^96
      + (l2 % 2^8) * 2^104
      + (l2 / 2^8 % 2^8) * 2^112
      + (l2 / 2^16 % 2^8) * 2^120
      + (l2 / 2^24 % 2^8) * 2^128
      + (l2 / 2^32 % 2^8) * 2^136
      + (l2 / 2^40 % 2^8) * 2^144
      + (l2 / 2^48 + (l3 % 2^4) * 2^4) * 2^152
      + (l3 / 2^4 % 2^8) * 2^160
      + (l3 / 2^12 % 2^8) * 2^168
      + (l3 / 2^20 % 2^8) * 2^176
      + (l3 / 2^28 % 2^8) * 2^184
      + (l3 / 2^36 % 2^8) * 2^192
      + (l3 / 2^44 % 2^8) * 2^200
      + (l4 % 2^8) * 2^208
      + (l4 / 2^8 % 2^8) * 2^216
      + (l4 / 2^16 % 2^8) * 2^224
      + (l4 / 2^24 % 2^8) * 2^232
      + (l4 / 2^32 % 2^8) * 2^240
      + (l4 / 2^40) * 2^248
      = l0 + l1 * 2^52 + l2 * 2^104 + l3 * 2^156 + l4 * 2^208 := by
  have s0 := byte_split_0 l0
  have s1 := byte_split_52_4 l1
  have s2 := byte_split_0 l2
  have s3 := byte_split_52_4 l3
  -- limb 4 has only 6 bytes: split_0's seventh chunk vanishes (l4 < 2^48)
  have s4 := byte_split_0 l4
  have h4z : l4 / 2^48 = 0 := Nat.div_eq_of_lt h4
  -- l1/2^44, l3/2^44, l4/2^40 all fit a byte: the mods are the identity
  have h1m : l1 / 2^44 % 2^8 = l1 / 2^44 :=
    Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (show l1 < 2^44 * 2^8 by omega))
  have h3m : l3 / 2^44 % 2^8 = l3 / 2^44 :=
    Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (show l3 < 2^44 * 2^8 by omega))
  have h4m : l4 / 2^40 % 2^8 = l4 / 2^40 :=
    Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (show l4 < 2^40 * 2^8 by omega))
  rw [h1m, h3m]
  rw [h4m, h4z] at s4
  zify at s0 s1 s2 s3 s4 ⊢
  linear_combination s0 + 2^52 * s1 + 2^104 * s2 + 2^156 * s3 + 2^208 * s4

/-- **`Scalar52::to_bytes` is the canonical serializer of canonical limbs**:
    for limbs below 2⁵² with value below 2²⁵³ (every reduced scalar), the 32
    output bytes denote exactly the limb value. -/
theorem scalar52_to_bytes_spec (a : Sc) (l0 l1 l2 l3 l4 : U64)
    (hl : (↑a : List U64) = [l0, l1, l2, l3, l4])
    (hb0 : l0.val < 2^52) (hb1 : l1.val < 2^52) (hb2 : l2.val < 2^52)
    (hb3 : l3.val < 2^52) (hb4 : l4.val < 2^48) :
    backend.serial.u64.scalar.Scalar52.to_bytes a
      ⦃ s => bytesVal s = scVal a ⦄ := by
  unfold backend.serial.u64.scalar.Scalar52.to_bytes
  -- limb 0 read
  step as ⟨v0, hv0⟩
  simp [hl] at hv0
  -- byte 0 (limb 0 >> 0)
  step as ⟨x0, hx0⟩
  rw [hv0] at hx0
  step as ⟨b0, hb0⟩
  have hb0v : b0.val = l0.val % 2^8 := by
    rw [hb0, UScalar.cast_val_eq, hx0, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s1, hs1⟩
  have hsl0 : (↑s1 : List Std.U8) = [b0, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs1, Array.set_val_eq, Array.repeat_val]
    rfl
  clear hx0 hb0 hs1
  -- byte 1 (limb 0 >> 8)
  step as ⟨x1, hx1⟩
  rw [hv0] at hx1
  step as ⟨b1, hb1⟩
  have hb1v : b1.val = l0.val / 2^8 % 2^8 := by
    rw [hb1, UScalar.cast_val_eq, hx1, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s2, hs2⟩
  have hsl1 : (↑s2 : List Std.U8) = [b0, b1, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs2, Array.set_val_eq, hsl0]
    rfl
  clear hx1 hb1 hs2 hsl0
  -- byte 2 (limb 0 >> 16)
  step as ⟨x2, hx2⟩
  rw [hv0] at hx2
  step as ⟨b2, hb2⟩
  have hb2v : b2.val = l0.val / 2^16 % 2^8 := by
    rw [hb2, UScalar.cast_val_eq, hx2, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s3, hs3⟩
  have hsl2 : (↑s3 : List Std.U8) = [b0, b1, b2, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs3, Array.set_val_eq, hsl1]
    rfl
  clear hx2 hb2 hs3 hsl1
  -- byte 3 (limb 0 >> 24)
  step as ⟨x3, hx3⟩
  rw [hv0] at hx3
  step as ⟨b3, hb3⟩
  have hb3v : b3.val = l0.val / 2^24 % 2^8 := by
    rw [hb3, UScalar.cast_val_eq, hx3, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s4, hs4⟩
  have hsl3 : (↑s4 : List Std.U8) = [b0, b1, b2, b3, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs4, Array.set_val_eq, hsl2]
    rfl
  clear hx3 hb3 hs4 hsl2
  -- byte 4 (limb 0 >> 32)
  step as ⟨x4, hx4⟩
  rw [hv0] at hx4
  step as ⟨b4, hb4⟩
  have hb4v : b4.val = l0.val / 2^32 % 2^8 := by
    rw [hb4, UScalar.cast_val_eq, hx4, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s5, hs5⟩
  have hsl4 : (↑s5 : List Std.U8) = [b0, b1, b2, b3, b4, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs5, Array.set_val_eq, hsl3]
    rfl
  clear hx4 hb4 hs5 hsl3
  -- byte 5 (limb 0 >> 40)
  step as ⟨x5, hx5⟩
  rw [hv0] at hx5
  step as ⟨b5, hb5⟩
  have hb5v : b5.val = l0.val / 2^40 % 2^8 := by
    rw [hb5, UScalar.cast_val_eq, hx5, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s6, hs6⟩
  have hsl5 : (↑s6 : List Std.U8) = [b0, b1, b2, b3, b4, b5, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs6, Array.set_val_eq, hsl4]
    rfl
  clear hx5 hb5 hs6 hsl4
  -- byte 6 (boundary: limb 0 >> 48 | limb 1 << 4)
  step as ⟨x6, hx6⟩
  rw [hv0] at hx6
  step as ⟨v1, hv1⟩
  simp [hl] at hv1
  step as ⟨y6, hy6⟩
  rw [hv1] at hy6
  have hy6v : y6.val = l1.val * 2^4 := by
    rw [hy6]
    simp only [Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (show l1.val * 2^4 < U64.size by scalar_tac)]
  step as ⟨z6, hz6⟩
  step as ⟨b6, hb6⟩
  have hb6v : b6.val = l0.val / 2^48 + (l1.val % 2^4) * 2^4 := by
    rw [hb6, UScalar.cast_val_eq]
    norm_num [UScalarTy.numBits]
    rw [hz6, UScalar.val_or, hx6, nat_shr, hy6v]
    have hxlt : l0.val / 2^48 < 2^4 := by omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := l0.val / 2^48) (i := 4) hxlt (l1.val)
    have hadd : l0.val / 2^48 ||| l1.val * 2^4 = l0.val / 2^48 + l1.val * 2^4 := by
      calc l0.val / 2^48 ||| l1.val * 2^4
          = l0.val / 2^48 ||| 2^4 * l1.val := by rw [Nat.mul_comm]
        _ = 2^4 * l1.val ||| l0.val / 2^48 := Nat.lor_comm _ _
        _ = 2^4 * l1.val + l0.val / 2^48 := hor.symm
        _ = l0.val / 2^48 + l1.val * 2^4 := by ring
    rw [hadd]
    omega
  step as ⟨s7, hs7⟩
  have hsl6 : (↑s7 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs7, Array.set_val_eq, hsl5]
    rfl
  clear hx6 hy6 hy6v hz6 hb6 hs7 hsl5
  -- byte 7 (limb 1 >> 4)
  step as ⟨x7, hx7⟩
  rw [hv1] at hx7
  step as ⟨b7, hb7⟩
  have hb7v : b7.val = l1.val / 2^4 % 2^8 := by
    rw [hb7, UScalar.cast_val_eq, hx7, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s8, hs8⟩
  have hsl7 : (↑s8 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs8, Array.set_val_eq, hsl6]
    rfl
  clear hx7 hb7 hs8 hsl6
  -- byte 8 (limb 1 >> 12)
  step as ⟨x8, hx8⟩
  rw [hv1] at hx8
  step as ⟨b8, hb8⟩
  have hb8v : b8.val = l1.val / 2^12 % 2^8 := by
    rw [hb8, UScalar.cast_val_eq, hx8, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s9, hs9⟩
  have hsl8 : (↑s9 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs9, Array.set_val_eq, hsl7]
    rfl
  clear hx8 hb8 hs9 hsl7
  -- byte 9 (limb 1 >> 20)
  step as ⟨x9, hx9⟩
  rw [hv1] at hx9
  step as ⟨b9, hb9⟩
  have hb9v : b9.val = l1.val / 2^20 % 2^8 := by
    rw [hb9, UScalar.cast_val_eq, hx9, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s10, hs10⟩
  have hsl9 : (↑s10 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs10, Array.set_val_eq, hsl8]
    rfl
  clear hx9 hb9 hs10 hsl8
  -- byte 10 (limb 1 >> 28)
  step as ⟨x10, hx10⟩
  rw [hv1] at hx10
  step as ⟨b10, hb10⟩
  have hb10v : b10.val = l1.val / 2^28 % 2^8 := by
    rw [hb10, UScalar.cast_val_eq, hx10, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s11, hs11⟩
  have hsl10 : (↑s11 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs11, Array.set_val_eq, hsl9]
    rfl
  clear hx10 hb10 hs11 hsl9
  -- byte 11 (limb 1 >> 36)
  step as ⟨x11, hx11⟩
  rw [hv1] at hx11
  step as ⟨b11, hb11⟩
  have hb11v : b11.val = l1.val / 2^36 % 2^8 := by
    rw [hb11, UScalar.cast_val_eq, hx11, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s12, hs12⟩
  have hsl11 : (↑s12 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs12, Array.set_val_eq, hsl10]
    rfl
  clear hx11 hb11 hs12 hsl10
  -- byte 12 (limb 1 >> 44)
  step as ⟨x12, hx12⟩
  rw [hv1] at hx12
  step as ⟨b12, hb12⟩
  have hb12v : b12.val = l1.val / 2^44 % 2^8 := by
    rw [hb12, UScalar.cast_val_eq, hx12, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s13, hs13⟩
  have hsl12 : (↑s13 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs13, Array.set_val_eq, hsl11]
    rfl
  clear hx12 hb12 hs13 hsl11
  -- limb 2 read
  step as ⟨v2, hv2⟩
  simp [hl] at hv2
  -- byte 13 (limb 2 >> 0)
  step as ⟨x13, hx13⟩
  rw [hv2] at hx13
  step as ⟨b13, hb13⟩
  have hb13v : b13.val = l2.val % 2^8 := by
    rw [hb13, UScalar.cast_val_eq, hx13, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s14, hs14⟩
  have hsl13 : (↑s14 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs14, Array.set_val_eq, hsl12]
    rfl
  clear hx13 hb13 hs14 hsl12
  -- byte 14 (limb 2 >> 8)
  step as ⟨x14, hx14⟩
  rw [hv2] at hx14
  step as ⟨b14, hb14⟩
  have hb14v : b14.val = l2.val / 2^8 % 2^8 := by
    rw [hb14, UScalar.cast_val_eq, hx14, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s15, hs15⟩
  have hsl14 : (↑s15 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs15, Array.set_val_eq, hsl13]
    rfl
  clear hx14 hb14 hs15 hsl13
  -- byte 15 (limb 2 >> 16)
  step as ⟨x15, hx15⟩
  rw [hv2] at hx15
  step as ⟨b15, hb15⟩
  have hb15v : b15.val = l2.val / 2^16 % 2^8 := by
    rw [hb15, UScalar.cast_val_eq, hx15, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s16, hs16⟩
  have hsl15 : (↑s16 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs16, Array.set_val_eq, hsl14]
    rfl
  clear hx15 hb15 hs16 hsl14
  -- byte 16 (limb 2 >> 24)
  step as ⟨x16, hx16⟩
  rw [hv2] at hx16
  step as ⟨b16, hb16⟩
  have hb16v : b16.val = l2.val / 2^24 % 2^8 := by
    rw [hb16, UScalar.cast_val_eq, hx16, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s17, hs17⟩
  have hsl16 : (↑s17 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs17, Array.set_val_eq, hsl15]
    rfl
  clear hx16 hb16 hs17 hsl15
  -- byte 17 (limb 2 >> 32)
  step as ⟨x17, hx17⟩
  rw [hv2] at hx17
  step as ⟨b17, hb17⟩
  have hb17v : b17.val = l2.val / 2^32 % 2^8 := by
    rw [hb17, UScalar.cast_val_eq, hx17, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s18, hs18⟩
  have hsl17 : (↑s18 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs18, Array.set_val_eq, hsl16]
    rfl
  clear hx17 hb17 hs18 hsl16
  -- byte 18 (limb 2 >> 40)
  step as ⟨x18, hx18⟩
  rw [hv2] at hx18
  step as ⟨b18, hb18⟩
  have hb18v : b18.val = l2.val / 2^40 % 2^8 := by
    rw [hb18, UScalar.cast_val_eq, hx18, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s19, hs19⟩
  have hsl18 : (↑s19 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs19, Array.set_val_eq, hsl17]
    rfl
  clear hx18 hb18 hs19 hsl17
  -- byte 19 (boundary: limb 2 >> 48 | limb 3 << 4)
  step as ⟨x19, hx19⟩
  rw [hv2] at hx19
  step as ⟨v3, hv3⟩
  simp [hl] at hv3
  step as ⟨y19, hy19⟩
  rw [hv3] at hy19
  have hy19v : y19.val = l3.val * 2^4 := by
    rw [hy19]
    simp only [Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (show l3.val * 2^4 < U64.size by scalar_tac)]
  step as ⟨z19, hz19⟩
  step as ⟨b19, hb19⟩
  have hb19v : b19.val = l2.val / 2^48 + (l3.val % 2^4) * 2^4 := by
    rw [hb19, UScalar.cast_val_eq]
    norm_num [UScalarTy.numBits]
    rw [hz19, UScalar.val_or, hx19, nat_shr, hy19v]
    have hxlt : l2.val / 2^48 < 2^4 := by omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := l2.val / 2^48) (i := 4) hxlt (l3.val)
    have hadd : l2.val / 2^48 ||| l3.val * 2^4 = l2.val / 2^48 + l3.val * 2^4 := by
      calc l2.val / 2^48 ||| l3.val * 2^4
          = l2.val / 2^48 ||| 2^4 * l3.val := by rw [Nat.mul_comm]
        _ = 2^4 * l3.val ||| l2.val / 2^48 := Nat.lor_comm _ _
        _ = 2^4 * l3.val + l2.val / 2^48 := hor.symm
        _ = l2.val / 2^48 + l3.val * 2^4 := by ring
    rw [hadd]
    omega
  step as ⟨s20, hs20⟩
  have hsl19 : (↑s20 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs20, Array.set_val_eq, hsl18]
    rfl
  clear hx19 hy19 hy19v hz19 hb19 hs20 hsl18
  -- byte 20 (limb 3 >> 4)
  step as ⟨x20, hx20⟩
  rw [hv3] at hx20
  step as ⟨b20, hb20⟩
  have hb20v : b20.val = l3.val / 2^4 % 2^8 := by
    rw [hb20, UScalar.cast_val_eq, hx20, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s21, hs21⟩
  have hsl20 : (↑s21 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs21, Array.set_val_eq, hsl19]
    rfl
  clear hx20 hb20 hs21 hsl19
  -- byte 21 (limb 3 >> 12)
  step as ⟨x21, hx21⟩
  rw [hv3] at hx21
  step as ⟨b21, hb21⟩
  have hb21v : b21.val = l3.val / 2^12 % 2^8 := by
    rw [hb21, UScalar.cast_val_eq, hx21, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s22, hs22⟩
  have hsl21 : (↑s22 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs22, Array.set_val_eq, hsl20]
    rfl
  clear hx21 hb21 hs22 hsl20
  -- byte 22 (limb 3 >> 20)
  step as ⟨x22, hx22⟩
  rw [hv3] at hx22
  step as ⟨b22, hb22⟩
  have hb22v : b22.val = l3.val / 2^20 % 2^8 := by
    rw [hb22, UScalar.cast_val_eq, hx22, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s23, hs23⟩
  have hsl22 : (↑s23 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs23, Array.set_val_eq, hsl21]
    rfl
  clear hx22 hb22 hs23 hsl21
  -- byte 23 (limb 3 >> 28)
  step as ⟨x23, hx23⟩
  rw [hv3] at hx23
  step as ⟨b23, hb23⟩
  have hb23v : b23.val = l3.val / 2^28 % 2^8 := by
    rw [hb23, UScalar.cast_val_eq, hx23, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s24, hs24⟩
  have hsl23 : (↑s24 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs24, Array.set_val_eq, hsl22]
    rfl
  clear hx23 hb23 hs24 hsl22
  -- byte 24 (limb 3 >> 36)
  step as ⟨x24, hx24⟩
  rw [hv3] at hx24
  step as ⟨b24, hb24⟩
  have hb24v : b24.val = l3.val / 2^36 % 2^8 := by
    rw [hb24, UScalar.cast_val_eq, hx24, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s25, hs25⟩
  have hsl24 : (↑s25 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs25, Array.set_val_eq, hsl23]
    rfl
  clear hx24 hb24 hs25 hsl23
  -- byte 25 (limb 3 >> 44)
  step as ⟨x25, hx25⟩
  rw [hv3] at hx25
  step as ⟨b25, hb25⟩
  have hb25v : b25.val = l3.val / 2^44 % 2^8 := by
    rw [hb25, UScalar.cast_val_eq, hx25, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s26, hs26⟩
  have hsl25 : (↑s26 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs26, Array.set_val_eq, hsl24]
    rfl
  clear hx25 hb25 hs26 hsl24
  -- limb 4 read
  step as ⟨v4, hv4⟩
  simp [hl] at hv4
  -- byte 26 (limb 4 >> 0)
  step as ⟨x26, hx26⟩
  rw [hv4] at hx26
  step as ⟨b26, hb26⟩
  have hb26v : b26.val = l4.val % 2^8 := by
    rw [hb26, UScalar.cast_val_eq, hx26, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s27, hs27⟩
  have hsl26 : (↑s27 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs27, Array.set_val_eq, hsl25]
    rfl
  clear hx26 hb26 hs27 hsl25
  -- byte 27 (limb 4 >> 8)
  step as ⟨x27, hx27⟩
  rw [hv4] at hx27
  step as ⟨b27, hb27⟩
  have hb27v : b27.val = l4.val / 2^8 % 2^8 := by
    rw [hb27, UScalar.cast_val_eq, hx27, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s28, hs28⟩
  have hsl27 : (↑s28 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs28, Array.set_val_eq, hsl26]
    rfl
  clear hx27 hb27 hs28 hsl26
  -- byte 28 (limb 4 >> 16)
  step as ⟨x28, hx28⟩
  rw [hv4] at hx28
  step as ⟨b28, hb28⟩
  have hb28v : b28.val = l4.val / 2^16 % 2^8 := by
    rw [hb28, UScalar.cast_val_eq, hx28, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s29, hs29⟩
  have hsl28 : (↑s29 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, 0#u8, 0#u8, 0#u8] := by
    simp only [hs29, Array.set_val_eq, hsl27]
    rfl
  clear hx28 hb28 hs29 hsl27
  -- byte 29 (limb 4 >> 24)
  step as ⟨x29, hx29⟩
  rw [hv4] at hx29
  step as ⟨b29, hb29⟩
  have hb29v : b29.val = l4.val / 2^24 % 2^8 := by
    rw [hb29, UScalar.cast_val_eq, hx29, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s30, hs30⟩
  have hsl29 : (↑s30 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, 0#u8, 0#u8] := by
    simp only [hs30, Array.set_val_eq, hsl28]
    rfl
  clear hx29 hb29 hs30 hsl28
  -- byte 30 (limb 4 >> 32)
  step as ⟨x30, hx30⟩
  rw [hv4] at hx30
  step as ⟨b30, hb30⟩
  have hb30v : b30.val = l4.val / 2^32 % 2^8 := by
    rw [hb30, UScalar.cast_val_eq, hx30, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s31, hs31⟩
  have hsl30 : (↑s31 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, 0#u8] := by
    simp only [hs31, Array.set_val_eq, hsl29]
    rfl
  clear hx30 hb30 hs31 hsl29
  -- byte 31 (limb 4 >> 40)
  step as ⟨x31, hx31⟩
  rw [hv4] at hx31
  step as ⟨b31, hb31⟩
  have hb31v : b31.val = l4.val / 2^40 := by
    rw [hb31, UScalar.cast_val_eq, hx31, nat_shr]
    norm_num [UScalarTy.numBits]
    omega
  step as ⟨s32, hs32⟩
  have hsl31 : (↑s32 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31] := by
    simp only [hs32, Array.set_val_eq, hsl30]
    rfl
  clear hx31 hb31 hs32 hsl30
  try simp only [spec_ok]
  -- assembly via the 52-bit packing identity
  have hsum : bytesVal s32 = l0.val + l1.val * 2^52 + l2.val * 2^104
      + l3.val * 2^156 + l4.val * 2^208 := by
    simp only [bytesVal, hsl31]
    rw [hb0v, hb1v, hb2v, hb3v, hb4v, hb5v, hb6v, hb7v, hb8v, hb9v, hb10v,
        hb11v, hb12v, hb13v, hb14v, hb15v, hb16v, hb17v, hb18v, hb19v, hb20v,
        hb21v, hb22v, hb23v, hb24v, hb25v, hb26v, hb27v, hb28v, hb29v, hb30v,
        hb31v]
    exact scalar_pack l0.val l1.val l2.val l3.val l4.val hb0 hb1 hb2 hb3 hb4
  rw [hsum, scVal_eq a l0 l1 l2 l3 l4 hl]
  unfold scLimbs
  ring

/-- **The hash-to-scalar entry is total and canonical**: for a 64-byte input
    of value T, `from_bytes_mod_order_wide` returns a Scalar whose 32 bytes
    denote V with V < ℓ and V ≡ T (mod ℓ) — exactly the scalar premises the
    dsm certificate consumes. -/
theorem from_bytes_mod_order_wide_spec (input : Std.Array Std.U8 64#usize)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63 : Std.U8)
    (hb : (↑input : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63])
    (T : ℕ) (hT : T = b0.val + b1.val * 2^8 + b2.val * 2^16 + b3.val * 2^24 + b4.val * 2^32 + b5.val * 2^40 + b6.val * 2^48 + b7.val * 2^56 + b8.val * 2^64 + b9.val * 2^72 + b10.val * 2^80 + b11.val * 2^88 + b12.val * 2^96 + b13.val * 2^104 + b14.val * 2^112 + b15.val * 2^120 + b16.val * 2^128 + b17.val * 2^136 + b18.val * 2^144 + b19.val * 2^152 + b20.val * 2^160 + b21.val * 2^168 + b22.val * 2^176 + b23.val * 2^184 + b24.val * 2^192 + b25.val * 2^200 + b26.val * 2^208 + b27.val * 2^216 + b28.val * 2^224 + b29.val * 2^232 + b30.val * 2^240 + b31.val * 2^248 + b32.val * 2^256 + b33.val * 2^264 + b34.val * 2^272 + b35.val * 2^280 + b36.val * 2^288 + b37.val * 2^296 + b38.val * 2^304 + b39.val * 2^312 + b40.val * 2^320 + b41.val * 2^328 + b42.val * 2^336 + b43.val * 2^344 + b44.val * 2^352 + b45.val * 2^360 + b46.val * 2^368 + b47.val * 2^376 + b48.val * 2^384 + b49.val * 2^392 + b50.val * 2^400 + b51.val * 2^408 + b52.val * 2^416 + b53.val * 2^424 + b54.val * 2^432 + b55.val * 2^440 + b56.val * 2^448 + b57.val * 2^456 + b58.val * 2^464 + b59.val * 2^472 + b60.val * 2^480 + b61.val * 2^488 + b62.val * 2^496 + b63.val * 2^504) :
    scalar.Scalar.from_bytes_mod_order_wide input
      ⦃ k => bytesVal k.bytes < Ell ∧ (bytesVal k.bytes : ZMod Ell) = (T : ZMod Ell) ⦄ := by
  unfold scalar.Scalar.from_bytes_mod_order_wide scalar.Scalar52.pack
  step with (from_bytes_wide_spec input b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63 hb T hT)
    as ⟨r, hex, hlt, hden⟩
  obtain ⟨s0, s1, s2, s3, s4, hrl, hs0, hs1, hs2, hs3, hs4⟩ := hex
  -- top-limb tightening: scVal r < ℓ < 2²⁵³ forces s4 < 2⁴⁵ < 2⁴⁸
  have hs4' : s4.val < 2^48 := by
    have hv := scVal_eq r s0 s1 s2 s3 s4 hrl
    have : scVal r < 2^253 := by
      have : Ell < 2^253 := by unfold Ell; norm_num
      omega
    unfold scLimbs at hv
    omega
  step with (scalar52_to_bytes_spec r s0 s1 s2 s3 s4 hrl hs0 hs1 hs2 hs3 hs4')
    as ⟨bytes, hbv⟩
  try simp only [spec_ok]
  constructor
  · simpa [hbv] using hlt
  · rw [hbv]
    exact hden

end ScalarProofs
