/- ──────────────────────────────────────────────────────────────────────────────
   Proofs/ToBytesSpec.lean — total-correctness spec of `FieldElement51::to_bytes`
   (phase 2 of the signature apex: the "to_bytes canonicity" brick).

   THE THEOREM (`to_bytes_spec`): for any field element a,
       to_bytes a = ok s   with   bytesVal s = feVal a mod p
   — the emitted 32 bytes are the CANONICAL little-endian encoding of the
   represented residue. Canonicity (bytesVal s < p, top bit clear) and
   injectivity ("equal residues ⇒ equal bytes, equal bytes ⇒ equal residues")
   are corollaries (`to_bytes_lt`, at the end), because bytesVal s is pinned
   to the residue itself.

   STRUCTURE: one straight-line symbolic execution (~150 machine ops — the
   longest walk in the repo, but loop-free), consuming the pure ℕ lemmas of
   Proofs/ToBytesMath.lean at exactly four joints:
     q_telescope   — the 5-rung carry chain that computes q = (h+19)/2²⁵⁵;
     q_facts       — q ∈ {0,1} (also feeds the no-overflow side conditions);
     carry_pack + q_mod_p — the final carry pass assembles (h+19q) mod 2²⁵⁵
                     = h mod p;
     bytes_pack    — the 32 shift/mask extractions reassemble the value.
   The four boundary bytes (6, 12, 19, 25) OR the high bits of one limb with
   the low bits of the next; disjointness turns each OR into +
   (Nat.two_pow_add_eq_or_of_lt, the ScalarBytesSpec idiom).

   Rust: `FieldElement51::to_bytes`, curve25519-dalek/src/backend/serial/u64/
   field.rs:368-450 (incl. its trailing debug-assert that the top bit is
   clear — discharged, not assumed). Gen: gen/CurveField/Funs.lean
   `backend.serial.u64.field.FieldElement51.to_bytes`.
   ────────────────────────────────────────────────────────────────────────────── -/
import Proofs.ReduceSpec
import Proofs.ToBytesMath
open Aeneas Aeneas.Std Result
open curve25519

set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000

namespace CurveFieldProofs

open Aeneas.Std.WP

abbrev fe_to_bytes := backend.serial.u64.field.FieldElement51.to_bytes

/-- Little-endian value of a 32-byte array (match-style, like `feVal`). -/
def bytesVal (s : Std.Array Std.U8 32#usize) : ℕ :=
  match (↑s : List Std.U8) with
  | [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
     b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31] =>
    b0.val + b1.val * 2^8 + b2.val * 2^16 + b3.val * 2^24 + b4.val * 2^32
      + b5.val * 2^40 + b6.val * 2^48 + b7.val * 2^56 + b8.val * 2^64
      + b9.val * 2^72 + b10.val * 2^80 + b11.val * 2^88 + b12.val * 2^96
      + b13.val * 2^104 + b14.val * 2^112 + b15.val * 2^120 + b16.val * 2^128
      + b17.val * 2^136 + b18.val * 2^144 + b19.val * 2^152 + b20.val * 2^160
      + b21.val * 2^168 + b22.val * 2^176 + b23.val * 2^184 + b24.val * 2^192
      + b25.val * 2^200 + b26.val * 2^208 + b27.val * 2^216 + b28.val * 2^224
      + b29.val * 2^232 + b30.val * 2^240 + b31.val * 2^248
  | _ => 0

/-- **`to_bytes` is the canonical encoder**: it always succeeds and its
    output bytes denote exactly the represented residue mod p. -/
theorem to_bytes_spec (a : Fe) (l0 l1 l2 l3 l4 : U64)
    (hl : (↑a : List U64) = [l0, l1, l2, l3, l4]) :
    fe_to_bytes a ⦃ s => bytesVal s = feVal a % P ⦄ := by
  unfold fe_to_bytes backend.serial.u64.field.FieldElement51.to_bytes
  -- weak reduction: limbs < 2⁵¹ + 19·2¹³, value preserved mod p (exactly)
  step with (reduce_spec a l0 l1 l2 l3 l4 hl) as ⟨fe, hbnd, hval⟩
  obtain ⟨m0, m1, m2, m3, m4, hm⟩ := Fe.exists_limbs fe
  rw [Bnd_eq fe m0 m1 m2 m3 m4 _ hm] at hbnd
  obtain ⟨hbm0, hbm1, hbm2, hbm3, hbm4⟩ := hbnd
  rw [feVal_eq fe m0 m1 m2 m3 m4 hm] at hval
  -- h := the weakly-reduced value; h < 2p
  have hh2p : limbsVal m0 m1 m2 m3 m4 < 2 * P := by
    unfold limbsVal P
    omega
  -- ── the q pass: q = (h+19)/2²⁵⁵ ─────────────────────────────────────────
  step as ⟨i, hi⟩
  simp [hm] at hi
  step as ⟨i1, hi1⟩
  rw [hi] at hi1
  step as ⟨q, hq⟩
  step as ⟨i2, hi2⟩
  simp [hm] at hi2
  step as ⟨i3, hi3⟩
  rw [hi2] at hi3
  step as ⟨q1, hq1⟩
  step as ⟨i4, hi4⟩
  simp [hm] at hi4
  step as ⟨i5, hi5⟩
  rw [hi4] at hi5
  step as ⟨q2, hq2⟩
  step as ⟨i6, hi6⟩
  simp [hm] at hi6
  step as ⟨i7, hi7⟩
  rw [hi6] at hi7
  step as ⟨q3, hq3⟩
  step as ⟨i8, hi8⟩
  simp [hm] at hi8
  step as ⟨i9, hi9⟩
  rw [hi8] at hi9
  step as ⟨q4, hq4⟩
  -- q4 = (h + 19) / 2²⁵⁵, and q4 ≤ 1
  have hq4v : q4.val = (limbsVal m0 m1 m2 m3 m4 + 19) / 2^255 := by
    rw [hq4, nat_shr, hi9, hq3, nat_shr, hi7, hq2, nat_shr, hi5, hq1, nat_shr,
        hi3, hq, nat_shr, hi1]
    have := q_telescope (m0.val + 19) m1.val m2.val m3.val m4.val
    unfold limbsVal
    omega
  have hq4le : q4.val ≤ 1 := by
    rw [hq4v]; exact (q_facts _ hh2p).1
  -- fold 19q into limb 0
  step as ⟨i10, hi10⟩
  step as ⟨i11, hi11⟩
  rw [hi] at hi11
  step as ⟨limbs, hlimbs⟩
  have hll : (↑limbs : List U64) = [i11, m1, m2, m3, m4] := by
    simp only [hlimbs, Array.set_val_eq, hm]
    rfl
  have hi11v : i11.val = m0.val + 19 * q4.val := by
    rw [hi11, hi10]
  -- the local mask constant 2⁵¹ − 1
  step as ⟨i12, hi12⟩
  step as ⟨mask, hmask⟩
  have hmaskv : mask.val = 2251799813685247 := by
    rw [hmask, hi12]
    simp [Nat.shiftLeft_eq]
    scalar_tac
  have hmask_mod : ∀ n : ℕ, n &&& mask.val = n % 2^51 := by
    intro n
    rw [hmaskv, nat_and_mask]
    norm_num
  -- ── the carry pass: normalize to radix 2⁵¹, dropping the 2²⁵⁵ carry ────
  -- round 0→1
  step as ⟨i13, hi13⟩
  simp [hll] at hi13
  step as ⟨i14, hi14⟩
  rw [hi13] at hi14
  step as ⟨i15, hi15⟩
  simp [hll] at hi15
  step as ⟨i16, hi16⟩
  rw [hi15] at hi16
  step as ⟨limbs1, hlimbs1⟩
  have hll1 : (↑limbs1 : List U64) = [i11, i16, m2, m3, m4] := by
    simp only [hlimbs1, Array.set_val_eq, hll]; rfl
  step as ⟨i17, hi17⟩
  simp [hll1] at hi17
  step as ⟨i18, hi18⟩
  rw [hi17] at hi18
  step as ⟨limbs2, hlimbs2⟩
  have hll2 : (↑limbs2 : List U64) = [i18, i16, m2, m3, m4] := by
    simp only [hlimbs2, Array.set_val_eq, hll1]; rfl
  -- round 1→2
  step as ⟨i19, hi19⟩
  simp [hll2] at hi19
  step as ⟨i20, hi20⟩
  rw [hi19] at hi20
  step as ⟨i21, hi21⟩
  simp [hll2] at hi21
  step as ⟨i22, hi22⟩
  rw [hi21] at hi22
  step as ⟨limbs3, hlimbs3⟩
  have hll3 : (↑limbs3 : List U64) = [i18, i16, i22, m3, m4] := by
    simp only [hlimbs3, Array.set_val_eq, hll2]; rfl
  step as ⟨i23, hi23⟩
  simp [hll3] at hi23
  step as ⟨i24, hi24⟩
  rw [hi23] at hi24
  step as ⟨limbs4, hlimbs4⟩
  have hll4 : (↑limbs4 : List U64) = [i18, i24, i22, m3, m4] := by
    simp only [hlimbs4, Array.set_val_eq, hll3]; rfl
  -- round 2→3
  step as ⟨i25, hi25⟩
  simp [hll4] at hi25
  step as ⟨i26, hi26⟩
  rw [hi25] at hi26
  step as ⟨i27, hi27⟩
  simp [hll4] at hi27
  step as ⟨i28, hi28⟩
  rw [hi27] at hi28
  step as ⟨limbs5, hlimbs5⟩
  have hll5 : (↑limbs5 : List U64) = [i18, i24, i22, i28, m4] := by
    simp only [hlimbs5, Array.set_val_eq, hll4]; rfl
  step as ⟨i29, hi29⟩
  simp [hll5] at hi29
  step as ⟨i30, hi30⟩
  rw [hi29] at hi30
  step as ⟨limbs6, hlimbs6⟩
  have hll6 : (↑limbs6 : List U64) = [i18, i24, i30, i28, m4] := by
    simp only [hlimbs6, Array.set_val_eq, hll5]; rfl
  -- round 3→4
  step as ⟨i31, hi31⟩
  simp [hll6] at hi31
  step as ⟨i32, hi32⟩
  rw [hi31] at hi32
  step as ⟨i33, hi33⟩
  simp [hll6] at hi33
  step as ⟨i34, hi34⟩
  rw [hi33] at hi34
  step as ⟨limbs7, hlimbs7⟩
  have hll7 : (↑limbs7 : List U64) = [i18, i24, i30, i28, i34] := by
    simp only [hlimbs7, Array.set_val_eq, hll6]; rfl
  step as ⟨i35, hi35⟩
  simp [hll7] at hi35
  step as ⟨i36, hi36⟩
  rw [hi35] at hi36
  step as ⟨limbs8, hlimbs8⟩
  have hll8 : (↑limbs8 : List U64) = [i18, i24, i30, i36, i34] := by
    simp only [hlimbs8, Array.set_val_eq, hll7]; rfl
  -- top slot: final mask
  step as ⟨i37, hi37⟩
  simp [hll8] at hi37
  step as ⟨i38, hi38⟩
  rw [hi37] at hi38
  step as ⟨limbs9, hlimbs9⟩
  have hll9 : (↑limbs9 : List U64) = [i18, i24, i30, i36, i38] := by
    simp only [hlimbs9, Array.set_val_eq, hll8]; rfl
  -- ── final-limb values in the exact nested q/r forms carry_pack expects ──
  have hf0v : i18.val = i11.val % 2^51 := by
    rw [hi18, UScalar.val_and, hmask_mod]
  have hi14v : i14.val = i11.val / 2^51 := by
    rw [hi14, nat_shr]
  have hi16v : i16.val = m1.val + i11.val / 2^51 := by
    rw [hi16, hi14v]
  have hf1v : i24.val = (m1.val + i11.val / 2^51) % 2^51 := by
    rw [hi24, UScalar.val_and, hmask_mod, hi16v]
  have hi20v : i20.val = (m1.val + i11.val / 2^51) / 2^51 := by
    rw [hi20, nat_shr, hi16v]
  have hi22v : i22.val = m2.val + (m1.val + i11.val / 2^51) / 2^51 := by
    rw [hi22, hi20v]
  have hf2v : i30.val = (m2.val + (m1.val + i11.val / 2^51) / 2^51) % 2^51 := by
    rw [hi30, UScalar.val_and, hmask_mod, hi22v]
  have hi26v : i26.val = (m2.val + (m1.val + i11.val / 2^51) / 2^51) / 2^51 := by
    rw [hi26, nat_shr, hi22v]
  have hi28v : i28.val = m3.val + (m2.val + (m1.val + i11.val / 2^51) / 2^51) / 2^51 := by
    rw [hi28, hi26v]
  have hf3v : i36.val = (m3.val + (m2.val + (m1.val + i11.val / 2^51) / 2^51) / 2^51) % 2^51 := by
    rw [hi36, UScalar.val_and, hmask_mod, hi28v]
  have hi32v : i32.val = (m3.val + (m2.val + (m1.val + i11.val / 2^51) / 2^51) / 2^51) / 2^51 := by
    rw [hi32, nat_shr, hi28v]
  have hi34v : i34.val = m4.val + (m3.val + (m2.val + (m1.val + i11.val / 2^51) / 2^51) / 2^51) / 2^51 := by
    rw [hi34, hi32v]
  have hf4v : i38.val = (m4.val + (m3.val + (m2.val + (m1.val + i11.val / 2^51) / 2^51) / 2^51) / 2^51) % 2^51 := by
    rw [hi38, UScalar.val_and, hmask_mod, hi34v]
  have hf0lt : i18.val < 2^51 := by rw [hf0v]; exact Nat.mod_lt _ (by norm_num)
  have hf1lt : i24.val < 2^51 := by rw [hf1v]; exact Nat.mod_lt _ (by norm_num)
  have hf2lt : i30.val < 2^51 := by rw [hf2v]; exact Nat.mod_lt _ (by norm_num)
  have hf3lt : i36.val < 2^51 := by rw [hf3v]; exact Nat.mod_lt _ (by norm_num)
  have hf4lt : i38.val < 2^51 := by rw [hf4v]; exact Nat.mod_lt _ (by norm_num)
  clear hi14 hi16 hi20 hi22 hi26 hi28 hi32 hi34 hi18 hi24 hi30 hi36 hi38
  clear hi14v hi16v hi20v hi22v hi26v hi28v hi32v hi34v
  clear hlimbs hlimbs1 hlimbs2 hlimbs3 hlimbs4 hlimbs5 hlimbs6 hlimbs7 hlimbs8 hlimbs9
  clear hll hll1 hll2 hll3 hll4 hll5 hll6 hll7 hll8
  -- ── the 32 byte extractions ──────────────────────────────────────────────
  -- byte 0 (limb 0 read + low byte)
  step as ⟨v0, hv0⟩
  simp [hll9] at hv0
  step as ⟨b0, hb0⟩
  rw [hv0] at hb0
  have hb0v : b0.val = i18.val % 2^8 := by
    rw [hb0, UScalar.cast_val_eq]
    norm_num [UScalarTy.numBits]
  step as ⟨s1, hs1⟩
  have hsl0 : (↑s1 : List Std.U8) = [b0, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs1, Array.set_val_eq, Array.repeat_val]
    rfl
  clear hb0 hs1
  -- byte 1 (limb 0 >> 8)
  step as ⟨x1, hx1⟩
  rw [hv0] at hx1
  step as ⟨b1, hb1⟩
  have hb1v : b1.val = i18.val / 2^8 % 2^8 := by
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
  have hb2v : b2.val = i18.val / 2^16 % 2^8 := by
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
  have hb3v : b3.val = i18.val / 2^24 % 2^8 := by
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
  have hb4v : b4.val = i18.val / 2^32 % 2^8 := by
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
  have hb5v : b5.val = i18.val / 2^40 % 2^8 := by
    rw [hb5, UScalar.cast_val_eq, hx5, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s6, hs6⟩
  have hsl5 : (↑s6 : List Std.U8) = [b0, b1, b2, b3, b4, b5, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs6, Array.set_val_eq, hsl4]
    rfl
  clear hx5 hb5 hs6 hsl4
  -- byte 6 (boundary: limb 0 >> 48  |  limb 1 << 3)
  step as ⟨x6, hx6⟩
  rw [hv0] at hx6
  step as ⟨v1, hv1⟩
  simp [hll9] at hv1
  step as ⟨y6, hy6⟩
  rw [hv1] at hy6
  have hy6v : y6.val = i24.val * 2^3 := by
    rw [hy6]
    simp only [Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (show i24.val * 2^3 < U64.size by scalar_tac)]
  step as ⟨z6, hz6⟩
  step as ⟨b6, hb6⟩
  have hb6v : b6.val = i18.val / 2^48 + (i24.val % 2^5) * 2^3 := by
    rw [hb6, UScalar.cast_val_eq]
    norm_num [UScalarTy.numBits]
    rw [hz6, UScalar.val_or, hx6, nat_shr, hy6v]
    have hxlt : i18.val / 2^48 < 2^3 := by omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := i18.val / 2^48) (i := 3) hxlt (i24.val)
    have hadd : i18.val / 2^48 ||| i24.val * 2^3 = i18.val / 2^48 + i24.val * 2^3 := by
      calc i18.val / 2^48 ||| i24.val * 2^3
          = i18.val / 2^48 ||| 2^3 * i24.val := by rw [Nat.mul_comm]
        _ = 2^3 * i24.val ||| i18.val / 2^48 := Nat.lor_comm _ _
        _ = 2^3 * i24.val + i18.val / 2^48 := hor.symm
        _ = i18.val / 2^48 + i24.val * 2^3 := by ring
    rw [hadd]
    omega
  step as ⟨s7, hs7⟩
  have hsl6 : (↑s7 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs7, Array.set_val_eq, hsl5]
    rfl
  clear hx6 hy6 hy6v hz6 hb6 hs7 hsl5
  -- byte 7 (limb 1 >> 5)
  step as ⟨x7, hx7⟩
  rw [hv1] at hx7
  step as ⟨b7, hb7⟩
  have hb7v : b7.val = i24.val / 2^5 % 2^8 := by
    rw [hb7, UScalar.cast_val_eq, hx7, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s8, hs8⟩
  have hsl7 : (↑s8 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs8, Array.set_val_eq, hsl6]
    rfl
  clear hx7 hb7 hs8 hsl6
  -- byte 8 (limb 1 >> 13)
  step as ⟨x8, hx8⟩
  rw [hv1] at hx8
  step as ⟨b8, hb8⟩
  have hb8v : b8.val = i24.val / 2^13 % 2^8 := by
    rw [hb8, UScalar.cast_val_eq, hx8, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s9, hs9⟩
  have hsl8 : (↑s9 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs9, Array.set_val_eq, hsl7]
    rfl
  clear hx8 hb8 hs9 hsl7
  -- byte 9 (limb 1 >> 21)
  step as ⟨x9, hx9⟩
  rw [hv1] at hx9
  step as ⟨b9, hb9⟩
  have hb9v : b9.val = i24.val / 2^21 % 2^8 := by
    rw [hb9, UScalar.cast_val_eq, hx9, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s10, hs10⟩
  have hsl9 : (↑s10 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs10, Array.set_val_eq, hsl8]
    rfl
  clear hx9 hb9 hs10 hsl8
  -- byte 10 (limb 1 >> 29)
  step as ⟨x10, hx10⟩
  rw [hv1] at hx10
  step as ⟨b10, hb10⟩
  have hb10v : b10.val = i24.val / 2^29 % 2^8 := by
    rw [hb10, UScalar.cast_val_eq, hx10, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s11, hs11⟩
  have hsl10 : (↑s11 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs11, Array.set_val_eq, hsl9]
    rfl
  clear hx10 hb10 hs11 hsl9
  -- byte 11 (limb 1 >> 37)
  step as ⟨x11, hx11⟩
  rw [hv1] at hx11
  step as ⟨b11, hb11⟩
  have hb11v : b11.val = i24.val / 2^37 % 2^8 := by
    rw [hb11, UScalar.cast_val_eq, hx11, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s12, hs12⟩
  have hsl11 : (↑s12 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs12, Array.set_val_eq, hsl10]
    rfl
  clear hx11 hb11 hs12 hsl10
  -- byte 12 (boundary: limb 1 >> 45  |  limb 2 << 6)
  step as ⟨x12, hx12⟩
  rw [hv1] at hx12
  step as ⟨v2, hv2⟩
  simp [hll9] at hv2
  step as ⟨y12, hy12⟩
  rw [hv2] at hy12
  have hy12v : y12.val = i30.val * 2^6 := by
    rw [hy12]
    simp only [Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (show i30.val * 2^6 < U64.size by scalar_tac)]
  step as ⟨z12, hz12⟩
  step as ⟨b12, hb12⟩
  have hb12v : b12.val = i24.val / 2^45 + (i30.val % 2^2) * 2^6 := by
    rw [hb12, UScalar.cast_val_eq]
    norm_num [UScalarTy.numBits]
    rw [hz12, UScalar.val_or, hx12, nat_shr, hy12v]
    have hxlt : i24.val / 2^45 < 2^6 := by omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := i24.val / 2^45) (i := 6) hxlt (i30.val)
    have hadd : i24.val / 2^45 ||| i30.val * 2^6 = i24.val / 2^45 + i30.val * 2^6 := by
      calc i24.val / 2^45 ||| i30.val * 2^6
          = i24.val / 2^45 ||| 2^6 * i30.val := by rw [Nat.mul_comm]
        _ = 2^6 * i30.val ||| i24.val / 2^45 := Nat.lor_comm _ _
        _ = 2^6 * i30.val + i24.val / 2^45 := hor.symm
        _ = i24.val / 2^45 + i30.val * 2^6 := by ring
    rw [hadd]
    omega
  step as ⟨s13, hs13⟩
  have hsl12 : (↑s13 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs13, Array.set_val_eq, hsl11]
    rfl
  clear hx12 hy12 hy12v hz12 hb12 hs13 hsl11
  -- byte 13 (limb 2 >> 2)
  step as ⟨x13, hx13⟩
  rw [hv2] at hx13
  step as ⟨b13, hb13⟩
  have hb13v : b13.val = i30.val / 2^2 % 2^8 := by
    rw [hb13, UScalar.cast_val_eq, hx13, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s14, hs14⟩
  have hsl13 : (↑s14 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs14, Array.set_val_eq, hsl12]
    rfl
  clear hx13 hb13 hs14 hsl12
  -- byte 14 (limb 2 >> 10)
  step as ⟨x14, hx14⟩
  rw [hv2] at hx14
  step as ⟨b14, hb14⟩
  have hb14v : b14.val = i30.val / 2^10 % 2^8 := by
    rw [hb14, UScalar.cast_val_eq, hx14, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s15, hs15⟩
  have hsl14 : (↑s15 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs15, Array.set_val_eq, hsl13]
    rfl
  clear hx14 hb14 hs15 hsl13
  -- byte 15 (limb 2 >> 18)
  step as ⟨x15, hx15⟩
  rw [hv2] at hx15
  step as ⟨b15, hb15⟩
  have hb15v : b15.val = i30.val / 2^18 % 2^8 := by
    rw [hb15, UScalar.cast_val_eq, hx15, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s16, hs16⟩
  have hsl15 : (↑s16 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs16, Array.set_val_eq, hsl14]
    rfl
  clear hx15 hb15 hs16 hsl14
  -- byte 16 (limb 2 >> 26)
  step as ⟨x16, hx16⟩
  rw [hv2] at hx16
  step as ⟨b16, hb16⟩
  have hb16v : b16.val = i30.val / 2^26 % 2^8 := by
    rw [hb16, UScalar.cast_val_eq, hx16, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s17, hs17⟩
  have hsl16 : (↑s17 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs17, Array.set_val_eq, hsl15]
    rfl
  clear hx16 hb16 hs17 hsl15
  -- byte 17 (limb 2 >> 34)
  step as ⟨x17, hx17⟩
  rw [hv2] at hx17
  step as ⟨b17, hb17⟩
  have hb17v : b17.val = i30.val / 2^34 % 2^8 := by
    rw [hb17, UScalar.cast_val_eq, hx17, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s18, hs18⟩
  have hsl17 : (↑s18 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs18, Array.set_val_eq, hsl16]
    rfl
  clear hx17 hb17 hs18 hsl16
  -- byte 18 (limb 2 >> 42)
  step as ⟨x18, hx18⟩
  rw [hv2] at hx18
  step as ⟨b18, hb18⟩
  have hb18v : b18.val = i30.val / 2^42 % 2^8 := by
    rw [hb18, UScalar.cast_val_eq, hx18, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s19, hs19⟩
  have hsl18 : (↑s19 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs19, Array.set_val_eq, hsl17]
    rfl
  clear hx18 hb18 hs19 hsl17
  -- byte 19 (boundary: limb 2 >> 50  |  limb 3 << 1)
  step as ⟨x19, hx19⟩
  rw [hv2] at hx19
  step as ⟨v3, hv3⟩
  simp [hll9] at hv3
  step as ⟨y19, hy19⟩
  rw [hv3] at hy19
  have hy19v : y19.val = i36.val * 2^1 := by
    rw [hy19]
    simp only [Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (show i36.val * 2^1 < U64.size by scalar_tac)]
  step as ⟨z19, hz19⟩
  step as ⟨b19, hb19⟩
  have hb19v : b19.val = i30.val / 2^50 + (i36.val % 2^7) * 2^1 := by
    rw [hb19, UScalar.cast_val_eq]
    norm_num [UScalarTy.numBits]
    rw [hz19, UScalar.val_or, hx19, nat_shr, hy19v]
    have hxlt : i30.val / 2^50 < 2^1 := by omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := i30.val / 2^50) (i := 1) hxlt (i36.val)
    have hadd : i30.val / 2^50 ||| i36.val * 2^1 = i30.val / 2^50 + i36.val * 2^1 := by
      calc i30.val / 2^50 ||| i36.val * 2^1
          = i30.val / 2^50 ||| 2^1 * i36.val := by rw [Nat.mul_comm]
        _ = 2^1 * i36.val ||| i30.val / 2^50 := Nat.lor_comm _ _
        _ = 2^1 * i36.val + i30.val / 2^50 := hor.symm
        _ = i30.val / 2^50 + i36.val * 2^1 := by ring
    rw [hadd]
    omega
  step as ⟨s20, hs20⟩
  have hsl19 : (↑s20 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs20, Array.set_val_eq, hsl18]
    rfl
  clear hx19 hy19 hy19v hz19 hb19 hs20 hsl18
  -- byte 20 (limb 3 >> 7)
  step as ⟨x20, hx20⟩
  rw [hv3] at hx20
  step as ⟨b20, hb20⟩
  have hb20v : b20.val = i36.val / 2^7 % 2^8 := by
    rw [hb20, UScalar.cast_val_eq, hx20, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s21, hs21⟩
  have hsl20 : (↑s21 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs21, Array.set_val_eq, hsl19]
    rfl
  clear hx20 hb20 hs21 hsl19
  -- byte 21 (limb 3 >> 15)
  step as ⟨x21, hx21⟩
  rw [hv3] at hx21
  step as ⟨b21, hb21⟩
  have hb21v : b21.val = i36.val / 2^15 % 2^8 := by
    rw [hb21, UScalar.cast_val_eq, hx21, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s22, hs22⟩
  have hsl21 : (↑s22 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs22, Array.set_val_eq, hsl20]
    rfl
  clear hx21 hb21 hs22 hsl20
  -- byte 22 (limb 3 >> 23)
  step as ⟨x22, hx22⟩
  rw [hv3] at hx22
  step as ⟨b22, hb22⟩
  have hb22v : b22.val = i36.val / 2^23 % 2^8 := by
    rw [hb22, UScalar.cast_val_eq, hx22, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s23, hs23⟩
  have hsl22 : (↑s23 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs23, Array.set_val_eq, hsl21]
    rfl
  clear hx22 hb22 hs23 hsl21
  -- byte 23 (limb 3 >> 31)
  step as ⟨x23, hx23⟩
  rw [hv3] at hx23
  step as ⟨b23, hb23⟩
  have hb23v : b23.val = i36.val / 2^31 % 2^8 := by
    rw [hb23, UScalar.cast_val_eq, hx23, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s24, hs24⟩
  have hsl23 : (↑s24 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs24, Array.set_val_eq, hsl22]
    rfl
  clear hx23 hb23 hs24 hsl22
  -- byte 24 (limb 3 >> 39)
  step as ⟨x24, hx24⟩
  rw [hv3] at hx24
  step as ⟨b24, hb24⟩
  have hb24v : b24.val = i36.val / 2^39 % 2^8 := by
    rw [hb24, UScalar.cast_val_eq, hx24, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s25, hs25⟩
  have hsl24 : (↑s25 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs25, Array.set_val_eq, hsl23]
    rfl
  clear hx24 hb24 hs25 hsl23
  -- byte 25 (boundary: limb 3 >> 47  |  limb 4 << 4)
  step as ⟨x25, hx25⟩
  rw [hv3] at hx25
  step as ⟨v4, hv4⟩
  simp [hll9] at hv4
  step as ⟨y25, hy25⟩
  rw [hv4] at hy25
  have hy25v : y25.val = i38.val * 2^4 := by
    rw [hy25]
    simp only [Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (show i38.val * 2^4 < U64.size by scalar_tac)]
  step as ⟨z25, hz25⟩
  step as ⟨b25, hb25⟩
  have hb25v : b25.val = i36.val / 2^47 + (i38.val % 2^4) * 2^4 := by
    rw [hb25, UScalar.cast_val_eq]
    norm_num [UScalarTy.numBits]
    rw [hz25, UScalar.val_or, hx25, nat_shr, hy25v]
    have hxlt : i36.val / 2^47 < 2^4 := by omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := i36.val / 2^47) (i := 4) hxlt (i38.val)
    have hadd : i36.val / 2^47 ||| i38.val * 2^4 = i36.val / 2^47 + i38.val * 2^4 := by
      calc i36.val / 2^47 ||| i38.val * 2^4
          = i36.val / 2^47 ||| 2^4 * i38.val := by rw [Nat.mul_comm]
        _ = 2^4 * i38.val ||| i36.val / 2^47 := Nat.lor_comm _ _
        _ = 2^4 * i38.val + i36.val / 2^47 := hor.symm
        _ = i36.val / 2^47 + i38.val * 2^4 := by ring
    rw [hadd]
    omega
  step as ⟨s26, hs26⟩
  have hsl25 : (↑s26 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs26, Array.set_val_eq, hsl24]
    rfl
  clear hx25 hy25 hy25v hz25 hb25 hs26 hsl24
  -- byte 26 (limb 4 >> 4)
  step as ⟨x26, hx26⟩
  rw [hv4] at hx26
  step as ⟨b26, hb26⟩
  have hb26v : b26.val = i38.val / 2^4 % 2^8 := by
    rw [hb26, UScalar.cast_val_eq, hx26, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s27, hs27⟩
  have hsl26 : (↑s27 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs27, Array.set_val_eq, hsl25]
    rfl
  clear hx26 hb26 hs27 hsl25
  -- byte 27 (limb 4 >> 12)
  step as ⟨x27, hx27⟩
  rw [hv4] at hx27
  step as ⟨b27, hb27⟩
  have hb27v : b27.val = i38.val / 2^12 % 2^8 := by
    rw [hb27, UScalar.cast_val_eq, hx27, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s28, hs28⟩
  have hsl27 : (↑s28 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp only [hs28, Array.set_val_eq, hsl26]
    rfl
  clear hx27 hb27 hs28 hsl26
  -- byte 28 (limb 4 >> 20)
  step as ⟨x28, hx28⟩
  rw [hv4] at hx28
  step as ⟨b28, hb28⟩
  have hb28v : b28.val = i38.val / 2^20 % 2^8 := by
    rw [hb28, UScalar.cast_val_eq, hx28, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s29, hs29⟩
  have hsl28 : (↑s29 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, 0#u8, 0#u8, 0#u8] := by
    simp only [hs29, Array.set_val_eq, hsl27]
    rfl
  clear hx28 hb28 hs29 hsl27
  -- byte 29 (limb 4 >> 28)
  step as ⟨x29, hx29⟩
  rw [hv4] at hx29
  step as ⟨b29, hb29⟩
  have hb29v : b29.val = i38.val / 2^28 % 2^8 := by
    rw [hb29, UScalar.cast_val_eq, hx29, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s30, hs30⟩
  have hsl29 : (↑s30 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, 0#u8, 0#u8] := by
    simp only [hs30, Array.set_val_eq, hsl28]
    rfl
  clear hx29 hb29 hs30 hsl28
  -- byte 30 (limb 4 >> 36)
  step as ⟨x30, hx30⟩
  rw [hv4] at hx30
  step as ⟨b30, hb30⟩
  have hb30v : b30.val = i38.val / 2^36 % 2^8 := by
    rw [hb30, UScalar.cast_val_eq, hx30, nat_shr]
    norm_num [UScalarTy.numBits]
  step as ⟨s31, hs31⟩
  have hsl30 : (↑s31 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, 0#u8] := by
    simp only [hs31, Array.set_val_eq, hsl29]
    rfl
  clear hx30 hb30 hs31 hsl29
  -- byte 31 (limb 4 >> 44)
  step as ⟨x31, hx31⟩
  rw [hv4] at hx31
  step as ⟨b31, hb31⟩
  have hb31v : b31.val = i38.val / 2^44 := by
    rw [hb31, UScalar.cast_val_eq, hx31, nat_shr]
    norm_num [UScalarTy.numBits]
    omega
  step as ⟨s32, hs32⟩
  have hsl31 : (↑s32 : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31] := by
    simp only [hs32, Array.set_val_eq, hsl30]
    rfl
  clear hx31 hb31 hs32 hsl30
  -- ── the trailing debug-assert: the top bit of byte 31 is clear ───────────
  step as ⟨t115, ht115⟩
  simp [hsl31] at ht115
  step as ⟨t116, ht116⟩
  rw [ht115] at ht116
  have hb31lt : b31.val < 2^7 := by
    rw [hb31v]; omega
  have ht116z : t116 = 0#u8 := by
    have hval : t116.val = 0 := by
      rw [ht116, UScalar.val_and]
      have h128 : (128#u8).val = 2^7 := by norm_num
      rw [h128, Nat.and_two_pow]
      have htb : b31.val.testBit 7 = false := Nat.testBit_lt_two_pow hb31lt
      rw [htb]
      simp
    scalar_tac
  rw [ht116z]
  step
  try simp only [spec_ok]
  -- ── assembly: bytes → limbs → mod-2²⁵⁵ → mod-p ──────────────────────────
  have hsum : bytesVal s32 =
      i18.val + i24.val * 2^51 + i30.val * 2^102 + i36.val * 2^153 + i38.val * 2^204 := by
    simp only [bytesVal, hsl31]
    rw [hb0v, hb1v, hb2v, hb3v, hb4v, hb5v, hb6v, hb7v, hb8v, hb9v, hb10v,
        hb11v, hb12v, hb13v, hb14v, hb15v, hb16v, hb17v, hb18v, hb19v, hb20v,
        hb21v, hb22v, hb23v, hb24v, hb25v, hb26v, hb27v, hb28v, hb29v, hb30v,
        hb31v]
    exact bytes_pack i18.val i24.val i30.val i36.val i38.val
      hf0lt hf1lt hf2lt hf3lt hf4lt
  have hmod255 : i18.val + i24.val * 2^51 + i30.val * 2^102 + i36.val * 2^153 + i38.val * 2^204
      = (i11.val + m1.val * 2^51 + m2.val * 2^102 + m3.val * 2^153 + m4.val * 2^204) % 2^255 := by
    rw [hf0v, hf1v, hf2v, hf3v, hf4v]
    exact carry_pack i11.val m1.val m2.val m3.val m4.val
  have hmodp : (i11.val + m1.val * 2^51 + m2.val * 2^102 + m3.val * 2^153 + m4.val * 2^204) % 2^255
      = limbsVal m0 m1 m2 m3 m4 % P := by
    have hre : i11.val + m1.val * 2^51 + m2.val * 2^102 + m3.val * 2^153 + m4.val * 2^204
        = limbsVal m0 m1 m2 m3 m4 + 19 * ((limbsVal m0 m1 m2 m3 m4 + 19) / 2^255) := by
      rw [hi11v, hq4v]
      unfold limbsVal
      ring
    rw [hre]
    exact q_mod_p _ hh2p
  have hfe_a : feVal a % P = limbsVal m0 m1 m2 m3 m4 % P := by
    rw [← hval]
    rw [Nat.add_mul_mod_self_left]
  rw [hsum, hmod255, hmodp, hfe_a]

end CurveFieldProofs
