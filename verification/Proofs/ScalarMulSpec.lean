/- ──────────────────────────────────────────────────────────────────────────────
   Proofs/ScalarMulSpec.lean — Scalar52 multiplication, phase A: mul_internal

   `mul_internal a b` computes the nine schoolbook column sums
   z_k = Σ_(i+j=k) a_i·b_j into u128 words (scalar.rs:222-236) — no carries,
   no reduction; those happen in montgomery_reduce (phase B, open frontier).
   This file proves the columns exact and bounded: each product < 2^104
   (52+52 bits), each column < 5·2^104 < 2^107.
   ────────────────────────────────────────────────────────────────────────────── -/
import Proofs.ScalarDenote
open Aeneas Aeneas.Std Result
open curve25519

set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

namespace ScalarProofs

open Aeneas.Std.WP

/-- The widening 52×52→104-bit product helper `m` (scalar.rs:56-58):
    total, value exact (u64→u128 casts cannot truncate; the product of two
    64-bit values cannot overflow u128). -/
theorem m_spec (x y : U64) :
    backend.serial.u64.scalar.m x y ⦃ r => r.val = x.val * y.val ⦄ := by
  unfold backend.serial.u64.scalar.m
  step with UScalar.cast.step_spec as ⟨cx, hcx⟩
  step with UScalar.cast.step_spec as ⟨cy, hcy⟩
  have hcxv : cx.val = x.val := by
    simp [hcx, UScalar.cast_val_eq, U64.size, U128.size]
  have hcyv : cy.val = y.val := by
    simp [hcy, UScalar.cast_val_eq, U64.size, U128.size]
  have hfits : cx.val * cy.val ≤ U128.max := by
    rw [hcxv, hcyv]
    have hx := x.hBounds
    have hy := y.hBounds
    have h2 : x.val * y.val < 2^64 * 2^64 := by
      apply Nat.mul_lt_mul'' <;> scalar_tac
    scalar_tac
  step as ⟨r, hr⟩
  try simp only [spec_ok]
  rw [hr, hcxv, hcyv]

/-- `mul_internal`: the nine exact schoolbook columns, each bounded.
    For 52-bit-bounded inputs no operation can overflow. -/
theorem mul_internal_spec (a b : Sc)
    (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : U64)
    (ha : (↑a : List U64) = [a0, a1, a2, a3, a4])
    (hb : (↑b : List U64) = [b0, b1, b2, b3, b4])
    (hbnd : a0.val < 2^52 ∧ a1.val < 2^52 ∧ a2.val < 2^52 ∧ a3.val < 2^52 ∧ a4.val < 2^52 ∧
            b0.val < 2^52 ∧ b1.val < 2^52 ∧ b2.val < 2^52 ∧ b3.val < 2^52 ∧ b4.val < 2^52) :
    backend.serial.u64.scalar.Scalar52.mul_internal a b
      ⦃ (zz : Std.Array Std.U128 9#usize) => ∃ z0 z1 z2 z3 z4 z5 z6 z7 z8 : Std.U128,
          (↑zz : List Std.U128) = [z0, z1, z2, z3, z4, z5, z6, z7, z8] ∧
          z0.val = (a0.val * b0.val) ∧
          z1.val = ((a0.val * b1.val) + (a1.val * b0.val)) ∧
          z2.val = (((a0.val * b2.val) + (a1.val * b1.val)) + (a2.val * b0.val)) ∧
          z3.val = ((((a0.val * b3.val) + (a1.val * b2.val)) + (a2.val * b1.val)) + (a3.val * b0.val)) ∧
          z4.val = (((((a0.val * b4.val) + (a1.val * b3.val)) + (a2.val * b2.val)) + (a3.val * b1.val)) + (a4.val * b0.val)) ∧
          z5.val = ((((a1.val * b4.val) + (a2.val * b3.val)) + (a3.val * b2.val)) + (a4.val * b1.val)) ∧
          z6.val = (((a2.val * b4.val) + (a3.val * b3.val)) + (a4.val * b2.val)) ∧
          z7.val = ((a3.val * b4.val) + (a4.val * b3.val)) ∧
          z8.val = (a4.val * b4.val) ⦄ := by
  obtain ⟨hA0, hA1, hA2, hA3, hA4, hB0, hB1, hB2, hB3, hB4⟩ := hbnd
  unfold backend.serial.u64.scalar.Scalar52.mul_internal
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexUsizeU64.index
  step as ⟨i, hi⟩
  simp [ha] at hi
  have hvi : i.val = a0.val := by rw [hi]
  step as ⟨i1, hi1⟩
  simp [hb] at hi1
  have hvi1 : i1.val = b0.val := by rw [hi1]
  step with m_spec as ⟨i2, hi2⟩
  have hvi2 : i2.val = a0.val * b0.val := by rw [hi2, hvi, hvi1]
  have hbi2 : a0.val * b0.val < 2^104 := by
    have h := Nat.mul_lt_mul'' hA0 hB0; omega
  step as ⟨z1, hz1⟩
  step as ⟨i3, hi3⟩
  simp [hb] at hi3
  have hvi3 : i3.val = b1.val := by rw [hi3]
  step with m_spec as ⟨i4, hi4⟩
  have hvi4 : i4.val = a0.val * b1.val := by rw [hi4, hvi, hvi3]
  have hbi4 : a0.val * b1.val < 2^104 := by
    have h := Nat.mul_lt_mul'' hA0 hB1; omega
  step as ⟨i5, hi5⟩
  simp [ha] at hi5
  have hvi5 : i5.val = a1.val := by rw [hi5]
  step with m_spec as ⟨i6, hi6⟩
  have hvi6 : i6.val = a1.val * b0.val := by rw [hi6, hvi5, hvi1]
  have hbi6 : a1.val * b0.val < 2^104 := by
    have h := Nat.mul_lt_mul'' hA1 hB0; omega
  have hsi7 : i4.val + i6.val < 2^128 := by rw [hvi4, hvi6]; omega
  step as ⟨i7, hi7⟩
  have hvi7 : i7.val = (a0.val * b1.val) + (a1.val * b0.val) := by rw [hi7, hvi4, hvi6]
  have hbi7 : (a0.val * b1.val) + (a1.val * b0.val) < 2^107 := by omega
  step as ⟨z2, hz2⟩
  step as ⟨i8, hi8⟩
  simp [hb] at hi8
  have hvi8 : i8.val = b2.val := by rw [hi8]
  step with m_spec as ⟨i9, hi9⟩
  have hvi9 : i9.val = a0.val * b2.val := by rw [hi9, hvi, hvi8]
  have hbi9 : a0.val * b2.val < 2^104 := by
    have h := Nat.mul_lt_mul'' hA0 hB2; omega
  step with m_spec as ⟨i10, hi10⟩
  have hvi10 : i10.val = a1.val * b1.val := by rw [hi10, hvi5, hvi3]
  have hbi10 : a1.val * b1.val < 2^104 := by
    have h := Nat.mul_lt_mul'' hA1 hB1; omega
  have hsi11 : i9.val + i10.val < 2^128 := by rw [hvi9, hvi10]; omega
  step as ⟨i11, hi11⟩
  have hvi11 : i11.val = (a0.val * b2.val) + (a1.val * b1.val) := by rw [hi11, hvi9, hvi10]
  have hbi11 : (a0.val * b2.val) + (a1.val * b1.val) < 2^107 := by omega
  step as ⟨i12, hi12⟩
  simp [ha] at hi12
  have hvi12 : i12.val = a2.val := by rw [hi12]
  step with m_spec as ⟨i13, hi13⟩
  have hvi13 : i13.val = a2.val * b0.val := by rw [hi13, hvi12, hvi1]
  have hbi13 : a2.val * b0.val < 2^104 := by
    have h := Nat.mul_lt_mul'' hA2 hB0; omega
  have hsi14 : i11.val + i13.val < 2^128 := by rw [hvi11, hvi13]; omega
  step as ⟨i14, hi14⟩
  have hvi14 : i14.val = ((a0.val * b2.val) + (a1.val * b1.val)) + (a2.val * b0.val) := by rw [hi14, hvi11, hvi13]
  have hbi14 : ((a0.val * b2.val) + (a1.val * b1.val)) + (a2.val * b0.val) < 2^107 := by omega
  step as ⟨z3, hz3⟩
  step as ⟨i15, hi15⟩
  simp [hb] at hi15
  have hvi15 : i15.val = b3.val := by rw [hi15]
  step with m_spec as ⟨i16, hi16⟩
  have hvi16 : i16.val = a0.val * b3.val := by rw [hi16, hvi, hvi15]
  have hbi16 : a0.val * b3.val < 2^104 := by
    have h := Nat.mul_lt_mul'' hA0 hB3; omega
  step with m_spec as ⟨i17, hi17⟩
  have hvi17 : i17.val = a1.val * b2.val := by rw [hi17, hvi5, hvi8]
  have hbi17 : a1.val * b2.val < 2^104 := by
    have h := Nat.mul_lt_mul'' hA1 hB2; omega
  have hsi18 : i16.val + i17.val < 2^128 := by rw [hvi16, hvi17]; omega
  step as ⟨i18, hi18⟩
  have hvi18 : i18.val = (a0.val * b3.val) + (a1.val * b2.val) := by rw [hi18, hvi16, hvi17]
  have hbi18 : (a0.val * b3.val) + (a1.val * b2.val) < 2^107 := by omega
  step with m_spec as ⟨i19, hi19⟩
  have hvi19 : i19.val = a2.val * b1.val := by rw [hi19, hvi12, hvi3]
  have hbi19 : a2.val * b1.val < 2^104 := by
    have h := Nat.mul_lt_mul'' hA2 hB1; omega
  have hsi20 : i18.val + i19.val < 2^128 := by rw [hvi18, hvi19]; omega
  step as ⟨i20, hi20⟩
  have hvi20 : i20.val = ((a0.val * b3.val) + (a1.val * b2.val)) + (a2.val * b1.val) := by rw [hi20, hvi18, hvi19]
  have hbi20 : ((a0.val * b3.val) + (a1.val * b2.val)) + (a2.val * b1.val) < 2^107 := by omega
  step as ⟨i21, hi21⟩
  simp [ha] at hi21
  have hvi21 : i21.val = a3.val := by rw [hi21]
  step with m_spec as ⟨i22, hi22⟩
  have hvi22 : i22.val = a3.val * b0.val := by rw [hi22, hvi21, hvi1]
  have hbi22 : a3.val * b0.val < 2^104 := by
    have h := Nat.mul_lt_mul'' hA3 hB0; omega
  have hsi23 : i20.val + i22.val < 2^128 := by rw [hvi20, hvi22]; omega
  step as ⟨i23, hi23⟩
  have hvi23 : i23.val = (((a0.val * b3.val) + (a1.val * b2.val)) + (a2.val * b1.val)) + (a3.val * b0.val) := by rw [hi23, hvi20, hvi22]
  have hbi23 : (((a0.val * b3.val) + (a1.val * b2.val)) + (a2.val * b1.val)) + (a3.val * b0.val) < 2^107 := by omega
  step as ⟨z4, hz4⟩
  step as ⟨i24, hi24⟩
  simp [hb] at hi24
  have hvi24 : i24.val = b4.val := by rw [hi24]
  step with m_spec as ⟨i25, hi25⟩
  have hvi25 : i25.val = a0.val * b4.val := by rw [hi25, hvi, hvi24]
  have hbi25 : a0.val * b4.val < 2^104 := by
    have h := Nat.mul_lt_mul'' hA0 hB4; omega
  step with m_spec as ⟨i26, hi26⟩
  have hvi26 : i26.val = a1.val * b3.val := by rw [hi26, hvi5, hvi15]
  have hbi26 : a1.val * b3.val < 2^104 := by
    have h := Nat.mul_lt_mul'' hA1 hB3; omega
  have hsi27 : i25.val + i26.val < 2^128 := by rw [hvi25, hvi26]; omega
  step as ⟨i27, hi27⟩
  have hvi27 : i27.val = (a0.val * b4.val) + (a1.val * b3.val) := by rw [hi27, hvi25, hvi26]
  have hbi27 : (a0.val * b4.val) + (a1.val * b3.val) < 2^107 := by omega
  step with m_spec as ⟨i28, hi28⟩
  have hvi28 : i28.val = a2.val * b2.val := by rw [hi28, hvi12, hvi8]
  have hbi28 : a2.val * b2.val < 2^104 := by
    have h := Nat.mul_lt_mul'' hA2 hB2; omega
  have hsi29 : i27.val + i28.val < 2^128 := by rw [hvi27, hvi28]; omega
  step as ⟨i29, hi29⟩
  have hvi29 : i29.val = ((a0.val * b4.val) + (a1.val * b3.val)) + (a2.val * b2.val) := by rw [hi29, hvi27, hvi28]
  have hbi29 : ((a0.val * b4.val) + (a1.val * b3.val)) + (a2.val * b2.val) < 2^107 := by omega
  step with m_spec as ⟨i30, hi30⟩
  have hvi30 : i30.val = a3.val * b1.val := by rw [hi30, hvi21, hvi3]
  have hbi30 : a3.val * b1.val < 2^104 := by
    have h := Nat.mul_lt_mul'' hA3 hB1; omega
  have hsi31 : i29.val + i30.val < 2^128 := by rw [hvi29, hvi30]; omega
  step as ⟨i31, hi31⟩
  have hvi31 : i31.val = (((a0.val * b4.val) + (a1.val * b3.val)) + (a2.val * b2.val)) + (a3.val * b1.val) := by rw [hi31, hvi29, hvi30]
  have hbi31 : (((a0.val * b4.val) + (a1.val * b3.val)) + (a2.val * b2.val)) + (a3.val * b1.val) < 2^107 := by omega
  step as ⟨i32, hi32⟩
  simp [ha] at hi32
  have hvi32 : i32.val = a4.val := by rw [hi32]
  step with m_spec as ⟨i33, hi33⟩
  have hvi33 : i33.val = a4.val * b0.val := by rw [hi33, hvi32, hvi1]
  have hbi33 : a4.val * b0.val < 2^104 := by
    have h := Nat.mul_lt_mul'' hA4 hB0; omega
  have hsi34 : i31.val + i33.val < 2^128 := by rw [hvi31, hvi33]; omega
  step as ⟨i34, hi34⟩
  have hvi34 : i34.val = ((((a0.val * b4.val) + (a1.val * b3.val)) + (a2.val * b2.val)) + (a3.val * b1.val)) + (a4.val * b0.val) := by rw [hi34, hvi31, hvi33]
  have hbi34 : ((((a0.val * b4.val) + (a1.val * b3.val)) + (a2.val * b2.val)) + (a3.val * b1.val)) + (a4.val * b0.val) < 2^107 := by omega
  step as ⟨z5, hz5⟩
  step with m_spec as ⟨i35, hi35⟩
  have hvi35 : i35.val = a1.val * b4.val := by rw [hi35, hvi5, hvi24]
  have hbi35 : a1.val * b4.val < 2^104 := by
    have h := Nat.mul_lt_mul'' hA1 hB4; omega
  step with m_spec as ⟨i36, hi36⟩
  have hvi36 : i36.val = a2.val * b3.val := by rw [hi36, hvi12, hvi15]
  have hbi36 : a2.val * b3.val < 2^104 := by
    have h := Nat.mul_lt_mul'' hA2 hB3; omega
  have hsi37 : i35.val + i36.val < 2^128 := by rw [hvi35, hvi36]; omega
  step as ⟨i37, hi37⟩
  have hvi37 : i37.val = (a1.val * b4.val) + (a2.val * b3.val) := by rw [hi37, hvi35, hvi36]
  have hbi37 : (a1.val * b4.val) + (a2.val * b3.val) < 2^107 := by omega
  step with m_spec as ⟨i38, hi38⟩
  have hvi38 : i38.val = a3.val * b2.val := by rw [hi38, hvi21, hvi8]
  have hbi38 : a3.val * b2.val < 2^104 := by
    have h := Nat.mul_lt_mul'' hA3 hB2; omega
  have hsi39 : i37.val + i38.val < 2^128 := by rw [hvi37, hvi38]; omega
  step as ⟨i39, hi39⟩
  have hvi39 : i39.val = ((a1.val * b4.val) + (a2.val * b3.val)) + (a3.val * b2.val) := by rw [hi39, hvi37, hvi38]
  have hbi39 : ((a1.val * b4.val) + (a2.val * b3.val)) + (a3.val * b2.val) < 2^107 := by omega
  step with m_spec as ⟨i40, hi40⟩
  have hvi40 : i40.val = a4.val * b1.val := by rw [hi40, hvi32, hvi3]
  have hbi40 : a4.val * b1.val < 2^104 := by
    have h := Nat.mul_lt_mul'' hA4 hB1; omega
  have hsi41 : i39.val + i40.val < 2^128 := by rw [hvi39, hvi40]; omega
  step as ⟨i41, hi41⟩
  have hvi41 : i41.val = (((a1.val * b4.val) + (a2.val * b3.val)) + (a3.val * b2.val)) + (a4.val * b1.val) := by rw [hi41, hvi39, hvi40]
  have hbi41 : (((a1.val * b4.val) + (a2.val * b3.val)) + (a3.val * b2.val)) + (a4.val * b1.val) < 2^107 := by omega
  step as ⟨z6, hz6⟩
  step with m_spec as ⟨i42, hi42⟩
  have hvi42 : i42.val = a2.val * b4.val := by rw [hi42, hvi12, hvi24]
  have hbi42 : a2.val * b4.val < 2^104 := by
    have h := Nat.mul_lt_mul'' hA2 hB4; omega
  step with m_spec as ⟨i43, hi43⟩
  have hvi43 : i43.val = a3.val * b3.val := by rw [hi43, hvi21, hvi15]
  have hbi43 : a3.val * b3.val < 2^104 := by
    have h := Nat.mul_lt_mul'' hA3 hB3; omega
  have hsi44 : i42.val + i43.val < 2^128 := by rw [hvi42, hvi43]; omega
  step as ⟨i44, hi44⟩
  have hvi44 : i44.val = (a2.val * b4.val) + (a3.val * b3.val) := by rw [hi44, hvi42, hvi43]
  have hbi44 : (a2.val * b4.val) + (a3.val * b3.val) < 2^107 := by omega
  step with m_spec as ⟨i45, hi45⟩
  have hvi45 : i45.val = a4.val * b2.val := by rw [hi45, hvi32, hvi8]
  have hbi45 : a4.val * b2.val < 2^104 := by
    have h := Nat.mul_lt_mul'' hA4 hB2; omega
  have hsi46 : i44.val + i45.val < 2^128 := by rw [hvi44, hvi45]; omega
  step as ⟨i46, hi46⟩
  have hvi46 : i46.val = ((a2.val * b4.val) + (a3.val * b3.val)) + (a4.val * b2.val) := by rw [hi46, hvi44, hvi45]
  have hbi46 : ((a2.val * b4.val) + (a3.val * b3.val)) + (a4.val * b2.val) < 2^107 := by omega
  step as ⟨z7, hz7⟩
  step with m_spec as ⟨i47, hi47⟩
  have hvi47 : i47.val = a3.val * b4.val := by rw [hi47, hvi21, hvi24]
  have hbi47 : a3.val * b4.val < 2^104 := by
    have h := Nat.mul_lt_mul'' hA3 hB4; omega
  step with m_spec as ⟨i48, hi48⟩
  have hvi48 : i48.val = a4.val * b3.val := by rw [hi48, hvi32, hvi15]
  have hbi48 : a4.val * b3.val < 2^104 := by
    have h := Nat.mul_lt_mul'' hA4 hB3; omega
  have hsi49 : i47.val + i48.val < 2^128 := by rw [hvi47, hvi48]; omega
  step as ⟨i49, hi49⟩
  have hvi49 : i49.val = (a3.val * b4.val) + (a4.val * b3.val) := by rw [hi49, hvi47, hvi48]
  have hbi49 : (a3.val * b4.val) + (a4.val * b3.val) < 2^107 := by omega
  step as ⟨z8, hz8⟩
  step with m_spec as ⟨i50, hi50⟩
  have hvi50 : i50.val = a4.val * b4.val := by rw [hi50, hvi32, hvi24]
  have hbi50 : a4.val * b4.val < 2^104 := by
    have h := Nat.mul_lt_mul'' hA4 hB4; omega
  step as ⟨zfin, hzfin⟩
  try simp only [spec_ok]
  refine ⟨i2, i7, i14, i23, i34, i41, i46, i49, i50, ?_,
          hvi2, hvi7, hvi14, hvi23, hvi34, hvi41, hvi46, hvi49, hvi50⟩
  simp [hzfin, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, Array.set_val_eq]

end ScalarProofs
