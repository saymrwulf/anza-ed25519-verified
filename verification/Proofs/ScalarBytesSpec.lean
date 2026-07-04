/- Proofs/ScalarBytesSpec.lean — from_bytes_wide, stage 1: the 8×8
   byte-unpack loops. For each word index I, bytes_word_loop_spec_I
   proves the inner loop packs bytes 8I..8I+7 little-endian into word I
   (split at j = 4 into head + tail per METHOD 4 — the 8-fold monolith
   exceeds the elaboration budget). Disjoint-bit ORs become additions
   via core Nat.two_pow_add_eq_or_of_lt. -/
import Proofs.ScalarWideSpec
import Proofs.ScalarLoop
open Aeneas Aeneas.Std Result
open curve25519

set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 600

namespace ScalarProofs

open Aeneas.Std.WP

/-- Inner byte loop for word 0, iterations 4..7 + exit: continues the
    accumulation from the mid-state (bytes 0..3 absorbed). -/
theorem bytes_word_loop_tail_0
    (bytes : Std.Array Std.U8 64#usize)
    (words : Std.Array Std.U64 8#usize)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63 : Std.U8)
    (w0 w1 w2 w3 w4 w5 w6 w7 : U64)
    (iter : core.ops.range.Range Std.Usize)
    (hb : (↑bytes : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63])
    (hw : (↑words : List U64) = [w0, w1, w2, w3, w4, w5, w6, w7])
    (hst : iter.start.val = 4) (hend : iter.«end» = 8#usize)
    (hacc : w0.val = b0.val + b1.val * 2^8 + b2.val * 2^16 + b3.val * 2^24) :
    backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0 iter bytes words 0#usize
      ⦃ ws => ∃ v : U64, (↑ws : List U64) = [v, w1, w2, w3, w4, w5, w6, w7] ∧
          v.val = b0.val + b1.val * 2^8 + b2.val * 2^16 + b3.val * 2^24 + b4.val * 2^32 + b5.val * 2^40 + b6.val * 2^48 + b7.val * 2^56 ⦄ := by
  have hsz64 : (U64.size : ℕ) = 2^64 := by scalar_tac
  have hbb0 : b0.val < 2^8 := by scalar_tac
  have hbb1 : b1.val < 2^8 := by scalar_tac
  have hbb2 : b2.val < 2^8 := by scalar_tac
  have hbb3 : b3.val < 2^8 := by scalar_tac
  have hbb4 : b4.val < 2^8 := by scalar_tac
  have hbb5 : b5.val < 2^8 := by scalar_tac
  have hbb6 : b6.val < 2^8 := by scalar_tac
  have hbb7 : b7.val < 2^8 := by scalar_tac
  unfold backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0
  -- j = 4: byte 4
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with (range_next_lt_spec iter (by simp [hend, hst]; all_goals scalar_tac)) as ⟨o4, iter4, ho4, hs4, he4⟩
  simp only [ho4]
  step as ⟨p4, hp4⟩
  step as ⟨q4, hq4⟩
  have hq4v : q4.val = 4 := by
    simp [hq4, hp4, hst]
    all_goals scalar_tac
  step as ⟨x4, hx4⟩
  simp [hb, hq4v] at hx4
  step with UScalar.cast.step_spec as ⟨c4, hc4⟩
  have hc4v : c4.val = b4.val := by
    rw [hc4, UScalar.cast_val_eq, hx4]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s4, hsh4⟩
  have hsv4 : s4.val = 32 := by
    simp [hsh4, hst]
    all_goals scalar_tac
  step as ⟨t4, ht4⟩
  have ht4v : t4.val = b4.val * 2^32 := by
    rw [ht4]
    simp [hsv4, hc4v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u4, hu4⟩
  simp [hw] at hu4
  have hu4v : u4.val = b0.val + b1.val * 2^8 + b2.val * 2^16 + b3.val * 2^24 := by rw [hu4]; exact hacc
  step as ⟨y4, hy4⟩
  have hy4v : y4.val = b0.val + b1.val * 2^8 + b2.val * 2^16 + b3.val * 2^24 + b4.val * 2^32 := by
    have hult : u4.val < 2^32 := by rw [hu4v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u4.val) (i := 32) hult b4.val
    have hadd : u4.val ||| b4.val * 2^32 = u4.val + b4.val * 2^32 := by
      calc u4.val ||| b4.val * 2^32
          = u4.val ||| 2^32 * b4.val := by rw [Nat.mul_comm]
        _ = 2^32 * b4.val ||| u4.val := Nat.lor_comm _ _
        _ = 2^32 * b4.val + u4.val := hor.symm
        _ = u4.val + b4.val * 2^32 := by ring
    simp only [hy4, UScalar.val_or, ht4v]
    rw [hadd, hu4v]
    all_goals ring
  step as ⟨wn4, hwn4⟩
  try simp only [spec_ok]
  -- j = 5: byte 5
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with (range_next_lt_spec iter4 (by simp [hs4, he4, hend, hst]; all_goals scalar_tac)) as ⟨o5, iter5, ho5, hs5, he5⟩
  simp only [ho5]
  step as ⟨p5, hp5⟩
  step as ⟨q5, hq5⟩
  have hq5v : q5.val = 5 := by
    simp [hq5, hp5, hst, hs4, he4]
    all_goals scalar_tac
  step as ⟨x5, hx5⟩
  simp [hb, hq5v] at hx5
  step with UScalar.cast.step_spec as ⟨c5, hc5⟩
  have hc5v : c5.val = b5.val := by
    rw [hc5, UScalar.cast_val_eq, hx5]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s5, hsh5⟩
  have hsv5 : s5.val = 40 := by
    simp [hsh5, hst, hs4, he4]
    all_goals scalar_tac
  step as ⟨t5, ht5⟩
  have ht5v : t5.val = b5.val * 2^40 := by
    rw [ht5]
    simp [hsv5, hc5v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u5, hu5⟩
  simp [hwn4, hw] at hu5
  have hu5v : u5.val = b0.val + b1.val * 2^8 + b2.val * 2^16 + b3.val * 2^24 + b4.val * 2^32 := by rw [hu5]; exact hy4v
  step as ⟨y5, hy5⟩
  have hy5v : y5.val = b0.val + b1.val * 2^8 + b2.val * 2^16 + b3.val * 2^24 + b4.val * 2^32 + b5.val * 2^40 := by
    have hult : u5.val < 2^40 := by rw [hu5v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u5.val) (i := 40) hult b5.val
    have hadd : u5.val ||| b5.val * 2^40 = u5.val + b5.val * 2^40 := by
      calc u5.val ||| b5.val * 2^40
          = u5.val ||| 2^40 * b5.val := by rw [Nat.mul_comm]
        _ = 2^40 * b5.val ||| u5.val := Nat.lor_comm _ _
        _ = 2^40 * b5.val + u5.val := hor.symm
        _ = u5.val + b5.val * 2^40 := by ring
    simp only [hy5, UScalar.val_or, ht5v]
    rw [hadd, hu5v]
    all_goals ring
  step as ⟨wn5, hwn5⟩
  try simp only [spec_ok]
  -- j = 6: byte 6
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with (range_next_lt_spec iter5 (by simp [hs4, he4, hs5, he5, hend, hst]; all_goals scalar_tac)) as ⟨o6, iter6, ho6, hs6, he6⟩
  simp only [ho6]
  step as ⟨p6, hp6⟩
  step as ⟨q6, hq6⟩
  have hq6v : q6.val = 6 := by
    simp [hq6, hp6, hst, hs4, he4, hs5, he5]
    all_goals scalar_tac
  step as ⟨x6, hx6⟩
  simp [hb, hq6v] at hx6
  step with UScalar.cast.step_spec as ⟨c6, hc6⟩
  have hc6v : c6.val = b6.val := by
    rw [hc6, UScalar.cast_val_eq, hx6]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s6, hsh6⟩
  have hsv6 : s6.val = 48 := by
    simp [hsh6, hst, hs4, he4, hs5, he5]
    all_goals scalar_tac
  step as ⟨t6, ht6⟩
  have ht6v : t6.val = b6.val * 2^48 := by
    rw [ht6]
    simp [hsv6, hc6v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u6, hu6⟩
  simp [hwn5, hw] at hu6
  have hu6v : u6.val = b0.val + b1.val * 2^8 + b2.val * 2^16 + b3.val * 2^24 + b4.val * 2^32 + b5.val * 2^40 := by rw [hu6]; exact hy5v
  step as ⟨y6, hy6⟩
  have hy6v : y6.val = b0.val + b1.val * 2^8 + b2.val * 2^16 + b3.val * 2^24 + b4.val * 2^32 + b5.val * 2^40 + b6.val * 2^48 := by
    have hult : u6.val < 2^48 := by rw [hu6v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u6.val) (i := 48) hult b6.val
    have hadd : u6.val ||| b6.val * 2^48 = u6.val + b6.val * 2^48 := by
      calc u6.val ||| b6.val * 2^48
          = u6.val ||| 2^48 * b6.val := by rw [Nat.mul_comm]
        _ = 2^48 * b6.val ||| u6.val := Nat.lor_comm _ _
        _ = 2^48 * b6.val + u6.val := hor.symm
        _ = u6.val + b6.val * 2^48 := by ring
    simp only [hy6, UScalar.val_or, ht6v]
    rw [hadd, hu6v]
    all_goals ring
  step as ⟨wn6, hwn6⟩
  try simp only [spec_ok]
  -- j = 7: byte 7
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with (range_next_lt_spec iter6 (by simp [hs4, he4, hs5, he5, hs6, he6, hend, hst]; all_goals scalar_tac)) as ⟨o7, iter7, ho7, hs7, he7⟩
  simp only [ho7]
  step as ⟨p7, hp7⟩
  step as ⟨q7, hq7⟩
  have hq7v : q7.val = 7 := by
    simp [hq7, hp7, hst, hs4, he4, hs5, he5, hs6, he6]
    all_goals scalar_tac
  step as ⟨x7, hx7⟩
  simp [hb, hq7v] at hx7
  step with UScalar.cast.step_spec as ⟨c7, hc7⟩
  have hc7v : c7.val = b7.val := by
    rw [hc7, UScalar.cast_val_eq, hx7]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s7, hsh7⟩
  have hsv7 : s7.val = 56 := by
    simp [hsh7, hst, hs4, he4, hs5, he5, hs6, he6]
    all_goals scalar_tac
  step as ⟨t7, ht7⟩
  have ht7v : t7.val = b7.val * 2^56 := by
    rw [ht7]
    simp [hsv7, hc7v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u7, hu7⟩
  simp [hwn6, hw] at hu7
  have hu7v : u7.val = b0.val + b1.val * 2^8 + b2.val * 2^16 + b3.val * 2^24 + b4.val * 2^32 + b5.val * 2^40 + b6.val * 2^48 := by rw [hu7]; exact hy6v
  step as ⟨y7, hy7⟩
  have hy7v : y7.val = b0.val + b1.val * 2^8 + b2.val * 2^16 + b3.val * 2^24 + b4.val * 2^32 + b5.val * 2^40 + b6.val * 2^48 + b7.val * 2^56 := by
    have hult : u7.val < 2^56 := by rw [hu7v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u7.val) (i := 56) hult b7.val
    have hadd : u7.val ||| b7.val * 2^56 = u7.val + b7.val * 2^56 := by
      calc u7.val ||| b7.val * 2^56
          = u7.val ||| 2^56 * b7.val := by rw [Nat.mul_comm]
        _ = 2^56 * b7.val ||| u7.val := Nat.lor_comm _ _
        _ = 2^56 * b7.val + u7.val := hor.symm
        _ = u7.val + b7.val * 2^56 := by ring
    simp only [hy7, UScalar.val_or, ht7v]
    rw [hadd, hu7v]
    all_goals ring
  step as ⟨wn7, hwn7⟩
  try simp only [spec_ok]
  -- exit (8 ≥ 8)
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with (range_next_ge_spec iter7 (by simp [he7, he6, he5, he4, hend, hs7, hs6, hs5, hs4]; all_goals scalar_tac)) as ⟨oX, iterX, hoX, hrX⟩
  simp only [hoX]
  try simp only [spec_ok]
  refine ⟨y7, ?_, hy7v⟩
  simp [hwn4, hwn5, hwn6, hwn7, hw, Array.set_val_eq]

/-- Inner byte loop, outer index 0: word 0 accumulates bytes
    0..7 little-endian; the other words are untouched.
    Iterations 0..3 here; 4..7 + exit in `bytes_word_loop_tail_0`
    (the 8-fold monolith exceeds the elaboration budget — METHOD 4). -/
theorem bytes_word_loop_spec_0
    (bytes : Std.Array Std.U8 64#usize)
    (words : Std.Array Std.U64 8#usize)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63 : Std.U8)
    (w0 w1 w2 w3 w4 w5 w6 w7 : U64)
    (hb : (↑bytes : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63])
    (hw : (↑words : List U64) = [w0, w1, w2, w3, w4, w5, w6, w7])
    (hz : w0.val = 0) :
    backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0 { start := 0#usize, «end» := 8#usize } bytes words 0#usize
      ⦃ ws => ∃ v : U64, (↑ws : List U64) = [v, w1, w2, w3, w4, w5, w6, w7] ∧
          v.val = b0.val + b1.val * 2^8 + b2.val * 2^16 + b3.val * 2^24 + b4.val * 2^32 + b5.val * 2^40 + b6.val * 2^48 + b7.val * 2^56 ⦄ := by
  have hsz64 : (U64.size : ℕ) = 2^64 := by scalar_tac
  have hbb0 : b0.val < 2^8 := by scalar_tac
  have hbb1 : b1.val < 2^8 := by scalar_tac
  have hbb2 : b2.val < 2^8 := by scalar_tac
  have hbb3 : b3.val < 2^8 := by scalar_tac
  unfold backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0
  -- j = 0: byte 0
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with range_next_lt_spec as ⟨o0, iter0, ho0, hs0, he0⟩
  simp only [ho0]
  step as ⟨p0, hp0⟩
  step as ⟨q0, hq0⟩
  have hq0v : q0.val = 0 := by
    simp [hq0, hp0]
    all_goals scalar_tac
  step as ⟨x0, hx0⟩
  simp [hb, hq0v] at hx0
  step with UScalar.cast.step_spec as ⟨c0, hc0⟩
  have hc0v : c0.val = b0.val := by
    rw [hc0, UScalar.cast_val_eq, hx0]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s0, hsh0⟩
  have hsv0 : s0.val = 0 := by
    simp [hsh0]
    all_goals scalar_tac
  step as ⟨t0, ht0⟩
  have ht0v : t0.val = b0.val * 2^0 := by
    rw [ht0]
    simp [hsv0, hc0v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u0, hu0⟩
  simp [hw] at hu0
  have hu0v : u0.val = 0 := by rw [hu0]; exact hz
  step as ⟨y0, hy0⟩
  have hy0v : y0.val = b0.val := by
    simp [hy0, UScalar.val_or, hu0v, ht0v]
  step as ⟨wn0, hwn0⟩
  try simp only [spec_ok]
  -- j = 1: byte 1
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with range_next_lt_spec as ⟨o1, iter1, ho1, hs1, he1⟩
  simp only [ho1]
  step as ⟨p1, hp1⟩
  step as ⟨q1, hq1⟩
  have hq1v : q1.val = 1 := by
    simp [hq1, hp1, hs0, he0]
    all_goals scalar_tac
  step as ⟨x1, hx1⟩
  simp [hb, hq1v] at hx1
  step with UScalar.cast.step_spec as ⟨c1, hc1⟩
  have hc1v : c1.val = b1.val := by
    rw [hc1, UScalar.cast_val_eq, hx1]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s1, hsh1⟩
  have hsv1 : s1.val = 8 := by
    simp [hsh1, hs0, he0]
    all_goals scalar_tac
  step as ⟨t1, ht1⟩
  have ht1v : t1.val = b1.val * 2^8 := by
    rw [ht1]
    simp [hsv1, hc1v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u1, hu1⟩
  simp [hwn0, hw] at hu1
  have hu1v : u1.val = b0.val := by rw [hu1]; exact hy0v
  step as ⟨y1, hy1⟩
  have hy1v : y1.val = b0.val + b1.val * 2^8 := by
    have hult : u1.val < 2^8 := by rw [hu1v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u1.val) (i := 8) hult b1.val
    have hadd : u1.val ||| b1.val * 2^8 = u1.val + b1.val * 2^8 := by
      calc u1.val ||| b1.val * 2^8
          = u1.val ||| 2^8 * b1.val := by rw [Nat.mul_comm]
        _ = 2^8 * b1.val ||| u1.val := Nat.lor_comm _ _
        _ = 2^8 * b1.val + u1.val := hor.symm
        _ = u1.val + b1.val * 2^8 := by ring
    simp only [hy1, UScalar.val_or, ht1v]
    rw [hadd, hu1v]
    all_goals ring
  step as ⟨wn1, hwn1⟩
  try simp only [spec_ok]
  -- j = 2: byte 2
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with range_next_lt_spec as ⟨o2, iter2, ho2, hs2, he2⟩
  simp only [ho2]
  step as ⟨p2, hp2⟩
  step as ⟨q2, hq2⟩
  have hq2v : q2.val = 2 := by
    simp [hq2, hp2, hs0, he0, hs1, he1]
    all_goals scalar_tac
  step as ⟨x2, hx2⟩
  simp [hb, hq2v] at hx2
  step with UScalar.cast.step_spec as ⟨c2, hc2⟩
  have hc2v : c2.val = b2.val := by
    rw [hc2, UScalar.cast_val_eq, hx2]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s2, hsh2⟩
  have hsv2 : s2.val = 16 := by
    simp [hsh2, hs0, he0, hs1, he1]
    all_goals scalar_tac
  step as ⟨t2, ht2⟩
  have ht2v : t2.val = b2.val * 2^16 := by
    rw [ht2]
    simp [hsv2, hc2v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u2, hu2⟩
  simp [hwn1, hw] at hu2
  have hu2v : u2.val = b0.val + b1.val * 2^8 := by rw [hu2]; exact hy1v
  step as ⟨y2, hy2⟩
  have hy2v : y2.val = b0.val + b1.val * 2^8 + b2.val * 2^16 := by
    have hult : u2.val < 2^16 := by rw [hu2v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u2.val) (i := 16) hult b2.val
    have hadd : u2.val ||| b2.val * 2^16 = u2.val + b2.val * 2^16 := by
      calc u2.val ||| b2.val * 2^16
          = u2.val ||| 2^16 * b2.val := by rw [Nat.mul_comm]
        _ = 2^16 * b2.val ||| u2.val := Nat.lor_comm _ _
        _ = 2^16 * b2.val + u2.val := hor.symm
        _ = u2.val + b2.val * 2^16 := by ring
    simp only [hy2, UScalar.val_or, ht2v]
    rw [hadd, hu2v]
    all_goals ring
  step as ⟨wn2, hwn2⟩
  try simp only [spec_ok]
  -- j = 3: byte 3
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with range_next_lt_spec as ⟨o3, iter3, ho3, hs3, he3⟩
  simp only [ho3]
  step as ⟨p3, hp3⟩
  step as ⟨q3, hq3⟩
  have hq3v : q3.val = 3 := by
    simp [hq3, hp3, hs0, he0, hs1, he1, hs2, he2]
    all_goals scalar_tac
  step as ⟨x3, hx3⟩
  simp [hb, hq3v] at hx3
  step with UScalar.cast.step_spec as ⟨c3, hc3⟩
  have hc3v : c3.val = b3.val := by
    rw [hc3, UScalar.cast_val_eq, hx3]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s3, hsh3⟩
  have hsv3 : s3.val = 24 := by
    simp [hsh3, hs0, he0, hs1, he1, hs2, he2]
    all_goals scalar_tac
  step as ⟨t3, ht3⟩
  have ht3v : t3.val = b3.val * 2^24 := by
    rw [ht3]
    simp [hsv3, hc3v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u3, hu3⟩
  simp [hwn2, hw] at hu3
  have hu3v : u3.val = b0.val + b1.val * 2^8 + b2.val * 2^16 := by rw [hu3]; exact hy2v
  step as ⟨y3, hy3⟩
  have hy3v : y3.val = b0.val + b1.val * 2^8 + b2.val * 2^16 + b3.val * 2^24 := by
    have hult : u3.val < 2^24 := by rw [hu3v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u3.val) (i := 24) hult b3.val
    have hadd : u3.val ||| b3.val * 2^24 = u3.val + b3.val * 2^24 := by
      calc u3.val ||| b3.val * 2^24
          = u3.val ||| 2^24 * b3.val := by rw [Nat.mul_comm]
        _ = 2^24 * b3.val ||| u3.val := Nat.lor_comm _ _
        _ = 2^24 * b3.val + u3.val := hor.symm
        _ = u3.val + b3.val * 2^24 := by ring
    simp only [hy3, UScalar.val_or, ht3v]
    rw [hadd, hu3v]
    all_goals ring
  step as ⟨wn3, hwn3⟩
  try simp only [spec_ok]
  -- refold and hand over to the tail lemma at the j = 4 boundary
  show backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0 iter3 bytes wn3 0#usize
    ⦃ ws => ∃ v : U64, (↑ws : List U64) = [v, w1, w2, w3, w4, w5, w6, w7] ∧
        v.val = b0.val + b1.val * 2^8 + b2.val * 2^16 + b3.val * 2^24 + b4.val * 2^32 + b5.val * 2^40 + b6.val * 2^48 + b7.val * 2^56 ⦄
  have hwn3l : (↑wn3 : List U64) = [y3, w1, w2, w3, w4, w5, w6, w7] := by
    simp [hwn0, hwn1, hwn2, hwn3, hw, Array.set_val_eq]
  have hst3 : iter3.start.val = 4 := by
    simp [hs3, hs2, hs1, hs0]
    all_goals scalar_tac
  have hend3 : iter3.«end» = 8#usize := by
    simp [he3, he2, he1, he0]
  exact bytes_word_loop_tail_0 bytes wn3 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63
    y3 w1 w2 w3 w4 w5 w6 w7 iter3 hb hwn3l hst3 hend3 hy3v

/-- Inner byte loop for word 1, iterations 4..7 + exit: continues the
    accumulation from the mid-state (bytes 8..11 absorbed). -/
theorem bytes_word_loop_tail_1
    (bytes : Std.Array Std.U8 64#usize)
    (words : Std.Array Std.U64 8#usize)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63 : Std.U8)
    (w0 w1 w2 w3 w4 w5 w6 w7 : U64)
    (iter : core.ops.range.Range Std.Usize)
    (hb : (↑bytes : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63])
    (hw : (↑words : List U64) = [w0, w1, w2, w3, w4, w5, w6, w7])
    (hst : iter.start.val = 4) (hend : iter.«end» = 8#usize)
    (hacc : w1.val = b8.val + b9.val * 2^8 + b10.val * 2^16 + b11.val * 2^24) :
    backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0 iter bytes words 1#usize
      ⦃ ws => ∃ v : U64, (↑ws : List U64) = [w0, v, w2, w3, w4, w5, w6, w7] ∧
          v.val = b8.val + b9.val * 2^8 + b10.val * 2^16 + b11.val * 2^24 + b12.val * 2^32 + b13.val * 2^40 + b14.val * 2^48 + b15.val * 2^56 ⦄ := by
  have hsz64 : (U64.size : ℕ) = 2^64 := by scalar_tac
  have hbb8 : b8.val < 2^8 := by scalar_tac
  have hbb9 : b9.val < 2^8 := by scalar_tac
  have hbb10 : b10.val < 2^8 := by scalar_tac
  have hbb11 : b11.val < 2^8 := by scalar_tac
  have hbb12 : b12.val < 2^8 := by scalar_tac
  have hbb13 : b13.val < 2^8 := by scalar_tac
  have hbb14 : b14.val < 2^8 := by scalar_tac
  have hbb15 : b15.val < 2^8 := by scalar_tac
  unfold backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0
  -- j = 4: byte 12
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with (range_next_lt_spec iter (by simp [hend, hst]; all_goals scalar_tac)) as ⟨o4, iter4, ho4, hs4, he4⟩
  simp only [ho4]
  step as ⟨p4, hp4⟩
  step as ⟨q4, hq4⟩
  have hq4v : q4.val = 12 := by
    simp [hq4, hp4, hst]
    all_goals scalar_tac
  step as ⟨x4, hx4⟩
  simp [hb, hq4v] at hx4
  step with UScalar.cast.step_spec as ⟨c4, hc4⟩
  have hc4v : c4.val = b12.val := by
    rw [hc4, UScalar.cast_val_eq, hx4]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s4, hsh4⟩
  have hsv4 : s4.val = 32 := by
    simp [hsh4, hst]
    all_goals scalar_tac
  step as ⟨t4, ht4⟩
  have ht4v : t4.val = b12.val * 2^32 := by
    rw [ht4]
    simp [hsv4, hc4v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u4, hu4⟩
  simp [hw] at hu4
  have hu4v : u4.val = b8.val + b9.val * 2^8 + b10.val * 2^16 + b11.val * 2^24 := by rw [hu4]; exact hacc
  step as ⟨y4, hy4⟩
  have hy4v : y4.val = b8.val + b9.val * 2^8 + b10.val * 2^16 + b11.val * 2^24 + b12.val * 2^32 := by
    have hult : u4.val < 2^32 := by rw [hu4v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u4.val) (i := 32) hult b12.val
    have hadd : u4.val ||| b12.val * 2^32 = u4.val + b12.val * 2^32 := by
      calc u4.val ||| b12.val * 2^32
          = u4.val ||| 2^32 * b12.val := by rw [Nat.mul_comm]
        _ = 2^32 * b12.val ||| u4.val := Nat.lor_comm _ _
        _ = 2^32 * b12.val + u4.val := hor.symm
        _ = u4.val + b12.val * 2^32 := by ring
    simp only [hy4, UScalar.val_or, ht4v]
    rw [hadd, hu4v]
    all_goals ring
  step as ⟨wn4, hwn4⟩
  try simp only [spec_ok]
  -- j = 5: byte 13
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with (range_next_lt_spec iter4 (by simp [hs4, he4, hend, hst]; all_goals scalar_tac)) as ⟨o5, iter5, ho5, hs5, he5⟩
  simp only [ho5]
  step as ⟨p5, hp5⟩
  step as ⟨q5, hq5⟩
  have hq5v : q5.val = 13 := by
    simp [hq5, hp5, hst, hs4, he4]
    all_goals scalar_tac
  step as ⟨x5, hx5⟩
  simp [hb, hq5v] at hx5
  step with UScalar.cast.step_spec as ⟨c5, hc5⟩
  have hc5v : c5.val = b13.val := by
    rw [hc5, UScalar.cast_val_eq, hx5]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s5, hsh5⟩
  have hsv5 : s5.val = 40 := by
    simp [hsh5, hst, hs4, he4]
    all_goals scalar_tac
  step as ⟨t5, ht5⟩
  have ht5v : t5.val = b13.val * 2^40 := by
    rw [ht5]
    simp [hsv5, hc5v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u5, hu5⟩
  simp [hwn4, hw] at hu5
  have hu5v : u5.val = b8.val + b9.val * 2^8 + b10.val * 2^16 + b11.val * 2^24 + b12.val * 2^32 := by rw [hu5]; exact hy4v
  step as ⟨y5, hy5⟩
  have hy5v : y5.val = b8.val + b9.val * 2^8 + b10.val * 2^16 + b11.val * 2^24 + b12.val * 2^32 + b13.val * 2^40 := by
    have hult : u5.val < 2^40 := by rw [hu5v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u5.val) (i := 40) hult b13.val
    have hadd : u5.val ||| b13.val * 2^40 = u5.val + b13.val * 2^40 := by
      calc u5.val ||| b13.val * 2^40
          = u5.val ||| 2^40 * b13.val := by rw [Nat.mul_comm]
        _ = 2^40 * b13.val ||| u5.val := Nat.lor_comm _ _
        _ = 2^40 * b13.val + u5.val := hor.symm
        _ = u5.val + b13.val * 2^40 := by ring
    simp only [hy5, UScalar.val_or, ht5v]
    rw [hadd, hu5v]
    all_goals ring
  step as ⟨wn5, hwn5⟩
  try simp only [spec_ok]
  -- j = 6: byte 14
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with (range_next_lt_spec iter5 (by simp [hs4, he4, hs5, he5, hend, hst]; all_goals scalar_tac)) as ⟨o6, iter6, ho6, hs6, he6⟩
  simp only [ho6]
  step as ⟨p6, hp6⟩
  step as ⟨q6, hq6⟩
  have hq6v : q6.val = 14 := by
    simp [hq6, hp6, hst, hs4, he4, hs5, he5]
    all_goals scalar_tac
  step as ⟨x6, hx6⟩
  simp [hb, hq6v] at hx6
  step with UScalar.cast.step_spec as ⟨c6, hc6⟩
  have hc6v : c6.val = b14.val := by
    rw [hc6, UScalar.cast_val_eq, hx6]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s6, hsh6⟩
  have hsv6 : s6.val = 48 := by
    simp [hsh6, hst, hs4, he4, hs5, he5]
    all_goals scalar_tac
  step as ⟨t6, ht6⟩
  have ht6v : t6.val = b14.val * 2^48 := by
    rw [ht6]
    simp [hsv6, hc6v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u6, hu6⟩
  simp [hwn5, hw] at hu6
  have hu6v : u6.val = b8.val + b9.val * 2^8 + b10.val * 2^16 + b11.val * 2^24 + b12.val * 2^32 + b13.val * 2^40 := by rw [hu6]; exact hy5v
  step as ⟨y6, hy6⟩
  have hy6v : y6.val = b8.val + b9.val * 2^8 + b10.val * 2^16 + b11.val * 2^24 + b12.val * 2^32 + b13.val * 2^40 + b14.val * 2^48 := by
    have hult : u6.val < 2^48 := by rw [hu6v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u6.val) (i := 48) hult b14.val
    have hadd : u6.val ||| b14.val * 2^48 = u6.val + b14.val * 2^48 := by
      calc u6.val ||| b14.val * 2^48
          = u6.val ||| 2^48 * b14.val := by rw [Nat.mul_comm]
        _ = 2^48 * b14.val ||| u6.val := Nat.lor_comm _ _
        _ = 2^48 * b14.val + u6.val := hor.symm
        _ = u6.val + b14.val * 2^48 := by ring
    simp only [hy6, UScalar.val_or, ht6v]
    rw [hadd, hu6v]
    all_goals ring
  step as ⟨wn6, hwn6⟩
  try simp only [spec_ok]
  -- j = 7: byte 15
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with (range_next_lt_spec iter6 (by simp [hs4, he4, hs5, he5, hs6, he6, hend, hst]; all_goals scalar_tac)) as ⟨o7, iter7, ho7, hs7, he7⟩
  simp only [ho7]
  step as ⟨p7, hp7⟩
  step as ⟨q7, hq7⟩
  have hq7v : q7.val = 15 := by
    simp [hq7, hp7, hst, hs4, he4, hs5, he5, hs6, he6]
    all_goals scalar_tac
  step as ⟨x7, hx7⟩
  simp [hb, hq7v] at hx7
  step with UScalar.cast.step_spec as ⟨c7, hc7⟩
  have hc7v : c7.val = b15.val := by
    rw [hc7, UScalar.cast_val_eq, hx7]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s7, hsh7⟩
  have hsv7 : s7.val = 56 := by
    simp [hsh7, hst, hs4, he4, hs5, he5, hs6, he6]
    all_goals scalar_tac
  step as ⟨t7, ht7⟩
  have ht7v : t7.val = b15.val * 2^56 := by
    rw [ht7]
    simp [hsv7, hc7v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u7, hu7⟩
  simp [hwn6, hw] at hu7
  have hu7v : u7.val = b8.val + b9.val * 2^8 + b10.val * 2^16 + b11.val * 2^24 + b12.val * 2^32 + b13.val * 2^40 + b14.val * 2^48 := by rw [hu7]; exact hy6v
  step as ⟨y7, hy7⟩
  have hy7v : y7.val = b8.val + b9.val * 2^8 + b10.val * 2^16 + b11.val * 2^24 + b12.val * 2^32 + b13.val * 2^40 + b14.val * 2^48 + b15.val * 2^56 := by
    have hult : u7.val < 2^56 := by rw [hu7v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u7.val) (i := 56) hult b15.val
    have hadd : u7.val ||| b15.val * 2^56 = u7.val + b15.val * 2^56 := by
      calc u7.val ||| b15.val * 2^56
          = u7.val ||| 2^56 * b15.val := by rw [Nat.mul_comm]
        _ = 2^56 * b15.val ||| u7.val := Nat.lor_comm _ _
        _ = 2^56 * b15.val + u7.val := hor.symm
        _ = u7.val + b15.val * 2^56 := by ring
    simp only [hy7, UScalar.val_or, ht7v]
    rw [hadd, hu7v]
    all_goals ring
  step as ⟨wn7, hwn7⟩
  try simp only [spec_ok]
  -- exit (8 ≥ 8)
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with (range_next_ge_spec iter7 (by simp [he7, he6, he5, he4, hend, hs7, hs6, hs5, hs4]; all_goals scalar_tac)) as ⟨oX, iterX, hoX, hrX⟩
  simp only [hoX]
  try simp only [spec_ok]
  refine ⟨y7, ?_, hy7v⟩
  simp [hwn4, hwn5, hwn6, hwn7, hw, Array.set_val_eq]

/-- Inner byte loop, outer index 1: word 1 accumulates bytes
    8..15 little-endian; the other words are untouched.
    Iterations 0..3 here; 4..7 + exit in `bytes_word_loop_tail_1`
    (the 8-fold monolith exceeds the elaboration budget — METHOD 4). -/
theorem bytes_word_loop_spec_1
    (bytes : Std.Array Std.U8 64#usize)
    (words : Std.Array Std.U64 8#usize)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63 : Std.U8)
    (w0 w1 w2 w3 w4 w5 w6 w7 : U64)
    (hb : (↑bytes : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63])
    (hw : (↑words : List U64) = [w0, w1, w2, w3, w4, w5, w6, w7])
    (hz : w1.val = 0) :
    backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0 { start := 0#usize, «end» := 8#usize } bytes words 1#usize
      ⦃ ws => ∃ v : U64, (↑ws : List U64) = [w0, v, w2, w3, w4, w5, w6, w7] ∧
          v.val = b8.val + b9.val * 2^8 + b10.val * 2^16 + b11.val * 2^24 + b12.val * 2^32 + b13.val * 2^40 + b14.val * 2^48 + b15.val * 2^56 ⦄ := by
  have hsz64 : (U64.size : ℕ) = 2^64 := by scalar_tac
  have hbb8 : b8.val < 2^8 := by scalar_tac
  have hbb9 : b9.val < 2^8 := by scalar_tac
  have hbb10 : b10.val < 2^8 := by scalar_tac
  have hbb11 : b11.val < 2^8 := by scalar_tac
  unfold backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0
  -- j = 0: byte 8
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with range_next_lt_spec as ⟨o0, iter0, ho0, hs0, he0⟩
  simp only [ho0]
  step as ⟨p0, hp0⟩
  step as ⟨q0, hq0⟩
  have hq0v : q0.val = 8 := by
    simp [hq0, hp0]
    all_goals scalar_tac
  step as ⟨x0, hx0⟩
  simp [hb, hq0v] at hx0
  step with UScalar.cast.step_spec as ⟨c0, hc0⟩
  have hc0v : c0.val = b8.val := by
    rw [hc0, UScalar.cast_val_eq, hx0]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s0, hsh0⟩
  have hsv0 : s0.val = 0 := by
    simp [hsh0]
    all_goals scalar_tac
  step as ⟨t0, ht0⟩
  have ht0v : t0.val = b8.val * 2^0 := by
    rw [ht0]
    simp [hsv0, hc0v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u0, hu0⟩
  simp [hw] at hu0
  have hu0v : u0.val = 0 := by rw [hu0]; exact hz
  step as ⟨y0, hy0⟩
  have hy0v : y0.val = b8.val := by
    simp [hy0, UScalar.val_or, hu0v, ht0v]
  step as ⟨wn0, hwn0⟩
  try simp only [spec_ok]
  -- j = 1: byte 9
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with range_next_lt_spec as ⟨o1, iter1, ho1, hs1, he1⟩
  simp only [ho1]
  step as ⟨p1, hp1⟩
  step as ⟨q1, hq1⟩
  have hq1v : q1.val = 9 := by
    simp [hq1, hp1, hs0, he0]
    all_goals scalar_tac
  step as ⟨x1, hx1⟩
  simp [hb, hq1v] at hx1
  step with UScalar.cast.step_spec as ⟨c1, hc1⟩
  have hc1v : c1.val = b9.val := by
    rw [hc1, UScalar.cast_val_eq, hx1]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s1, hsh1⟩
  have hsv1 : s1.val = 8 := by
    simp [hsh1, hs0, he0]
    all_goals scalar_tac
  step as ⟨t1, ht1⟩
  have ht1v : t1.val = b9.val * 2^8 := by
    rw [ht1]
    simp [hsv1, hc1v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u1, hu1⟩
  simp [hwn0, hw] at hu1
  have hu1v : u1.val = b8.val := by rw [hu1]; exact hy0v
  step as ⟨y1, hy1⟩
  have hy1v : y1.val = b8.val + b9.val * 2^8 := by
    have hult : u1.val < 2^8 := by rw [hu1v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u1.val) (i := 8) hult b9.val
    have hadd : u1.val ||| b9.val * 2^8 = u1.val + b9.val * 2^8 := by
      calc u1.val ||| b9.val * 2^8
          = u1.val ||| 2^8 * b9.val := by rw [Nat.mul_comm]
        _ = 2^8 * b9.val ||| u1.val := Nat.lor_comm _ _
        _ = 2^8 * b9.val + u1.val := hor.symm
        _ = u1.val + b9.val * 2^8 := by ring
    simp only [hy1, UScalar.val_or, ht1v]
    rw [hadd, hu1v]
    all_goals ring
  step as ⟨wn1, hwn1⟩
  try simp only [spec_ok]
  -- j = 2: byte 10
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with range_next_lt_spec as ⟨o2, iter2, ho2, hs2, he2⟩
  simp only [ho2]
  step as ⟨p2, hp2⟩
  step as ⟨q2, hq2⟩
  have hq2v : q2.val = 10 := by
    simp [hq2, hp2, hs0, he0, hs1, he1]
    all_goals scalar_tac
  step as ⟨x2, hx2⟩
  simp [hb, hq2v] at hx2
  step with UScalar.cast.step_spec as ⟨c2, hc2⟩
  have hc2v : c2.val = b10.val := by
    rw [hc2, UScalar.cast_val_eq, hx2]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s2, hsh2⟩
  have hsv2 : s2.val = 16 := by
    simp [hsh2, hs0, he0, hs1, he1]
    all_goals scalar_tac
  step as ⟨t2, ht2⟩
  have ht2v : t2.val = b10.val * 2^16 := by
    rw [ht2]
    simp [hsv2, hc2v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u2, hu2⟩
  simp [hwn1, hw] at hu2
  have hu2v : u2.val = b8.val + b9.val * 2^8 := by rw [hu2]; exact hy1v
  step as ⟨y2, hy2⟩
  have hy2v : y2.val = b8.val + b9.val * 2^8 + b10.val * 2^16 := by
    have hult : u2.val < 2^16 := by rw [hu2v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u2.val) (i := 16) hult b10.val
    have hadd : u2.val ||| b10.val * 2^16 = u2.val + b10.val * 2^16 := by
      calc u2.val ||| b10.val * 2^16
          = u2.val ||| 2^16 * b10.val := by rw [Nat.mul_comm]
        _ = 2^16 * b10.val ||| u2.val := Nat.lor_comm _ _
        _ = 2^16 * b10.val + u2.val := hor.symm
        _ = u2.val + b10.val * 2^16 := by ring
    simp only [hy2, UScalar.val_or, ht2v]
    rw [hadd, hu2v]
    all_goals ring
  step as ⟨wn2, hwn2⟩
  try simp only [spec_ok]
  -- j = 3: byte 11
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with range_next_lt_spec as ⟨o3, iter3, ho3, hs3, he3⟩
  simp only [ho3]
  step as ⟨p3, hp3⟩
  step as ⟨q3, hq3⟩
  have hq3v : q3.val = 11 := by
    simp [hq3, hp3, hs0, he0, hs1, he1, hs2, he2]
    all_goals scalar_tac
  step as ⟨x3, hx3⟩
  simp [hb, hq3v] at hx3
  step with UScalar.cast.step_spec as ⟨c3, hc3⟩
  have hc3v : c3.val = b11.val := by
    rw [hc3, UScalar.cast_val_eq, hx3]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s3, hsh3⟩
  have hsv3 : s3.val = 24 := by
    simp [hsh3, hs0, he0, hs1, he1, hs2, he2]
    all_goals scalar_tac
  step as ⟨t3, ht3⟩
  have ht3v : t3.val = b11.val * 2^24 := by
    rw [ht3]
    simp [hsv3, hc3v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u3, hu3⟩
  simp [hwn2, hw] at hu3
  have hu3v : u3.val = b8.val + b9.val * 2^8 + b10.val * 2^16 := by rw [hu3]; exact hy2v
  step as ⟨y3, hy3⟩
  have hy3v : y3.val = b8.val + b9.val * 2^8 + b10.val * 2^16 + b11.val * 2^24 := by
    have hult : u3.val < 2^24 := by rw [hu3v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u3.val) (i := 24) hult b11.val
    have hadd : u3.val ||| b11.val * 2^24 = u3.val + b11.val * 2^24 := by
      calc u3.val ||| b11.val * 2^24
          = u3.val ||| 2^24 * b11.val := by rw [Nat.mul_comm]
        _ = 2^24 * b11.val ||| u3.val := Nat.lor_comm _ _
        _ = 2^24 * b11.val + u3.val := hor.symm
        _ = u3.val + b11.val * 2^24 := by ring
    simp only [hy3, UScalar.val_or, ht3v]
    rw [hadd, hu3v]
    all_goals ring
  step as ⟨wn3, hwn3⟩
  try simp only [spec_ok]
  -- refold and hand over to the tail lemma at the j = 4 boundary
  show backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0 iter3 bytes wn3 1#usize
    ⦃ ws => ∃ v : U64, (↑ws : List U64) = [w0, v, w2, w3, w4, w5, w6, w7] ∧
        v.val = b8.val + b9.val * 2^8 + b10.val * 2^16 + b11.val * 2^24 + b12.val * 2^32 + b13.val * 2^40 + b14.val * 2^48 + b15.val * 2^56 ⦄
  have hwn3l : (↑wn3 : List U64) = [w0, y3, w2, w3, w4, w5, w6, w7] := by
    simp [hwn0, hwn1, hwn2, hwn3, hw, Array.set_val_eq]
  have hst3 : iter3.start.val = 4 := by
    simp [hs3, hs2, hs1, hs0]
    all_goals scalar_tac
  have hend3 : iter3.«end» = 8#usize := by
    simp [he3, he2, he1, he0]
  exact bytes_word_loop_tail_1 bytes wn3 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63
    w0 y3 w2 w3 w4 w5 w6 w7 iter3 hb hwn3l hst3 hend3 hy3v

/-- Inner byte loop for word 2, iterations 4..7 + exit: continues the
    accumulation from the mid-state (bytes 16..19 absorbed). -/
theorem bytes_word_loop_tail_2
    (bytes : Std.Array Std.U8 64#usize)
    (words : Std.Array Std.U64 8#usize)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63 : Std.U8)
    (w0 w1 w2 w3 w4 w5 w6 w7 : U64)
    (iter : core.ops.range.Range Std.Usize)
    (hb : (↑bytes : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63])
    (hw : (↑words : List U64) = [w0, w1, w2, w3, w4, w5, w6, w7])
    (hst : iter.start.val = 4) (hend : iter.«end» = 8#usize)
    (hacc : w2.val = b16.val + b17.val * 2^8 + b18.val * 2^16 + b19.val * 2^24) :
    backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0 iter bytes words 2#usize
      ⦃ ws => ∃ v : U64, (↑ws : List U64) = [w0, w1, v, w3, w4, w5, w6, w7] ∧
          v.val = b16.val + b17.val * 2^8 + b18.val * 2^16 + b19.val * 2^24 + b20.val * 2^32 + b21.val * 2^40 + b22.val * 2^48 + b23.val * 2^56 ⦄ := by
  have hsz64 : (U64.size : ℕ) = 2^64 := by scalar_tac
  have hbb16 : b16.val < 2^8 := by scalar_tac
  have hbb17 : b17.val < 2^8 := by scalar_tac
  have hbb18 : b18.val < 2^8 := by scalar_tac
  have hbb19 : b19.val < 2^8 := by scalar_tac
  have hbb20 : b20.val < 2^8 := by scalar_tac
  have hbb21 : b21.val < 2^8 := by scalar_tac
  have hbb22 : b22.val < 2^8 := by scalar_tac
  have hbb23 : b23.val < 2^8 := by scalar_tac
  unfold backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0
  -- j = 4: byte 20
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with (range_next_lt_spec iter (by simp [hend, hst]; all_goals scalar_tac)) as ⟨o4, iter4, ho4, hs4, he4⟩
  simp only [ho4]
  step as ⟨p4, hp4⟩
  step as ⟨q4, hq4⟩
  have hq4v : q4.val = 20 := by
    simp [hq4, hp4, hst]
    all_goals scalar_tac
  step as ⟨x4, hx4⟩
  simp [hb, hq4v] at hx4
  step with UScalar.cast.step_spec as ⟨c4, hc4⟩
  have hc4v : c4.val = b20.val := by
    rw [hc4, UScalar.cast_val_eq, hx4]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s4, hsh4⟩
  have hsv4 : s4.val = 32 := by
    simp [hsh4, hst]
    all_goals scalar_tac
  step as ⟨t4, ht4⟩
  have ht4v : t4.val = b20.val * 2^32 := by
    rw [ht4]
    simp [hsv4, hc4v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u4, hu4⟩
  simp [hw] at hu4
  have hu4v : u4.val = b16.val + b17.val * 2^8 + b18.val * 2^16 + b19.val * 2^24 := by rw [hu4]; exact hacc
  step as ⟨y4, hy4⟩
  have hy4v : y4.val = b16.val + b17.val * 2^8 + b18.val * 2^16 + b19.val * 2^24 + b20.val * 2^32 := by
    have hult : u4.val < 2^32 := by rw [hu4v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u4.val) (i := 32) hult b20.val
    have hadd : u4.val ||| b20.val * 2^32 = u4.val + b20.val * 2^32 := by
      calc u4.val ||| b20.val * 2^32
          = u4.val ||| 2^32 * b20.val := by rw [Nat.mul_comm]
        _ = 2^32 * b20.val ||| u4.val := Nat.lor_comm _ _
        _ = 2^32 * b20.val + u4.val := hor.symm
        _ = u4.val + b20.val * 2^32 := by ring
    simp only [hy4, UScalar.val_or, ht4v]
    rw [hadd, hu4v]
    all_goals ring
  step as ⟨wn4, hwn4⟩
  try simp only [spec_ok]
  -- j = 5: byte 21
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with (range_next_lt_spec iter4 (by simp [hs4, he4, hend, hst]; all_goals scalar_tac)) as ⟨o5, iter5, ho5, hs5, he5⟩
  simp only [ho5]
  step as ⟨p5, hp5⟩
  step as ⟨q5, hq5⟩
  have hq5v : q5.val = 21 := by
    simp [hq5, hp5, hst, hs4, he4]
    all_goals scalar_tac
  step as ⟨x5, hx5⟩
  simp [hb, hq5v] at hx5
  step with UScalar.cast.step_spec as ⟨c5, hc5⟩
  have hc5v : c5.val = b21.val := by
    rw [hc5, UScalar.cast_val_eq, hx5]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s5, hsh5⟩
  have hsv5 : s5.val = 40 := by
    simp [hsh5, hst, hs4, he4]
    all_goals scalar_tac
  step as ⟨t5, ht5⟩
  have ht5v : t5.val = b21.val * 2^40 := by
    rw [ht5]
    simp [hsv5, hc5v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u5, hu5⟩
  simp [hwn4, hw] at hu5
  have hu5v : u5.val = b16.val + b17.val * 2^8 + b18.val * 2^16 + b19.val * 2^24 + b20.val * 2^32 := by rw [hu5]; exact hy4v
  step as ⟨y5, hy5⟩
  have hy5v : y5.val = b16.val + b17.val * 2^8 + b18.val * 2^16 + b19.val * 2^24 + b20.val * 2^32 + b21.val * 2^40 := by
    have hult : u5.val < 2^40 := by rw [hu5v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u5.val) (i := 40) hult b21.val
    have hadd : u5.val ||| b21.val * 2^40 = u5.val + b21.val * 2^40 := by
      calc u5.val ||| b21.val * 2^40
          = u5.val ||| 2^40 * b21.val := by rw [Nat.mul_comm]
        _ = 2^40 * b21.val ||| u5.val := Nat.lor_comm _ _
        _ = 2^40 * b21.val + u5.val := hor.symm
        _ = u5.val + b21.val * 2^40 := by ring
    simp only [hy5, UScalar.val_or, ht5v]
    rw [hadd, hu5v]
    all_goals ring
  step as ⟨wn5, hwn5⟩
  try simp only [spec_ok]
  -- j = 6: byte 22
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with (range_next_lt_spec iter5 (by simp [hs4, he4, hs5, he5, hend, hst]; all_goals scalar_tac)) as ⟨o6, iter6, ho6, hs6, he6⟩
  simp only [ho6]
  step as ⟨p6, hp6⟩
  step as ⟨q6, hq6⟩
  have hq6v : q6.val = 22 := by
    simp [hq6, hp6, hst, hs4, he4, hs5, he5]
    all_goals scalar_tac
  step as ⟨x6, hx6⟩
  simp [hb, hq6v] at hx6
  step with UScalar.cast.step_spec as ⟨c6, hc6⟩
  have hc6v : c6.val = b22.val := by
    rw [hc6, UScalar.cast_val_eq, hx6]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s6, hsh6⟩
  have hsv6 : s6.val = 48 := by
    simp [hsh6, hst, hs4, he4, hs5, he5]
    all_goals scalar_tac
  step as ⟨t6, ht6⟩
  have ht6v : t6.val = b22.val * 2^48 := by
    rw [ht6]
    simp [hsv6, hc6v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u6, hu6⟩
  simp [hwn5, hw] at hu6
  have hu6v : u6.val = b16.val + b17.val * 2^8 + b18.val * 2^16 + b19.val * 2^24 + b20.val * 2^32 + b21.val * 2^40 := by rw [hu6]; exact hy5v
  step as ⟨y6, hy6⟩
  have hy6v : y6.val = b16.val + b17.val * 2^8 + b18.val * 2^16 + b19.val * 2^24 + b20.val * 2^32 + b21.val * 2^40 + b22.val * 2^48 := by
    have hult : u6.val < 2^48 := by rw [hu6v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u6.val) (i := 48) hult b22.val
    have hadd : u6.val ||| b22.val * 2^48 = u6.val + b22.val * 2^48 := by
      calc u6.val ||| b22.val * 2^48
          = u6.val ||| 2^48 * b22.val := by rw [Nat.mul_comm]
        _ = 2^48 * b22.val ||| u6.val := Nat.lor_comm _ _
        _ = 2^48 * b22.val + u6.val := hor.symm
        _ = u6.val + b22.val * 2^48 := by ring
    simp only [hy6, UScalar.val_or, ht6v]
    rw [hadd, hu6v]
    all_goals ring
  step as ⟨wn6, hwn6⟩
  try simp only [spec_ok]
  -- j = 7: byte 23
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with (range_next_lt_spec iter6 (by simp [hs4, he4, hs5, he5, hs6, he6, hend, hst]; all_goals scalar_tac)) as ⟨o7, iter7, ho7, hs7, he7⟩
  simp only [ho7]
  step as ⟨p7, hp7⟩
  step as ⟨q7, hq7⟩
  have hq7v : q7.val = 23 := by
    simp [hq7, hp7, hst, hs4, he4, hs5, he5, hs6, he6]
    all_goals scalar_tac
  step as ⟨x7, hx7⟩
  simp [hb, hq7v] at hx7
  step with UScalar.cast.step_spec as ⟨c7, hc7⟩
  have hc7v : c7.val = b23.val := by
    rw [hc7, UScalar.cast_val_eq, hx7]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s7, hsh7⟩
  have hsv7 : s7.val = 56 := by
    simp [hsh7, hst, hs4, he4, hs5, he5, hs6, he6]
    all_goals scalar_tac
  step as ⟨t7, ht7⟩
  have ht7v : t7.val = b23.val * 2^56 := by
    rw [ht7]
    simp [hsv7, hc7v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u7, hu7⟩
  simp [hwn6, hw] at hu7
  have hu7v : u7.val = b16.val + b17.val * 2^8 + b18.val * 2^16 + b19.val * 2^24 + b20.val * 2^32 + b21.val * 2^40 + b22.val * 2^48 := by rw [hu7]; exact hy6v
  step as ⟨y7, hy7⟩
  have hy7v : y7.val = b16.val + b17.val * 2^8 + b18.val * 2^16 + b19.val * 2^24 + b20.val * 2^32 + b21.val * 2^40 + b22.val * 2^48 + b23.val * 2^56 := by
    have hult : u7.val < 2^56 := by rw [hu7v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u7.val) (i := 56) hult b23.val
    have hadd : u7.val ||| b23.val * 2^56 = u7.val + b23.val * 2^56 := by
      calc u7.val ||| b23.val * 2^56
          = u7.val ||| 2^56 * b23.val := by rw [Nat.mul_comm]
        _ = 2^56 * b23.val ||| u7.val := Nat.lor_comm _ _
        _ = 2^56 * b23.val + u7.val := hor.symm
        _ = u7.val + b23.val * 2^56 := by ring
    simp only [hy7, UScalar.val_or, ht7v]
    rw [hadd, hu7v]
    all_goals ring
  step as ⟨wn7, hwn7⟩
  try simp only [spec_ok]
  -- exit (8 ≥ 8)
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with (range_next_ge_spec iter7 (by simp [he7, he6, he5, he4, hend, hs7, hs6, hs5, hs4]; all_goals scalar_tac)) as ⟨oX, iterX, hoX, hrX⟩
  simp only [hoX]
  try simp only [spec_ok]
  refine ⟨y7, ?_, hy7v⟩
  simp [hwn4, hwn5, hwn6, hwn7, hw, Array.set_val_eq]

/-- Inner byte loop, outer index 2: word 2 accumulates bytes
    16..23 little-endian; the other words are untouched.
    Iterations 0..3 here; 4..7 + exit in `bytes_word_loop_tail_2`
    (the 8-fold monolith exceeds the elaboration budget — METHOD 4). -/
theorem bytes_word_loop_spec_2
    (bytes : Std.Array Std.U8 64#usize)
    (words : Std.Array Std.U64 8#usize)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63 : Std.U8)
    (w0 w1 w2 w3 w4 w5 w6 w7 : U64)
    (hb : (↑bytes : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63])
    (hw : (↑words : List U64) = [w0, w1, w2, w3, w4, w5, w6, w7])
    (hz : w2.val = 0) :
    backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0 { start := 0#usize, «end» := 8#usize } bytes words 2#usize
      ⦃ ws => ∃ v : U64, (↑ws : List U64) = [w0, w1, v, w3, w4, w5, w6, w7] ∧
          v.val = b16.val + b17.val * 2^8 + b18.val * 2^16 + b19.val * 2^24 + b20.val * 2^32 + b21.val * 2^40 + b22.val * 2^48 + b23.val * 2^56 ⦄ := by
  have hsz64 : (U64.size : ℕ) = 2^64 := by scalar_tac
  have hbb16 : b16.val < 2^8 := by scalar_tac
  have hbb17 : b17.val < 2^8 := by scalar_tac
  have hbb18 : b18.val < 2^8 := by scalar_tac
  have hbb19 : b19.val < 2^8 := by scalar_tac
  unfold backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0
  -- j = 0: byte 16
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with range_next_lt_spec as ⟨o0, iter0, ho0, hs0, he0⟩
  simp only [ho0]
  step as ⟨p0, hp0⟩
  step as ⟨q0, hq0⟩
  have hq0v : q0.val = 16 := by
    simp [hq0, hp0]
    all_goals scalar_tac
  step as ⟨x0, hx0⟩
  simp [hb, hq0v] at hx0
  step with UScalar.cast.step_spec as ⟨c0, hc0⟩
  have hc0v : c0.val = b16.val := by
    rw [hc0, UScalar.cast_val_eq, hx0]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s0, hsh0⟩
  have hsv0 : s0.val = 0 := by
    simp [hsh0]
    all_goals scalar_tac
  step as ⟨t0, ht0⟩
  have ht0v : t0.val = b16.val * 2^0 := by
    rw [ht0]
    simp [hsv0, hc0v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u0, hu0⟩
  simp [hw] at hu0
  have hu0v : u0.val = 0 := by rw [hu0]; exact hz
  step as ⟨y0, hy0⟩
  have hy0v : y0.val = b16.val := by
    simp [hy0, UScalar.val_or, hu0v, ht0v]
  step as ⟨wn0, hwn0⟩
  try simp only [spec_ok]
  -- j = 1: byte 17
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with range_next_lt_spec as ⟨o1, iter1, ho1, hs1, he1⟩
  simp only [ho1]
  step as ⟨p1, hp1⟩
  step as ⟨q1, hq1⟩
  have hq1v : q1.val = 17 := by
    simp [hq1, hp1, hs0, he0]
    all_goals scalar_tac
  step as ⟨x1, hx1⟩
  simp [hb, hq1v] at hx1
  step with UScalar.cast.step_spec as ⟨c1, hc1⟩
  have hc1v : c1.val = b17.val := by
    rw [hc1, UScalar.cast_val_eq, hx1]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s1, hsh1⟩
  have hsv1 : s1.val = 8 := by
    simp [hsh1, hs0, he0]
    all_goals scalar_tac
  step as ⟨t1, ht1⟩
  have ht1v : t1.val = b17.val * 2^8 := by
    rw [ht1]
    simp [hsv1, hc1v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u1, hu1⟩
  simp [hwn0, hw] at hu1
  have hu1v : u1.val = b16.val := by rw [hu1]; exact hy0v
  step as ⟨y1, hy1⟩
  have hy1v : y1.val = b16.val + b17.val * 2^8 := by
    have hult : u1.val < 2^8 := by rw [hu1v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u1.val) (i := 8) hult b17.val
    have hadd : u1.val ||| b17.val * 2^8 = u1.val + b17.val * 2^8 := by
      calc u1.val ||| b17.val * 2^8
          = u1.val ||| 2^8 * b17.val := by rw [Nat.mul_comm]
        _ = 2^8 * b17.val ||| u1.val := Nat.lor_comm _ _
        _ = 2^8 * b17.val + u1.val := hor.symm
        _ = u1.val + b17.val * 2^8 := by ring
    simp only [hy1, UScalar.val_or, ht1v]
    rw [hadd, hu1v]
    all_goals ring
  step as ⟨wn1, hwn1⟩
  try simp only [spec_ok]
  -- j = 2: byte 18
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with range_next_lt_spec as ⟨o2, iter2, ho2, hs2, he2⟩
  simp only [ho2]
  step as ⟨p2, hp2⟩
  step as ⟨q2, hq2⟩
  have hq2v : q2.val = 18 := by
    simp [hq2, hp2, hs0, he0, hs1, he1]
    all_goals scalar_tac
  step as ⟨x2, hx2⟩
  simp [hb, hq2v] at hx2
  step with UScalar.cast.step_spec as ⟨c2, hc2⟩
  have hc2v : c2.val = b18.val := by
    rw [hc2, UScalar.cast_val_eq, hx2]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s2, hsh2⟩
  have hsv2 : s2.val = 16 := by
    simp [hsh2, hs0, he0, hs1, he1]
    all_goals scalar_tac
  step as ⟨t2, ht2⟩
  have ht2v : t2.val = b18.val * 2^16 := by
    rw [ht2]
    simp [hsv2, hc2v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u2, hu2⟩
  simp [hwn1, hw] at hu2
  have hu2v : u2.val = b16.val + b17.val * 2^8 := by rw [hu2]; exact hy1v
  step as ⟨y2, hy2⟩
  have hy2v : y2.val = b16.val + b17.val * 2^8 + b18.val * 2^16 := by
    have hult : u2.val < 2^16 := by rw [hu2v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u2.val) (i := 16) hult b18.val
    have hadd : u2.val ||| b18.val * 2^16 = u2.val + b18.val * 2^16 := by
      calc u2.val ||| b18.val * 2^16
          = u2.val ||| 2^16 * b18.val := by rw [Nat.mul_comm]
        _ = 2^16 * b18.val ||| u2.val := Nat.lor_comm _ _
        _ = 2^16 * b18.val + u2.val := hor.symm
        _ = u2.val + b18.val * 2^16 := by ring
    simp only [hy2, UScalar.val_or, ht2v]
    rw [hadd, hu2v]
    all_goals ring
  step as ⟨wn2, hwn2⟩
  try simp only [spec_ok]
  -- j = 3: byte 19
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with range_next_lt_spec as ⟨o3, iter3, ho3, hs3, he3⟩
  simp only [ho3]
  step as ⟨p3, hp3⟩
  step as ⟨q3, hq3⟩
  have hq3v : q3.val = 19 := by
    simp [hq3, hp3, hs0, he0, hs1, he1, hs2, he2]
    all_goals scalar_tac
  step as ⟨x3, hx3⟩
  simp [hb, hq3v] at hx3
  step with UScalar.cast.step_spec as ⟨c3, hc3⟩
  have hc3v : c3.val = b19.val := by
    rw [hc3, UScalar.cast_val_eq, hx3]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s3, hsh3⟩
  have hsv3 : s3.val = 24 := by
    simp [hsh3, hs0, he0, hs1, he1, hs2, he2]
    all_goals scalar_tac
  step as ⟨t3, ht3⟩
  have ht3v : t3.val = b19.val * 2^24 := by
    rw [ht3]
    simp [hsv3, hc3v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u3, hu3⟩
  simp [hwn2, hw] at hu3
  have hu3v : u3.val = b16.val + b17.val * 2^8 + b18.val * 2^16 := by rw [hu3]; exact hy2v
  step as ⟨y3, hy3⟩
  have hy3v : y3.val = b16.val + b17.val * 2^8 + b18.val * 2^16 + b19.val * 2^24 := by
    have hult : u3.val < 2^24 := by rw [hu3v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u3.val) (i := 24) hult b19.val
    have hadd : u3.val ||| b19.val * 2^24 = u3.val + b19.val * 2^24 := by
      calc u3.val ||| b19.val * 2^24
          = u3.val ||| 2^24 * b19.val := by rw [Nat.mul_comm]
        _ = 2^24 * b19.val ||| u3.val := Nat.lor_comm _ _
        _ = 2^24 * b19.val + u3.val := hor.symm
        _ = u3.val + b19.val * 2^24 := by ring
    simp only [hy3, UScalar.val_or, ht3v]
    rw [hadd, hu3v]
    all_goals ring
  step as ⟨wn3, hwn3⟩
  try simp only [spec_ok]
  -- refold and hand over to the tail lemma at the j = 4 boundary
  show backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0 iter3 bytes wn3 2#usize
    ⦃ ws => ∃ v : U64, (↑ws : List U64) = [w0, w1, v, w3, w4, w5, w6, w7] ∧
        v.val = b16.val + b17.val * 2^8 + b18.val * 2^16 + b19.val * 2^24 + b20.val * 2^32 + b21.val * 2^40 + b22.val * 2^48 + b23.val * 2^56 ⦄
  have hwn3l : (↑wn3 : List U64) = [w0, w1, y3, w3, w4, w5, w6, w7] := by
    simp [hwn0, hwn1, hwn2, hwn3, hw, Array.set_val_eq]
  have hst3 : iter3.start.val = 4 := by
    simp [hs3, hs2, hs1, hs0]
    all_goals scalar_tac
  have hend3 : iter3.«end» = 8#usize := by
    simp [he3, he2, he1, he0]
  exact bytes_word_loop_tail_2 bytes wn3 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63
    w0 w1 y3 w3 w4 w5 w6 w7 iter3 hb hwn3l hst3 hend3 hy3v

/-- Inner byte loop for word 3, iterations 4..7 + exit: continues the
    accumulation from the mid-state (bytes 24..27 absorbed). -/
theorem bytes_word_loop_tail_3
    (bytes : Std.Array Std.U8 64#usize)
    (words : Std.Array Std.U64 8#usize)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63 : Std.U8)
    (w0 w1 w2 w3 w4 w5 w6 w7 : U64)
    (iter : core.ops.range.Range Std.Usize)
    (hb : (↑bytes : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63])
    (hw : (↑words : List U64) = [w0, w1, w2, w3, w4, w5, w6, w7])
    (hst : iter.start.val = 4) (hend : iter.«end» = 8#usize)
    (hacc : w3.val = b24.val + b25.val * 2^8 + b26.val * 2^16 + b27.val * 2^24) :
    backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0 iter bytes words 3#usize
      ⦃ ws => ∃ v : U64, (↑ws : List U64) = [w0, w1, w2, v, w4, w5, w6, w7] ∧
          v.val = b24.val + b25.val * 2^8 + b26.val * 2^16 + b27.val * 2^24 + b28.val * 2^32 + b29.val * 2^40 + b30.val * 2^48 + b31.val * 2^56 ⦄ := by
  have hsz64 : (U64.size : ℕ) = 2^64 := by scalar_tac
  have hbb24 : b24.val < 2^8 := by scalar_tac
  have hbb25 : b25.val < 2^8 := by scalar_tac
  have hbb26 : b26.val < 2^8 := by scalar_tac
  have hbb27 : b27.val < 2^8 := by scalar_tac
  have hbb28 : b28.val < 2^8 := by scalar_tac
  have hbb29 : b29.val < 2^8 := by scalar_tac
  have hbb30 : b30.val < 2^8 := by scalar_tac
  have hbb31 : b31.val < 2^8 := by scalar_tac
  unfold backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0
  -- j = 4: byte 28
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with (range_next_lt_spec iter (by simp [hend, hst]; all_goals scalar_tac)) as ⟨o4, iter4, ho4, hs4, he4⟩
  simp only [ho4]
  step as ⟨p4, hp4⟩
  step as ⟨q4, hq4⟩
  have hq4v : q4.val = 28 := by
    simp [hq4, hp4, hst]
    all_goals scalar_tac
  step as ⟨x4, hx4⟩
  simp [hb, hq4v] at hx4
  step with UScalar.cast.step_spec as ⟨c4, hc4⟩
  have hc4v : c4.val = b28.val := by
    rw [hc4, UScalar.cast_val_eq, hx4]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s4, hsh4⟩
  have hsv4 : s4.val = 32 := by
    simp [hsh4, hst]
    all_goals scalar_tac
  step as ⟨t4, ht4⟩
  have ht4v : t4.val = b28.val * 2^32 := by
    rw [ht4]
    simp [hsv4, hc4v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u4, hu4⟩
  simp [hw] at hu4
  have hu4v : u4.val = b24.val + b25.val * 2^8 + b26.val * 2^16 + b27.val * 2^24 := by rw [hu4]; exact hacc
  step as ⟨y4, hy4⟩
  have hy4v : y4.val = b24.val + b25.val * 2^8 + b26.val * 2^16 + b27.val * 2^24 + b28.val * 2^32 := by
    have hult : u4.val < 2^32 := by rw [hu4v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u4.val) (i := 32) hult b28.val
    have hadd : u4.val ||| b28.val * 2^32 = u4.val + b28.val * 2^32 := by
      calc u4.val ||| b28.val * 2^32
          = u4.val ||| 2^32 * b28.val := by rw [Nat.mul_comm]
        _ = 2^32 * b28.val ||| u4.val := Nat.lor_comm _ _
        _ = 2^32 * b28.val + u4.val := hor.symm
        _ = u4.val + b28.val * 2^32 := by ring
    simp only [hy4, UScalar.val_or, ht4v]
    rw [hadd, hu4v]
    all_goals ring
  step as ⟨wn4, hwn4⟩
  try simp only [spec_ok]
  -- j = 5: byte 29
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with (range_next_lt_spec iter4 (by simp [hs4, he4, hend, hst]; all_goals scalar_tac)) as ⟨o5, iter5, ho5, hs5, he5⟩
  simp only [ho5]
  step as ⟨p5, hp5⟩
  step as ⟨q5, hq5⟩
  have hq5v : q5.val = 29 := by
    simp [hq5, hp5, hst, hs4, he4]
    all_goals scalar_tac
  step as ⟨x5, hx5⟩
  simp [hb, hq5v] at hx5
  step with UScalar.cast.step_spec as ⟨c5, hc5⟩
  have hc5v : c5.val = b29.val := by
    rw [hc5, UScalar.cast_val_eq, hx5]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s5, hsh5⟩
  have hsv5 : s5.val = 40 := by
    simp [hsh5, hst, hs4, he4]
    all_goals scalar_tac
  step as ⟨t5, ht5⟩
  have ht5v : t5.val = b29.val * 2^40 := by
    rw [ht5]
    simp [hsv5, hc5v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u5, hu5⟩
  simp [hwn4, hw] at hu5
  have hu5v : u5.val = b24.val + b25.val * 2^8 + b26.val * 2^16 + b27.val * 2^24 + b28.val * 2^32 := by rw [hu5]; exact hy4v
  step as ⟨y5, hy5⟩
  have hy5v : y5.val = b24.val + b25.val * 2^8 + b26.val * 2^16 + b27.val * 2^24 + b28.val * 2^32 + b29.val * 2^40 := by
    have hult : u5.val < 2^40 := by rw [hu5v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u5.val) (i := 40) hult b29.val
    have hadd : u5.val ||| b29.val * 2^40 = u5.val + b29.val * 2^40 := by
      calc u5.val ||| b29.val * 2^40
          = u5.val ||| 2^40 * b29.val := by rw [Nat.mul_comm]
        _ = 2^40 * b29.val ||| u5.val := Nat.lor_comm _ _
        _ = 2^40 * b29.val + u5.val := hor.symm
        _ = u5.val + b29.val * 2^40 := by ring
    simp only [hy5, UScalar.val_or, ht5v]
    rw [hadd, hu5v]
    all_goals ring
  step as ⟨wn5, hwn5⟩
  try simp only [spec_ok]
  -- j = 6: byte 30
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with (range_next_lt_spec iter5 (by simp [hs4, he4, hs5, he5, hend, hst]; all_goals scalar_tac)) as ⟨o6, iter6, ho6, hs6, he6⟩
  simp only [ho6]
  step as ⟨p6, hp6⟩
  step as ⟨q6, hq6⟩
  have hq6v : q6.val = 30 := by
    simp [hq6, hp6, hst, hs4, he4, hs5, he5]
    all_goals scalar_tac
  step as ⟨x6, hx6⟩
  simp [hb, hq6v] at hx6
  step with UScalar.cast.step_spec as ⟨c6, hc6⟩
  have hc6v : c6.val = b30.val := by
    rw [hc6, UScalar.cast_val_eq, hx6]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s6, hsh6⟩
  have hsv6 : s6.val = 48 := by
    simp [hsh6, hst, hs4, he4, hs5, he5]
    all_goals scalar_tac
  step as ⟨t6, ht6⟩
  have ht6v : t6.val = b30.val * 2^48 := by
    rw [ht6]
    simp [hsv6, hc6v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u6, hu6⟩
  simp [hwn5, hw] at hu6
  have hu6v : u6.val = b24.val + b25.val * 2^8 + b26.val * 2^16 + b27.val * 2^24 + b28.val * 2^32 + b29.val * 2^40 := by rw [hu6]; exact hy5v
  step as ⟨y6, hy6⟩
  have hy6v : y6.val = b24.val + b25.val * 2^8 + b26.val * 2^16 + b27.val * 2^24 + b28.val * 2^32 + b29.val * 2^40 + b30.val * 2^48 := by
    have hult : u6.val < 2^48 := by rw [hu6v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u6.val) (i := 48) hult b30.val
    have hadd : u6.val ||| b30.val * 2^48 = u6.val + b30.val * 2^48 := by
      calc u6.val ||| b30.val * 2^48
          = u6.val ||| 2^48 * b30.val := by rw [Nat.mul_comm]
        _ = 2^48 * b30.val ||| u6.val := Nat.lor_comm _ _
        _ = 2^48 * b30.val + u6.val := hor.symm
        _ = u6.val + b30.val * 2^48 := by ring
    simp only [hy6, UScalar.val_or, ht6v]
    rw [hadd, hu6v]
    all_goals ring
  step as ⟨wn6, hwn6⟩
  try simp only [spec_ok]
  -- j = 7: byte 31
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with (range_next_lt_spec iter6 (by simp [hs4, he4, hs5, he5, hs6, he6, hend, hst]; all_goals scalar_tac)) as ⟨o7, iter7, ho7, hs7, he7⟩
  simp only [ho7]
  step as ⟨p7, hp7⟩
  step as ⟨q7, hq7⟩
  have hq7v : q7.val = 31 := by
    simp [hq7, hp7, hst, hs4, he4, hs5, he5, hs6, he6]
    all_goals scalar_tac
  step as ⟨x7, hx7⟩
  simp [hb, hq7v] at hx7
  step with UScalar.cast.step_spec as ⟨c7, hc7⟩
  have hc7v : c7.val = b31.val := by
    rw [hc7, UScalar.cast_val_eq, hx7]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s7, hsh7⟩
  have hsv7 : s7.val = 56 := by
    simp [hsh7, hst, hs4, he4, hs5, he5, hs6, he6]
    all_goals scalar_tac
  step as ⟨t7, ht7⟩
  have ht7v : t7.val = b31.val * 2^56 := by
    rw [ht7]
    simp [hsv7, hc7v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u7, hu7⟩
  simp [hwn6, hw] at hu7
  have hu7v : u7.val = b24.val + b25.val * 2^8 + b26.val * 2^16 + b27.val * 2^24 + b28.val * 2^32 + b29.val * 2^40 + b30.val * 2^48 := by rw [hu7]; exact hy6v
  step as ⟨y7, hy7⟩
  have hy7v : y7.val = b24.val + b25.val * 2^8 + b26.val * 2^16 + b27.val * 2^24 + b28.val * 2^32 + b29.val * 2^40 + b30.val * 2^48 + b31.val * 2^56 := by
    have hult : u7.val < 2^56 := by rw [hu7v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u7.val) (i := 56) hult b31.val
    have hadd : u7.val ||| b31.val * 2^56 = u7.val + b31.val * 2^56 := by
      calc u7.val ||| b31.val * 2^56
          = u7.val ||| 2^56 * b31.val := by rw [Nat.mul_comm]
        _ = 2^56 * b31.val ||| u7.val := Nat.lor_comm _ _
        _ = 2^56 * b31.val + u7.val := hor.symm
        _ = u7.val + b31.val * 2^56 := by ring
    simp only [hy7, UScalar.val_or, ht7v]
    rw [hadd, hu7v]
    all_goals ring
  step as ⟨wn7, hwn7⟩
  try simp only [spec_ok]
  -- exit (8 ≥ 8)
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with (range_next_ge_spec iter7 (by simp [he7, he6, he5, he4, hend, hs7, hs6, hs5, hs4]; all_goals scalar_tac)) as ⟨oX, iterX, hoX, hrX⟩
  simp only [hoX]
  try simp only [spec_ok]
  refine ⟨y7, ?_, hy7v⟩
  simp [hwn4, hwn5, hwn6, hwn7, hw, Array.set_val_eq]

/-- Inner byte loop, outer index 3: word 3 accumulates bytes
    24..31 little-endian; the other words are untouched.
    Iterations 0..3 here; 4..7 + exit in `bytes_word_loop_tail_3`
    (the 8-fold monolith exceeds the elaboration budget — METHOD 4). -/
theorem bytes_word_loop_spec_3
    (bytes : Std.Array Std.U8 64#usize)
    (words : Std.Array Std.U64 8#usize)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63 : Std.U8)
    (w0 w1 w2 w3 w4 w5 w6 w7 : U64)
    (hb : (↑bytes : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63])
    (hw : (↑words : List U64) = [w0, w1, w2, w3, w4, w5, w6, w7])
    (hz : w3.val = 0) :
    backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0 { start := 0#usize, «end» := 8#usize } bytes words 3#usize
      ⦃ ws => ∃ v : U64, (↑ws : List U64) = [w0, w1, w2, v, w4, w5, w6, w7] ∧
          v.val = b24.val + b25.val * 2^8 + b26.val * 2^16 + b27.val * 2^24 + b28.val * 2^32 + b29.val * 2^40 + b30.val * 2^48 + b31.val * 2^56 ⦄ := by
  have hsz64 : (U64.size : ℕ) = 2^64 := by scalar_tac
  have hbb24 : b24.val < 2^8 := by scalar_tac
  have hbb25 : b25.val < 2^8 := by scalar_tac
  have hbb26 : b26.val < 2^8 := by scalar_tac
  have hbb27 : b27.val < 2^8 := by scalar_tac
  unfold backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0
  -- j = 0: byte 24
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with range_next_lt_spec as ⟨o0, iter0, ho0, hs0, he0⟩
  simp only [ho0]
  step as ⟨p0, hp0⟩
  step as ⟨q0, hq0⟩
  have hq0v : q0.val = 24 := by
    simp [hq0, hp0]
    all_goals scalar_tac
  step as ⟨x0, hx0⟩
  simp [hb, hq0v] at hx0
  step with UScalar.cast.step_spec as ⟨c0, hc0⟩
  have hc0v : c0.val = b24.val := by
    rw [hc0, UScalar.cast_val_eq, hx0]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s0, hsh0⟩
  have hsv0 : s0.val = 0 := by
    simp [hsh0]
    all_goals scalar_tac
  step as ⟨t0, ht0⟩
  have ht0v : t0.val = b24.val * 2^0 := by
    rw [ht0]
    simp [hsv0, hc0v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u0, hu0⟩
  simp [hw] at hu0
  have hu0v : u0.val = 0 := by rw [hu0]; exact hz
  step as ⟨y0, hy0⟩
  have hy0v : y0.val = b24.val := by
    simp [hy0, UScalar.val_or, hu0v, ht0v]
  step as ⟨wn0, hwn0⟩
  try simp only [spec_ok]
  -- j = 1: byte 25
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with range_next_lt_spec as ⟨o1, iter1, ho1, hs1, he1⟩
  simp only [ho1]
  step as ⟨p1, hp1⟩
  step as ⟨q1, hq1⟩
  have hq1v : q1.val = 25 := by
    simp [hq1, hp1, hs0, he0]
    all_goals scalar_tac
  step as ⟨x1, hx1⟩
  simp [hb, hq1v] at hx1
  step with UScalar.cast.step_spec as ⟨c1, hc1⟩
  have hc1v : c1.val = b25.val := by
    rw [hc1, UScalar.cast_val_eq, hx1]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s1, hsh1⟩
  have hsv1 : s1.val = 8 := by
    simp [hsh1, hs0, he0]
    all_goals scalar_tac
  step as ⟨t1, ht1⟩
  have ht1v : t1.val = b25.val * 2^8 := by
    rw [ht1]
    simp [hsv1, hc1v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u1, hu1⟩
  simp [hwn0, hw] at hu1
  have hu1v : u1.val = b24.val := by rw [hu1]; exact hy0v
  step as ⟨y1, hy1⟩
  have hy1v : y1.val = b24.val + b25.val * 2^8 := by
    have hult : u1.val < 2^8 := by rw [hu1v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u1.val) (i := 8) hult b25.val
    have hadd : u1.val ||| b25.val * 2^8 = u1.val + b25.val * 2^8 := by
      calc u1.val ||| b25.val * 2^8
          = u1.val ||| 2^8 * b25.val := by rw [Nat.mul_comm]
        _ = 2^8 * b25.val ||| u1.val := Nat.lor_comm _ _
        _ = 2^8 * b25.val + u1.val := hor.symm
        _ = u1.val + b25.val * 2^8 := by ring
    simp only [hy1, UScalar.val_or, ht1v]
    rw [hadd, hu1v]
    all_goals ring
  step as ⟨wn1, hwn1⟩
  try simp only [spec_ok]
  -- j = 2: byte 26
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with range_next_lt_spec as ⟨o2, iter2, ho2, hs2, he2⟩
  simp only [ho2]
  step as ⟨p2, hp2⟩
  step as ⟨q2, hq2⟩
  have hq2v : q2.val = 26 := by
    simp [hq2, hp2, hs0, he0, hs1, he1]
    all_goals scalar_tac
  step as ⟨x2, hx2⟩
  simp [hb, hq2v] at hx2
  step with UScalar.cast.step_spec as ⟨c2, hc2⟩
  have hc2v : c2.val = b26.val := by
    rw [hc2, UScalar.cast_val_eq, hx2]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s2, hsh2⟩
  have hsv2 : s2.val = 16 := by
    simp [hsh2, hs0, he0, hs1, he1]
    all_goals scalar_tac
  step as ⟨t2, ht2⟩
  have ht2v : t2.val = b26.val * 2^16 := by
    rw [ht2]
    simp [hsv2, hc2v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u2, hu2⟩
  simp [hwn1, hw] at hu2
  have hu2v : u2.val = b24.val + b25.val * 2^8 := by rw [hu2]; exact hy1v
  step as ⟨y2, hy2⟩
  have hy2v : y2.val = b24.val + b25.val * 2^8 + b26.val * 2^16 := by
    have hult : u2.val < 2^16 := by rw [hu2v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u2.val) (i := 16) hult b26.val
    have hadd : u2.val ||| b26.val * 2^16 = u2.val + b26.val * 2^16 := by
      calc u2.val ||| b26.val * 2^16
          = u2.val ||| 2^16 * b26.val := by rw [Nat.mul_comm]
        _ = 2^16 * b26.val ||| u2.val := Nat.lor_comm _ _
        _ = 2^16 * b26.val + u2.val := hor.symm
        _ = u2.val + b26.val * 2^16 := by ring
    simp only [hy2, UScalar.val_or, ht2v]
    rw [hadd, hu2v]
    all_goals ring
  step as ⟨wn2, hwn2⟩
  try simp only [spec_ok]
  -- j = 3: byte 27
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with range_next_lt_spec as ⟨o3, iter3, ho3, hs3, he3⟩
  simp only [ho3]
  step as ⟨p3, hp3⟩
  step as ⟨q3, hq3⟩
  have hq3v : q3.val = 27 := by
    simp [hq3, hp3, hs0, he0, hs1, he1, hs2, he2]
    all_goals scalar_tac
  step as ⟨x3, hx3⟩
  simp [hb, hq3v] at hx3
  step with UScalar.cast.step_spec as ⟨c3, hc3⟩
  have hc3v : c3.val = b27.val := by
    rw [hc3, UScalar.cast_val_eq, hx3]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s3, hsh3⟩
  have hsv3 : s3.val = 24 := by
    simp [hsh3, hs0, he0, hs1, he1, hs2, he2]
    all_goals scalar_tac
  step as ⟨t3, ht3⟩
  have ht3v : t3.val = b27.val * 2^24 := by
    rw [ht3]
    simp [hsv3, hc3v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u3, hu3⟩
  simp [hwn2, hw] at hu3
  have hu3v : u3.val = b24.val + b25.val * 2^8 + b26.val * 2^16 := by rw [hu3]; exact hy2v
  step as ⟨y3, hy3⟩
  have hy3v : y3.val = b24.val + b25.val * 2^8 + b26.val * 2^16 + b27.val * 2^24 := by
    have hult : u3.val < 2^24 := by rw [hu3v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u3.val) (i := 24) hult b27.val
    have hadd : u3.val ||| b27.val * 2^24 = u3.val + b27.val * 2^24 := by
      calc u3.val ||| b27.val * 2^24
          = u3.val ||| 2^24 * b27.val := by rw [Nat.mul_comm]
        _ = 2^24 * b27.val ||| u3.val := Nat.lor_comm _ _
        _ = 2^24 * b27.val + u3.val := hor.symm
        _ = u3.val + b27.val * 2^24 := by ring
    simp only [hy3, UScalar.val_or, ht3v]
    rw [hadd, hu3v]
    all_goals ring
  step as ⟨wn3, hwn3⟩
  try simp only [spec_ok]
  -- refold and hand over to the tail lemma at the j = 4 boundary
  show backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0 iter3 bytes wn3 3#usize
    ⦃ ws => ∃ v : U64, (↑ws : List U64) = [w0, w1, w2, v, w4, w5, w6, w7] ∧
        v.val = b24.val + b25.val * 2^8 + b26.val * 2^16 + b27.val * 2^24 + b28.val * 2^32 + b29.val * 2^40 + b30.val * 2^48 + b31.val * 2^56 ⦄
  have hwn3l : (↑wn3 : List U64) = [w0, w1, w2, y3, w4, w5, w6, w7] := by
    simp [hwn0, hwn1, hwn2, hwn3, hw, Array.set_val_eq]
  have hst3 : iter3.start.val = 4 := by
    simp [hs3, hs2, hs1, hs0]
    all_goals scalar_tac
  have hend3 : iter3.«end» = 8#usize := by
    simp [he3, he2, he1, he0]
  exact bytes_word_loop_tail_3 bytes wn3 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63
    w0 w1 w2 y3 w4 w5 w6 w7 iter3 hb hwn3l hst3 hend3 hy3v

/-- Inner byte loop for word 4, iterations 4..7 + exit: continues the
    accumulation from the mid-state (bytes 32..35 absorbed). -/
theorem bytes_word_loop_tail_4
    (bytes : Std.Array Std.U8 64#usize)
    (words : Std.Array Std.U64 8#usize)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63 : Std.U8)
    (w0 w1 w2 w3 w4 w5 w6 w7 : U64)
    (iter : core.ops.range.Range Std.Usize)
    (hb : (↑bytes : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63])
    (hw : (↑words : List U64) = [w0, w1, w2, w3, w4, w5, w6, w7])
    (hst : iter.start.val = 4) (hend : iter.«end» = 8#usize)
    (hacc : w4.val = b32.val + b33.val * 2^8 + b34.val * 2^16 + b35.val * 2^24) :
    backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0 iter bytes words 4#usize
      ⦃ ws => ∃ v : U64, (↑ws : List U64) = [w0, w1, w2, w3, v, w5, w6, w7] ∧
          v.val = b32.val + b33.val * 2^8 + b34.val * 2^16 + b35.val * 2^24 + b36.val * 2^32 + b37.val * 2^40 + b38.val * 2^48 + b39.val * 2^56 ⦄ := by
  have hsz64 : (U64.size : ℕ) = 2^64 := by scalar_tac
  have hbb32 : b32.val < 2^8 := by scalar_tac
  have hbb33 : b33.val < 2^8 := by scalar_tac
  have hbb34 : b34.val < 2^8 := by scalar_tac
  have hbb35 : b35.val < 2^8 := by scalar_tac
  have hbb36 : b36.val < 2^8 := by scalar_tac
  have hbb37 : b37.val < 2^8 := by scalar_tac
  have hbb38 : b38.val < 2^8 := by scalar_tac
  have hbb39 : b39.val < 2^8 := by scalar_tac
  unfold backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0
  -- j = 4: byte 36
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with (range_next_lt_spec iter (by simp [hend, hst]; all_goals scalar_tac)) as ⟨o4, iter4, ho4, hs4, he4⟩
  simp only [ho4]
  step as ⟨p4, hp4⟩
  step as ⟨q4, hq4⟩
  have hq4v : q4.val = 36 := by
    simp [hq4, hp4, hst]
    all_goals scalar_tac
  step as ⟨x4, hx4⟩
  simp [hb, hq4v] at hx4
  step with UScalar.cast.step_spec as ⟨c4, hc4⟩
  have hc4v : c4.val = b36.val := by
    rw [hc4, UScalar.cast_val_eq, hx4]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s4, hsh4⟩
  have hsv4 : s4.val = 32 := by
    simp [hsh4, hst]
    all_goals scalar_tac
  step as ⟨t4, ht4⟩
  have ht4v : t4.val = b36.val * 2^32 := by
    rw [ht4]
    simp [hsv4, hc4v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u4, hu4⟩
  simp [hw] at hu4
  have hu4v : u4.val = b32.val + b33.val * 2^8 + b34.val * 2^16 + b35.val * 2^24 := by rw [hu4]; exact hacc
  step as ⟨y4, hy4⟩
  have hy4v : y4.val = b32.val + b33.val * 2^8 + b34.val * 2^16 + b35.val * 2^24 + b36.val * 2^32 := by
    have hult : u4.val < 2^32 := by rw [hu4v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u4.val) (i := 32) hult b36.val
    have hadd : u4.val ||| b36.val * 2^32 = u4.val + b36.val * 2^32 := by
      calc u4.val ||| b36.val * 2^32
          = u4.val ||| 2^32 * b36.val := by rw [Nat.mul_comm]
        _ = 2^32 * b36.val ||| u4.val := Nat.lor_comm _ _
        _ = 2^32 * b36.val + u4.val := hor.symm
        _ = u4.val + b36.val * 2^32 := by ring
    simp only [hy4, UScalar.val_or, ht4v]
    rw [hadd, hu4v]
    all_goals ring
  step as ⟨wn4, hwn4⟩
  try simp only [spec_ok]
  -- j = 5: byte 37
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with (range_next_lt_spec iter4 (by simp [hs4, he4, hend, hst]; all_goals scalar_tac)) as ⟨o5, iter5, ho5, hs5, he5⟩
  simp only [ho5]
  step as ⟨p5, hp5⟩
  step as ⟨q5, hq5⟩
  have hq5v : q5.val = 37 := by
    simp [hq5, hp5, hst, hs4, he4]
    all_goals scalar_tac
  step as ⟨x5, hx5⟩
  simp [hb, hq5v] at hx5
  step with UScalar.cast.step_spec as ⟨c5, hc5⟩
  have hc5v : c5.val = b37.val := by
    rw [hc5, UScalar.cast_val_eq, hx5]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s5, hsh5⟩
  have hsv5 : s5.val = 40 := by
    simp [hsh5, hst, hs4, he4]
    all_goals scalar_tac
  step as ⟨t5, ht5⟩
  have ht5v : t5.val = b37.val * 2^40 := by
    rw [ht5]
    simp [hsv5, hc5v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u5, hu5⟩
  simp [hwn4, hw] at hu5
  have hu5v : u5.val = b32.val + b33.val * 2^8 + b34.val * 2^16 + b35.val * 2^24 + b36.val * 2^32 := by rw [hu5]; exact hy4v
  step as ⟨y5, hy5⟩
  have hy5v : y5.val = b32.val + b33.val * 2^8 + b34.val * 2^16 + b35.val * 2^24 + b36.val * 2^32 + b37.val * 2^40 := by
    have hult : u5.val < 2^40 := by rw [hu5v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u5.val) (i := 40) hult b37.val
    have hadd : u5.val ||| b37.val * 2^40 = u5.val + b37.val * 2^40 := by
      calc u5.val ||| b37.val * 2^40
          = u5.val ||| 2^40 * b37.val := by rw [Nat.mul_comm]
        _ = 2^40 * b37.val ||| u5.val := Nat.lor_comm _ _
        _ = 2^40 * b37.val + u5.val := hor.symm
        _ = u5.val + b37.val * 2^40 := by ring
    simp only [hy5, UScalar.val_or, ht5v]
    rw [hadd, hu5v]
    all_goals ring
  step as ⟨wn5, hwn5⟩
  try simp only [spec_ok]
  -- j = 6: byte 38
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with (range_next_lt_spec iter5 (by simp [hs4, he4, hs5, he5, hend, hst]; all_goals scalar_tac)) as ⟨o6, iter6, ho6, hs6, he6⟩
  simp only [ho6]
  step as ⟨p6, hp6⟩
  step as ⟨q6, hq6⟩
  have hq6v : q6.val = 38 := by
    simp [hq6, hp6, hst, hs4, he4, hs5, he5]
    all_goals scalar_tac
  step as ⟨x6, hx6⟩
  simp [hb, hq6v] at hx6
  step with UScalar.cast.step_spec as ⟨c6, hc6⟩
  have hc6v : c6.val = b38.val := by
    rw [hc6, UScalar.cast_val_eq, hx6]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s6, hsh6⟩
  have hsv6 : s6.val = 48 := by
    simp [hsh6, hst, hs4, he4, hs5, he5]
    all_goals scalar_tac
  step as ⟨t6, ht6⟩
  have ht6v : t6.val = b38.val * 2^48 := by
    rw [ht6]
    simp [hsv6, hc6v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u6, hu6⟩
  simp [hwn5, hw] at hu6
  have hu6v : u6.val = b32.val + b33.val * 2^8 + b34.val * 2^16 + b35.val * 2^24 + b36.val * 2^32 + b37.val * 2^40 := by rw [hu6]; exact hy5v
  step as ⟨y6, hy6⟩
  have hy6v : y6.val = b32.val + b33.val * 2^8 + b34.val * 2^16 + b35.val * 2^24 + b36.val * 2^32 + b37.val * 2^40 + b38.val * 2^48 := by
    have hult : u6.val < 2^48 := by rw [hu6v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u6.val) (i := 48) hult b38.val
    have hadd : u6.val ||| b38.val * 2^48 = u6.val + b38.val * 2^48 := by
      calc u6.val ||| b38.val * 2^48
          = u6.val ||| 2^48 * b38.val := by rw [Nat.mul_comm]
        _ = 2^48 * b38.val ||| u6.val := Nat.lor_comm _ _
        _ = 2^48 * b38.val + u6.val := hor.symm
        _ = u6.val + b38.val * 2^48 := by ring
    simp only [hy6, UScalar.val_or, ht6v]
    rw [hadd, hu6v]
    all_goals ring
  step as ⟨wn6, hwn6⟩
  try simp only [spec_ok]
  -- j = 7: byte 39
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with (range_next_lt_spec iter6 (by simp [hs4, he4, hs5, he5, hs6, he6, hend, hst]; all_goals scalar_tac)) as ⟨o7, iter7, ho7, hs7, he7⟩
  simp only [ho7]
  step as ⟨p7, hp7⟩
  step as ⟨q7, hq7⟩
  have hq7v : q7.val = 39 := by
    simp [hq7, hp7, hst, hs4, he4, hs5, he5, hs6, he6]
    all_goals scalar_tac
  step as ⟨x7, hx7⟩
  simp [hb, hq7v] at hx7
  step with UScalar.cast.step_spec as ⟨c7, hc7⟩
  have hc7v : c7.val = b39.val := by
    rw [hc7, UScalar.cast_val_eq, hx7]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s7, hsh7⟩
  have hsv7 : s7.val = 56 := by
    simp [hsh7, hst, hs4, he4, hs5, he5, hs6, he6]
    all_goals scalar_tac
  step as ⟨t7, ht7⟩
  have ht7v : t7.val = b39.val * 2^56 := by
    rw [ht7]
    simp [hsv7, hc7v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u7, hu7⟩
  simp [hwn6, hw] at hu7
  have hu7v : u7.val = b32.val + b33.val * 2^8 + b34.val * 2^16 + b35.val * 2^24 + b36.val * 2^32 + b37.val * 2^40 + b38.val * 2^48 := by rw [hu7]; exact hy6v
  step as ⟨y7, hy7⟩
  have hy7v : y7.val = b32.val + b33.val * 2^8 + b34.val * 2^16 + b35.val * 2^24 + b36.val * 2^32 + b37.val * 2^40 + b38.val * 2^48 + b39.val * 2^56 := by
    have hult : u7.val < 2^56 := by rw [hu7v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u7.val) (i := 56) hult b39.val
    have hadd : u7.val ||| b39.val * 2^56 = u7.val + b39.val * 2^56 := by
      calc u7.val ||| b39.val * 2^56
          = u7.val ||| 2^56 * b39.val := by rw [Nat.mul_comm]
        _ = 2^56 * b39.val ||| u7.val := Nat.lor_comm _ _
        _ = 2^56 * b39.val + u7.val := hor.symm
        _ = u7.val + b39.val * 2^56 := by ring
    simp only [hy7, UScalar.val_or, ht7v]
    rw [hadd, hu7v]
    all_goals ring
  step as ⟨wn7, hwn7⟩
  try simp only [spec_ok]
  -- exit (8 ≥ 8)
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with (range_next_ge_spec iter7 (by simp [he7, he6, he5, he4, hend, hs7, hs6, hs5, hs4]; all_goals scalar_tac)) as ⟨oX, iterX, hoX, hrX⟩
  simp only [hoX]
  try simp only [spec_ok]
  refine ⟨y7, ?_, hy7v⟩
  simp [hwn4, hwn5, hwn6, hwn7, hw, Array.set_val_eq]

/-- Inner byte loop, outer index 4: word 4 accumulates bytes
    32..39 little-endian; the other words are untouched.
    Iterations 0..3 here; 4..7 + exit in `bytes_word_loop_tail_4`
    (the 8-fold monolith exceeds the elaboration budget — METHOD 4). -/
theorem bytes_word_loop_spec_4
    (bytes : Std.Array Std.U8 64#usize)
    (words : Std.Array Std.U64 8#usize)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63 : Std.U8)
    (w0 w1 w2 w3 w4 w5 w6 w7 : U64)
    (hb : (↑bytes : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63])
    (hw : (↑words : List U64) = [w0, w1, w2, w3, w4, w5, w6, w7])
    (hz : w4.val = 0) :
    backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0 { start := 0#usize, «end» := 8#usize } bytes words 4#usize
      ⦃ ws => ∃ v : U64, (↑ws : List U64) = [w0, w1, w2, w3, v, w5, w6, w7] ∧
          v.val = b32.val + b33.val * 2^8 + b34.val * 2^16 + b35.val * 2^24 + b36.val * 2^32 + b37.val * 2^40 + b38.val * 2^48 + b39.val * 2^56 ⦄ := by
  have hsz64 : (U64.size : ℕ) = 2^64 := by scalar_tac
  have hbb32 : b32.val < 2^8 := by scalar_tac
  have hbb33 : b33.val < 2^8 := by scalar_tac
  have hbb34 : b34.val < 2^8 := by scalar_tac
  have hbb35 : b35.val < 2^8 := by scalar_tac
  unfold backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0
  -- j = 0: byte 32
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with range_next_lt_spec as ⟨o0, iter0, ho0, hs0, he0⟩
  simp only [ho0]
  step as ⟨p0, hp0⟩
  step as ⟨q0, hq0⟩
  have hq0v : q0.val = 32 := by
    simp [hq0, hp0]
    all_goals scalar_tac
  step as ⟨x0, hx0⟩
  simp [hb, hq0v] at hx0
  step with UScalar.cast.step_spec as ⟨c0, hc0⟩
  have hc0v : c0.val = b32.val := by
    rw [hc0, UScalar.cast_val_eq, hx0]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s0, hsh0⟩
  have hsv0 : s0.val = 0 := by
    simp [hsh0]
    all_goals scalar_tac
  step as ⟨t0, ht0⟩
  have ht0v : t0.val = b32.val * 2^0 := by
    rw [ht0]
    simp [hsv0, hc0v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u0, hu0⟩
  simp [hw] at hu0
  have hu0v : u0.val = 0 := by rw [hu0]; exact hz
  step as ⟨y0, hy0⟩
  have hy0v : y0.val = b32.val := by
    simp [hy0, UScalar.val_or, hu0v, ht0v]
  step as ⟨wn0, hwn0⟩
  try simp only [spec_ok]
  -- j = 1: byte 33
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with range_next_lt_spec as ⟨o1, iter1, ho1, hs1, he1⟩
  simp only [ho1]
  step as ⟨p1, hp1⟩
  step as ⟨q1, hq1⟩
  have hq1v : q1.val = 33 := by
    simp [hq1, hp1, hs0, he0]
    all_goals scalar_tac
  step as ⟨x1, hx1⟩
  simp [hb, hq1v] at hx1
  step with UScalar.cast.step_spec as ⟨c1, hc1⟩
  have hc1v : c1.val = b33.val := by
    rw [hc1, UScalar.cast_val_eq, hx1]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s1, hsh1⟩
  have hsv1 : s1.val = 8 := by
    simp [hsh1, hs0, he0]
    all_goals scalar_tac
  step as ⟨t1, ht1⟩
  have ht1v : t1.val = b33.val * 2^8 := by
    rw [ht1]
    simp [hsv1, hc1v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u1, hu1⟩
  simp [hwn0, hw] at hu1
  have hu1v : u1.val = b32.val := by rw [hu1]; exact hy0v
  step as ⟨y1, hy1⟩
  have hy1v : y1.val = b32.val + b33.val * 2^8 := by
    have hult : u1.val < 2^8 := by rw [hu1v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u1.val) (i := 8) hult b33.val
    have hadd : u1.val ||| b33.val * 2^8 = u1.val + b33.val * 2^8 := by
      calc u1.val ||| b33.val * 2^8
          = u1.val ||| 2^8 * b33.val := by rw [Nat.mul_comm]
        _ = 2^8 * b33.val ||| u1.val := Nat.lor_comm _ _
        _ = 2^8 * b33.val + u1.val := hor.symm
        _ = u1.val + b33.val * 2^8 := by ring
    simp only [hy1, UScalar.val_or, ht1v]
    rw [hadd, hu1v]
    all_goals ring
  step as ⟨wn1, hwn1⟩
  try simp only [spec_ok]
  -- j = 2: byte 34
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with range_next_lt_spec as ⟨o2, iter2, ho2, hs2, he2⟩
  simp only [ho2]
  step as ⟨p2, hp2⟩
  step as ⟨q2, hq2⟩
  have hq2v : q2.val = 34 := by
    simp [hq2, hp2, hs0, he0, hs1, he1]
    all_goals scalar_tac
  step as ⟨x2, hx2⟩
  simp [hb, hq2v] at hx2
  step with UScalar.cast.step_spec as ⟨c2, hc2⟩
  have hc2v : c2.val = b34.val := by
    rw [hc2, UScalar.cast_val_eq, hx2]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s2, hsh2⟩
  have hsv2 : s2.val = 16 := by
    simp [hsh2, hs0, he0, hs1, he1]
    all_goals scalar_tac
  step as ⟨t2, ht2⟩
  have ht2v : t2.val = b34.val * 2^16 := by
    rw [ht2]
    simp [hsv2, hc2v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u2, hu2⟩
  simp [hwn1, hw] at hu2
  have hu2v : u2.val = b32.val + b33.val * 2^8 := by rw [hu2]; exact hy1v
  step as ⟨y2, hy2⟩
  have hy2v : y2.val = b32.val + b33.val * 2^8 + b34.val * 2^16 := by
    have hult : u2.val < 2^16 := by rw [hu2v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u2.val) (i := 16) hult b34.val
    have hadd : u2.val ||| b34.val * 2^16 = u2.val + b34.val * 2^16 := by
      calc u2.val ||| b34.val * 2^16
          = u2.val ||| 2^16 * b34.val := by rw [Nat.mul_comm]
        _ = 2^16 * b34.val ||| u2.val := Nat.lor_comm _ _
        _ = 2^16 * b34.val + u2.val := hor.symm
        _ = u2.val + b34.val * 2^16 := by ring
    simp only [hy2, UScalar.val_or, ht2v]
    rw [hadd, hu2v]
    all_goals ring
  step as ⟨wn2, hwn2⟩
  try simp only [spec_ok]
  -- j = 3: byte 35
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with range_next_lt_spec as ⟨o3, iter3, ho3, hs3, he3⟩
  simp only [ho3]
  step as ⟨p3, hp3⟩
  step as ⟨q3, hq3⟩
  have hq3v : q3.val = 35 := by
    simp [hq3, hp3, hs0, he0, hs1, he1, hs2, he2]
    all_goals scalar_tac
  step as ⟨x3, hx3⟩
  simp [hb, hq3v] at hx3
  step with UScalar.cast.step_spec as ⟨c3, hc3⟩
  have hc3v : c3.val = b35.val := by
    rw [hc3, UScalar.cast_val_eq, hx3]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s3, hsh3⟩
  have hsv3 : s3.val = 24 := by
    simp [hsh3, hs0, he0, hs1, he1, hs2, he2]
    all_goals scalar_tac
  step as ⟨t3, ht3⟩
  have ht3v : t3.val = b35.val * 2^24 := by
    rw [ht3]
    simp [hsv3, hc3v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u3, hu3⟩
  simp [hwn2, hw] at hu3
  have hu3v : u3.val = b32.val + b33.val * 2^8 + b34.val * 2^16 := by rw [hu3]; exact hy2v
  step as ⟨y3, hy3⟩
  have hy3v : y3.val = b32.val + b33.val * 2^8 + b34.val * 2^16 + b35.val * 2^24 := by
    have hult : u3.val < 2^24 := by rw [hu3v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u3.val) (i := 24) hult b35.val
    have hadd : u3.val ||| b35.val * 2^24 = u3.val + b35.val * 2^24 := by
      calc u3.val ||| b35.val * 2^24
          = u3.val ||| 2^24 * b35.val := by rw [Nat.mul_comm]
        _ = 2^24 * b35.val ||| u3.val := Nat.lor_comm _ _
        _ = 2^24 * b35.val + u3.val := hor.symm
        _ = u3.val + b35.val * 2^24 := by ring
    simp only [hy3, UScalar.val_or, ht3v]
    rw [hadd, hu3v]
    all_goals ring
  step as ⟨wn3, hwn3⟩
  try simp only [spec_ok]
  -- refold and hand over to the tail lemma at the j = 4 boundary
  show backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0 iter3 bytes wn3 4#usize
    ⦃ ws => ∃ v : U64, (↑ws : List U64) = [w0, w1, w2, w3, v, w5, w6, w7] ∧
        v.val = b32.val + b33.val * 2^8 + b34.val * 2^16 + b35.val * 2^24 + b36.val * 2^32 + b37.val * 2^40 + b38.val * 2^48 + b39.val * 2^56 ⦄
  have hwn3l : (↑wn3 : List U64) = [w0, w1, w2, w3, y3, w5, w6, w7] := by
    simp [hwn0, hwn1, hwn2, hwn3, hw, Array.set_val_eq]
  have hst3 : iter3.start.val = 4 := by
    simp [hs3, hs2, hs1, hs0]
    all_goals scalar_tac
  have hend3 : iter3.«end» = 8#usize := by
    simp [he3, he2, he1, he0]
  exact bytes_word_loop_tail_4 bytes wn3 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63
    w0 w1 w2 w3 y3 w5 w6 w7 iter3 hb hwn3l hst3 hend3 hy3v

/-- Inner byte loop for word 5, iterations 4..7 + exit: continues the
    accumulation from the mid-state (bytes 40..43 absorbed). -/
theorem bytes_word_loop_tail_5
    (bytes : Std.Array Std.U8 64#usize)
    (words : Std.Array Std.U64 8#usize)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63 : Std.U8)
    (w0 w1 w2 w3 w4 w5 w6 w7 : U64)
    (iter : core.ops.range.Range Std.Usize)
    (hb : (↑bytes : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63])
    (hw : (↑words : List U64) = [w0, w1, w2, w3, w4, w5, w6, w7])
    (hst : iter.start.val = 4) (hend : iter.«end» = 8#usize)
    (hacc : w5.val = b40.val + b41.val * 2^8 + b42.val * 2^16 + b43.val * 2^24) :
    backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0 iter bytes words 5#usize
      ⦃ ws => ∃ v : U64, (↑ws : List U64) = [w0, w1, w2, w3, w4, v, w6, w7] ∧
          v.val = b40.val + b41.val * 2^8 + b42.val * 2^16 + b43.val * 2^24 + b44.val * 2^32 + b45.val * 2^40 + b46.val * 2^48 + b47.val * 2^56 ⦄ := by
  have hsz64 : (U64.size : ℕ) = 2^64 := by scalar_tac
  have hbb40 : b40.val < 2^8 := by scalar_tac
  have hbb41 : b41.val < 2^8 := by scalar_tac
  have hbb42 : b42.val < 2^8 := by scalar_tac
  have hbb43 : b43.val < 2^8 := by scalar_tac
  have hbb44 : b44.val < 2^8 := by scalar_tac
  have hbb45 : b45.val < 2^8 := by scalar_tac
  have hbb46 : b46.val < 2^8 := by scalar_tac
  have hbb47 : b47.val < 2^8 := by scalar_tac
  unfold backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0
  -- j = 4: byte 44
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with (range_next_lt_spec iter (by simp [hend, hst]; all_goals scalar_tac)) as ⟨o4, iter4, ho4, hs4, he4⟩
  simp only [ho4]
  step as ⟨p4, hp4⟩
  step as ⟨q4, hq4⟩
  have hq4v : q4.val = 44 := by
    simp [hq4, hp4, hst]
    all_goals scalar_tac
  step as ⟨x4, hx4⟩
  simp [hb, hq4v] at hx4
  step with UScalar.cast.step_spec as ⟨c4, hc4⟩
  have hc4v : c4.val = b44.val := by
    rw [hc4, UScalar.cast_val_eq, hx4]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s4, hsh4⟩
  have hsv4 : s4.val = 32 := by
    simp [hsh4, hst]
    all_goals scalar_tac
  step as ⟨t4, ht4⟩
  have ht4v : t4.val = b44.val * 2^32 := by
    rw [ht4]
    simp [hsv4, hc4v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u4, hu4⟩
  simp [hw] at hu4
  have hu4v : u4.val = b40.val + b41.val * 2^8 + b42.val * 2^16 + b43.val * 2^24 := by rw [hu4]; exact hacc
  step as ⟨y4, hy4⟩
  have hy4v : y4.val = b40.val + b41.val * 2^8 + b42.val * 2^16 + b43.val * 2^24 + b44.val * 2^32 := by
    have hult : u4.val < 2^32 := by rw [hu4v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u4.val) (i := 32) hult b44.val
    have hadd : u4.val ||| b44.val * 2^32 = u4.val + b44.val * 2^32 := by
      calc u4.val ||| b44.val * 2^32
          = u4.val ||| 2^32 * b44.val := by rw [Nat.mul_comm]
        _ = 2^32 * b44.val ||| u4.val := Nat.lor_comm _ _
        _ = 2^32 * b44.val + u4.val := hor.symm
        _ = u4.val + b44.val * 2^32 := by ring
    simp only [hy4, UScalar.val_or, ht4v]
    rw [hadd, hu4v]
    all_goals ring
  step as ⟨wn4, hwn4⟩
  try simp only [spec_ok]
  -- j = 5: byte 45
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with (range_next_lt_spec iter4 (by simp [hs4, he4, hend, hst]; all_goals scalar_tac)) as ⟨o5, iter5, ho5, hs5, he5⟩
  simp only [ho5]
  step as ⟨p5, hp5⟩
  step as ⟨q5, hq5⟩
  have hq5v : q5.val = 45 := by
    simp [hq5, hp5, hst, hs4, he4]
    all_goals scalar_tac
  step as ⟨x5, hx5⟩
  simp [hb, hq5v] at hx5
  step with UScalar.cast.step_spec as ⟨c5, hc5⟩
  have hc5v : c5.val = b45.val := by
    rw [hc5, UScalar.cast_val_eq, hx5]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s5, hsh5⟩
  have hsv5 : s5.val = 40 := by
    simp [hsh5, hst, hs4, he4]
    all_goals scalar_tac
  step as ⟨t5, ht5⟩
  have ht5v : t5.val = b45.val * 2^40 := by
    rw [ht5]
    simp [hsv5, hc5v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u5, hu5⟩
  simp [hwn4, hw] at hu5
  have hu5v : u5.val = b40.val + b41.val * 2^8 + b42.val * 2^16 + b43.val * 2^24 + b44.val * 2^32 := by rw [hu5]; exact hy4v
  step as ⟨y5, hy5⟩
  have hy5v : y5.val = b40.val + b41.val * 2^8 + b42.val * 2^16 + b43.val * 2^24 + b44.val * 2^32 + b45.val * 2^40 := by
    have hult : u5.val < 2^40 := by rw [hu5v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u5.val) (i := 40) hult b45.val
    have hadd : u5.val ||| b45.val * 2^40 = u5.val + b45.val * 2^40 := by
      calc u5.val ||| b45.val * 2^40
          = u5.val ||| 2^40 * b45.val := by rw [Nat.mul_comm]
        _ = 2^40 * b45.val ||| u5.val := Nat.lor_comm _ _
        _ = 2^40 * b45.val + u5.val := hor.symm
        _ = u5.val + b45.val * 2^40 := by ring
    simp only [hy5, UScalar.val_or, ht5v]
    rw [hadd, hu5v]
    all_goals ring
  step as ⟨wn5, hwn5⟩
  try simp only [spec_ok]
  -- j = 6: byte 46
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with (range_next_lt_spec iter5 (by simp [hs4, he4, hs5, he5, hend, hst]; all_goals scalar_tac)) as ⟨o6, iter6, ho6, hs6, he6⟩
  simp only [ho6]
  step as ⟨p6, hp6⟩
  step as ⟨q6, hq6⟩
  have hq6v : q6.val = 46 := by
    simp [hq6, hp6, hst, hs4, he4, hs5, he5]
    all_goals scalar_tac
  step as ⟨x6, hx6⟩
  simp [hb, hq6v] at hx6
  step with UScalar.cast.step_spec as ⟨c6, hc6⟩
  have hc6v : c6.val = b46.val := by
    rw [hc6, UScalar.cast_val_eq, hx6]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s6, hsh6⟩
  have hsv6 : s6.val = 48 := by
    simp [hsh6, hst, hs4, he4, hs5, he5]
    all_goals scalar_tac
  step as ⟨t6, ht6⟩
  have ht6v : t6.val = b46.val * 2^48 := by
    rw [ht6]
    simp [hsv6, hc6v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u6, hu6⟩
  simp [hwn5, hw] at hu6
  have hu6v : u6.val = b40.val + b41.val * 2^8 + b42.val * 2^16 + b43.val * 2^24 + b44.val * 2^32 + b45.val * 2^40 := by rw [hu6]; exact hy5v
  step as ⟨y6, hy6⟩
  have hy6v : y6.val = b40.val + b41.val * 2^8 + b42.val * 2^16 + b43.val * 2^24 + b44.val * 2^32 + b45.val * 2^40 + b46.val * 2^48 := by
    have hult : u6.val < 2^48 := by rw [hu6v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u6.val) (i := 48) hult b46.val
    have hadd : u6.val ||| b46.val * 2^48 = u6.val + b46.val * 2^48 := by
      calc u6.val ||| b46.val * 2^48
          = u6.val ||| 2^48 * b46.val := by rw [Nat.mul_comm]
        _ = 2^48 * b46.val ||| u6.val := Nat.lor_comm _ _
        _ = 2^48 * b46.val + u6.val := hor.symm
        _ = u6.val + b46.val * 2^48 := by ring
    simp only [hy6, UScalar.val_or, ht6v]
    rw [hadd, hu6v]
    all_goals ring
  step as ⟨wn6, hwn6⟩
  try simp only [spec_ok]
  -- j = 7: byte 47
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with (range_next_lt_spec iter6 (by simp [hs4, he4, hs5, he5, hs6, he6, hend, hst]; all_goals scalar_tac)) as ⟨o7, iter7, ho7, hs7, he7⟩
  simp only [ho7]
  step as ⟨p7, hp7⟩
  step as ⟨q7, hq7⟩
  have hq7v : q7.val = 47 := by
    simp [hq7, hp7, hst, hs4, he4, hs5, he5, hs6, he6]
    all_goals scalar_tac
  step as ⟨x7, hx7⟩
  simp [hb, hq7v] at hx7
  step with UScalar.cast.step_spec as ⟨c7, hc7⟩
  have hc7v : c7.val = b47.val := by
    rw [hc7, UScalar.cast_val_eq, hx7]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s7, hsh7⟩
  have hsv7 : s7.val = 56 := by
    simp [hsh7, hst, hs4, he4, hs5, he5, hs6, he6]
    all_goals scalar_tac
  step as ⟨t7, ht7⟩
  have ht7v : t7.val = b47.val * 2^56 := by
    rw [ht7]
    simp [hsv7, hc7v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u7, hu7⟩
  simp [hwn6, hw] at hu7
  have hu7v : u7.val = b40.val + b41.val * 2^8 + b42.val * 2^16 + b43.val * 2^24 + b44.val * 2^32 + b45.val * 2^40 + b46.val * 2^48 := by rw [hu7]; exact hy6v
  step as ⟨y7, hy7⟩
  have hy7v : y7.val = b40.val + b41.val * 2^8 + b42.val * 2^16 + b43.val * 2^24 + b44.val * 2^32 + b45.val * 2^40 + b46.val * 2^48 + b47.val * 2^56 := by
    have hult : u7.val < 2^56 := by rw [hu7v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u7.val) (i := 56) hult b47.val
    have hadd : u7.val ||| b47.val * 2^56 = u7.val + b47.val * 2^56 := by
      calc u7.val ||| b47.val * 2^56
          = u7.val ||| 2^56 * b47.val := by rw [Nat.mul_comm]
        _ = 2^56 * b47.val ||| u7.val := Nat.lor_comm _ _
        _ = 2^56 * b47.val + u7.val := hor.symm
        _ = u7.val + b47.val * 2^56 := by ring
    simp only [hy7, UScalar.val_or, ht7v]
    rw [hadd, hu7v]
    all_goals ring
  step as ⟨wn7, hwn7⟩
  try simp only [spec_ok]
  -- exit (8 ≥ 8)
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with (range_next_ge_spec iter7 (by simp [he7, he6, he5, he4, hend, hs7, hs6, hs5, hs4]; all_goals scalar_tac)) as ⟨oX, iterX, hoX, hrX⟩
  simp only [hoX]
  try simp only [spec_ok]
  refine ⟨y7, ?_, hy7v⟩
  simp [hwn4, hwn5, hwn6, hwn7, hw, Array.set_val_eq]

/-- Inner byte loop, outer index 5: word 5 accumulates bytes
    40..47 little-endian; the other words are untouched.
    Iterations 0..3 here; 4..7 + exit in `bytes_word_loop_tail_5`
    (the 8-fold monolith exceeds the elaboration budget — METHOD 4). -/
theorem bytes_word_loop_spec_5
    (bytes : Std.Array Std.U8 64#usize)
    (words : Std.Array Std.U64 8#usize)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63 : Std.U8)
    (w0 w1 w2 w3 w4 w5 w6 w7 : U64)
    (hb : (↑bytes : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63])
    (hw : (↑words : List U64) = [w0, w1, w2, w3, w4, w5, w6, w7])
    (hz : w5.val = 0) :
    backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0 { start := 0#usize, «end» := 8#usize } bytes words 5#usize
      ⦃ ws => ∃ v : U64, (↑ws : List U64) = [w0, w1, w2, w3, w4, v, w6, w7] ∧
          v.val = b40.val + b41.val * 2^8 + b42.val * 2^16 + b43.val * 2^24 + b44.val * 2^32 + b45.val * 2^40 + b46.val * 2^48 + b47.val * 2^56 ⦄ := by
  have hsz64 : (U64.size : ℕ) = 2^64 := by scalar_tac
  have hbb40 : b40.val < 2^8 := by scalar_tac
  have hbb41 : b41.val < 2^8 := by scalar_tac
  have hbb42 : b42.val < 2^8 := by scalar_tac
  have hbb43 : b43.val < 2^8 := by scalar_tac
  unfold backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0
  -- j = 0: byte 40
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with range_next_lt_spec as ⟨o0, iter0, ho0, hs0, he0⟩
  simp only [ho0]
  step as ⟨p0, hp0⟩
  step as ⟨q0, hq0⟩
  have hq0v : q0.val = 40 := by
    simp [hq0, hp0]
    all_goals scalar_tac
  step as ⟨x0, hx0⟩
  simp [hb, hq0v] at hx0
  step with UScalar.cast.step_spec as ⟨c0, hc0⟩
  have hc0v : c0.val = b40.val := by
    rw [hc0, UScalar.cast_val_eq, hx0]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s0, hsh0⟩
  have hsv0 : s0.val = 0 := by
    simp [hsh0]
    all_goals scalar_tac
  step as ⟨t0, ht0⟩
  have ht0v : t0.val = b40.val * 2^0 := by
    rw [ht0]
    simp [hsv0, hc0v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u0, hu0⟩
  simp [hw] at hu0
  have hu0v : u0.val = 0 := by rw [hu0]; exact hz
  step as ⟨y0, hy0⟩
  have hy0v : y0.val = b40.val := by
    simp [hy0, UScalar.val_or, hu0v, ht0v]
  step as ⟨wn0, hwn0⟩
  try simp only [spec_ok]
  -- j = 1: byte 41
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with range_next_lt_spec as ⟨o1, iter1, ho1, hs1, he1⟩
  simp only [ho1]
  step as ⟨p1, hp1⟩
  step as ⟨q1, hq1⟩
  have hq1v : q1.val = 41 := by
    simp [hq1, hp1, hs0, he0]
    all_goals scalar_tac
  step as ⟨x1, hx1⟩
  simp [hb, hq1v] at hx1
  step with UScalar.cast.step_spec as ⟨c1, hc1⟩
  have hc1v : c1.val = b41.val := by
    rw [hc1, UScalar.cast_val_eq, hx1]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s1, hsh1⟩
  have hsv1 : s1.val = 8 := by
    simp [hsh1, hs0, he0]
    all_goals scalar_tac
  step as ⟨t1, ht1⟩
  have ht1v : t1.val = b41.val * 2^8 := by
    rw [ht1]
    simp [hsv1, hc1v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u1, hu1⟩
  simp [hwn0, hw] at hu1
  have hu1v : u1.val = b40.val := by rw [hu1]; exact hy0v
  step as ⟨y1, hy1⟩
  have hy1v : y1.val = b40.val + b41.val * 2^8 := by
    have hult : u1.val < 2^8 := by rw [hu1v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u1.val) (i := 8) hult b41.val
    have hadd : u1.val ||| b41.val * 2^8 = u1.val + b41.val * 2^8 := by
      calc u1.val ||| b41.val * 2^8
          = u1.val ||| 2^8 * b41.val := by rw [Nat.mul_comm]
        _ = 2^8 * b41.val ||| u1.val := Nat.lor_comm _ _
        _ = 2^8 * b41.val + u1.val := hor.symm
        _ = u1.val + b41.val * 2^8 := by ring
    simp only [hy1, UScalar.val_or, ht1v]
    rw [hadd, hu1v]
    all_goals ring
  step as ⟨wn1, hwn1⟩
  try simp only [spec_ok]
  -- j = 2: byte 42
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with range_next_lt_spec as ⟨o2, iter2, ho2, hs2, he2⟩
  simp only [ho2]
  step as ⟨p2, hp2⟩
  step as ⟨q2, hq2⟩
  have hq2v : q2.val = 42 := by
    simp [hq2, hp2, hs0, he0, hs1, he1]
    all_goals scalar_tac
  step as ⟨x2, hx2⟩
  simp [hb, hq2v] at hx2
  step with UScalar.cast.step_spec as ⟨c2, hc2⟩
  have hc2v : c2.val = b42.val := by
    rw [hc2, UScalar.cast_val_eq, hx2]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s2, hsh2⟩
  have hsv2 : s2.val = 16 := by
    simp [hsh2, hs0, he0, hs1, he1]
    all_goals scalar_tac
  step as ⟨t2, ht2⟩
  have ht2v : t2.val = b42.val * 2^16 := by
    rw [ht2]
    simp [hsv2, hc2v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u2, hu2⟩
  simp [hwn1, hw] at hu2
  have hu2v : u2.val = b40.val + b41.val * 2^8 := by rw [hu2]; exact hy1v
  step as ⟨y2, hy2⟩
  have hy2v : y2.val = b40.val + b41.val * 2^8 + b42.val * 2^16 := by
    have hult : u2.val < 2^16 := by rw [hu2v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u2.val) (i := 16) hult b42.val
    have hadd : u2.val ||| b42.val * 2^16 = u2.val + b42.val * 2^16 := by
      calc u2.val ||| b42.val * 2^16
          = u2.val ||| 2^16 * b42.val := by rw [Nat.mul_comm]
        _ = 2^16 * b42.val ||| u2.val := Nat.lor_comm _ _
        _ = 2^16 * b42.val + u2.val := hor.symm
        _ = u2.val + b42.val * 2^16 := by ring
    simp only [hy2, UScalar.val_or, ht2v]
    rw [hadd, hu2v]
    all_goals ring
  step as ⟨wn2, hwn2⟩
  try simp only [spec_ok]
  -- j = 3: byte 43
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with range_next_lt_spec as ⟨o3, iter3, ho3, hs3, he3⟩
  simp only [ho3]
  step as ⟨p3, hp3⟩
  step as ⟨q3, hq3⟩
  have hq3v : q3.val = 43 := by
    simp [hq3, hp3, hs0, he0, hs1, he1, hs2, he2]
    all_goals scalar_tac
  step as ⟨x3, hx3⟩
  simp [hb, hq3v] at hx3
  step with UScalar.cast.step_spec as ⟨c3, hc3⟩
  have hc3v : c3.val = b43.val := by
    rw [hc3, UScalar.cast_val_eq, hx3]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s3, hsh3⟩
  have hsv3 : s3.val = 24 := by
    simp [hsh3, hs0, he0, hs1, he1, hs2, he2]
    all_goals scalar_tac
  step as ⟨t3, ht3⟩
  have ht3v : t3.val = b43.val * 2^24 := by
    rw [ht3]
    simp [hsv3, hc3v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u3, hu3⟩
  simp [hwn2, hw] at hu3
  have hu3v : u3.val = b40.val + b41.val * 2^8 + b42.val * 2^16 := by rw [hu3]; exact hy2v
  step as ⟨y3, hy3⟩
  have hy3v : y3.val = b40.val + b41.val * 2^8 + b42.val * 2^16 + b43.val * 2^24 := by
    have hult : u3.val < 2^24 := by rw [hu3v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u3.val) (i := 24) hult b43.val
    have hadd : u3.val ||| b43.val * 2^24 = u3.val + b43.val * 2^24 := by
      calc u3.val ||| b43.val * 2^24
          = u3.val ||| 2^24 * b43.val := by rw [Nat.mul_comm]
        _ = 2^24 * b43.val ||| u3.val := Nat.lor_comm _ _
        _ = 2^24 * b43.val + u3.val := hor.symm
        _ = u3.val + b43.val * 2^24 := by ring
    simp only [hy3, UScalar.val_or, ht3v]
    rw [hadd, hu3v]
    all_goals ring
  step as ⟨wn3, hwn3⟩
  try simp only [spec_ok]
  -- refold and hand over to the tail lemma at the j = 4 boundary
  show backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0 iter3 bytes wn3 5#usize
    ⦃ ws => ∃ v : U64, (↑ws : List U64) = [w0, w1, w2, w3, w4, v, w6, w7] ∧
        v.val = b40.val + b41.val * 2^8 + b42.val * 2^16 + b43.val * 2^24 + b44.val * 2^32 + b45.val * 2^40 + b46.val * 2^48 + b47.val * 2^56 ⦄
  have hwn3l : (↑wn3 : List U64) = [w0, w1, w2, w3, w4, y3, w6, w7] := by
    simp [hwn0, hwn1, hwn2, hwn3, hw, Array.set_val_eq]
  have hst3 : iter3.start.val = 4 := by
    simp [hs3, hs2, hs1, hs0]
    all_goals scalar_tac
  have hend3 : iter3.«end» = 8#usize := by
    simp [he3, he2, he1, he0]
  exact bytes_word_loop_tail_5 bytes wn3 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63
    w0 w1 w2 w3 w4 y3 w6 w7 iter3 hb hwn3l hst3 hend3 hy3v

/-- Inner byte loop for word 6, iterations 4..7 + exit: continues the
    accumulation from the mid-state (bytes 48..51 absorbed). -/
theorem bytes_word_loop_tail_6
    (bytes : Std.Array Std.U8 64#usize)
    (words : Std.Array Std.U64 8#usize)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63 : Std.U8)
    (w0 w1 w2 w3 w4 w5 w6 w7 : U64)
    (iter : core.ops.range.Range Std.Usize)
    (hb : (↑bytes : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63])
    (hw : (↑words : List U64) = [w0, w1, w2, w3, w4, w5, w6, w7])
    (hst : iter.start.val = 4) (hend : iter.«end» = 8#usize)
    (hacc : w6.val = b48.val + b49.val * 2^8 + b50.val * 2^16 + b51.val * 2^24) :
    backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0 iter bytes words 6#usize
      ⦃ ws => ∃ v : U64, (↑ws : List U64) = [w0, w1, w2, w3, w4, w5, v, w7] ∧
          v.val = b48.val + b49.val * 2^8 + b50.val * 2^16 + b51.val * 2^24 + b52.val * 2^32 + b53.val * 2^40 + b54.val * 2^48 + b55.val * 2^56 ⦄ := by
  have hsz64 : (U64.size : ℕ) = 2^64 := by scalar_tac
  have hbb48 : b48.val < 2^8 := by scalar_tac
  have hbb49 : b49.val < 2^8 := by scalar_tac
  have hbb50 : b50.val < 2^8 := by scalar_tac
  have hbb51 : b51.val < 2^8 := by scalar_tac
  have hbb52 : b52.val < 2^8 := by scalar_tac
  have hbb53 : b53.val < 2^8 := by scalar_tac
  have hbb54 : b54.val < 2^8 := by scalar_tac
  have hbb55 : b55.val < 2^8 := by scalar_tac
  unfold backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0
  -- j = 4: byte 52
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with (range_next_lt_spec iter (by simp [hend, hst]; all_goals scalar_tac)) as ⟨o4, iter4, ho4, hs4, he4⟩
  simp only [ho4]
  step as ⟨p4, hp4⟩
  step as ⟨q4, hq4⟩
  have hq4v : q4.val = 52 := by
    simp [hq4, hp4, hst]
    all_goals scalar_tac
  step as ⟨x4, hx4⟩
  simp [hb, hq4v] at hx4
  step with UScalar.cast.step_spec as ⟨c4, hc4⟩
  have hc4v : c4.val = b52.val := by
    rw [hc4, UScalar.cast_val_eq, hx4]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s4, hsh4⟩
  have hsv4 : s4.val = 32 := by
    simp [hsh4, hst]
    all_goals scalar_tac
  step as ⟨t4, ht4⟩
  have ht4v : t4.val = b52.val * 2^32 := by
    rw [ht4]
    simp [hsv4, hc4v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u4, hu4⟩
  simp [hw] at hu4
  have hu4v : u4.val = b48.val + b49.val * 2^8 + b50.val * 2^16 + b51.val * 2^24 := by rw [hu4]; exact hacc
  step as ⟨y4, hy4⟩
  have hy4v : y4.val = b48.val + b49.val * 2^8 + b50.val * 2^16 + b51.val * 2^24 + b52.val * 2^32 := by
    have hult : u4.val < 2^32 := by rw [hu4v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u4.val) (i := 32) hult b52.val
    have hadd : u4.val ||| b52.val * 2^32 = u4.val + b52.val * 2^32 := by
      calc u4.val ||| b52.val * 2^32
          = u4.val ||| 2^32 * b52.val := by rw [Nat.mul_comm]
        _ = 2^32 * b52.val ||| u4.val := Nat.lor_comm _ _
        _ = 2^32 * b52.val + u4.val := hor.symm
        _ = u4.val + b52.val * 2^32 := by ring
    simp only [hy4, UScalar.val_or, ht4v]
    rw [hadd, hu4v]
    all_goals ring
  step as ⟨wn4, hwn4⟩
  try simp only [spec_ok]
  -- j = 5: byte 53
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with (range_next_lt_spec iter4 (by simp [hs4, he4, hend, hst]; all_goals scalar_tac)) as ⟨o5, iter5, ho5, hs5, he5⟩
  simp only [ho5]
  step as ⟨p5, hp5⟩
  step as ⟨q5, hq5⟩
  have hq5v : q5.val = 53 := by
    simp [hq5, hp5, hst, hs4, he4]
    all_goals scalar_tac
  step as ⟨x5, hx5⟩
  simp [hb, hq5v] at hx5
  step with UScalar.cast.step_spec as ⟨c5, hc5⟩
  have hc5v : c5.val = b53.val := by
    rw [hc5, UScalar.cast_val_eq, hx5]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s5, hsh5⟩
  have hsv5 : s5.val = 40 := by
    simp [hsh5, hst, hs4, he4]
    all_goals scalar_tac
  step as ⟨t5, ht5⟩
  have ht5v : t5.val = b53.val * 2^40 := by
    rw [ht5]
    simp [hsv5, hc5v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u5, hu5⟩
  simp [hwn4, hw] at hu5
  have hu5v : u5.val = b48.val + b49.val * 2^8 + b50.val * 2^16 + b51.val * 2^24 + b52.val * 2^32 := by rw [hu5]; exact hy4v
  step as ⟨y5, hy5⟩
  have hy5v : y5.val = b48.val + b49.val * 2^8 + b50.val * 2^16 + b51.val * 2^24 + b52.val * 2^32 + b53.val * 2^40 := by
    have hult : u5.val < 2^40 := by rw [hu5v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u5.val) (i := 40) hult b53.val
    have hadd : u5.val ||| b53.val * 2^40 = u5.val + b53.val * 2^40 := by
      calc u5.val ||| b53.val * 2^40
          = u5.val ||| 2^40 * b53.val := by rw [Nat.mul_comm]
        _ = 2^40 * b53.val ||| u5.val := Nat.lor_comm _ _
        _ = 2^40 * b53.val + u5.val := hor.symm
        _ = u5.val + b53.val * 2^40 := by ring
    simp only [hy5, UScalar.val_or, ht5v]
    rw [hadd, hu5v]
    all_goals ring
  step as ⟨wn5, hwn5⟩
  try simp only [spec_ok]
  -- j = 6: byte 54
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with (range_next_lt_spec iter5 (by simp [hs4, he4, hs5, he5, hend, hst]; all_goals scalar_tac)) as ⟨o6, iter6, ho6, hs6, he6⟩
  simp only [ho6]
  step as ⟨p6, hp6⟩
  step as ⟨q6, hq6⟩
  have hq6v : q6.val = 54 := by
    simp [hq6, hp6, hst, hs4, he4, hs5, he5]
    all_goals scalar_tac
  step as ⟨x6, hx6⟩
  simp [hb, hq6v] at hx6
  step with UScalar.cast.step_spec as ⟨c6, hc6⟩
  have hc6v : c6.val = b54.val := by
    rw [hc6, UScalar.cast_val_eq, hx6]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s6, hsh6⟩
  have hsv6 : s6.val = 48 := by
    simp [hsh6, hst, hs4, he4, hs5, he5]
    all_goals scalar_tac
  step as ⟨t6, ht6⟩
  have ht6v : t6.val = b54.val * 2^48 := by
    rw [ht6]
    simp [hsv6, hc6v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u6, hu6⟩
  simp [hwn5, hw] at hu6
  have hu6v : u6.val = b48.val + b49.val * 2^8 + b50.val * 2^16 + b51.val * 2^24 + b52.val * 2^32 + b53.val * 2^40 := by rw [hu6]; exact hy5v
  step as ⟨y6, hy6⟩
  have hy6v : y6.val = b48.val + b49.val * 2^8 + b50.val * 2^16 + b51.val * 2^24 + b52.val * 2^32 + b53.val * 2^40 + b54.val * 2^48 := by
    have hult : u6.val < 2^48 := by rw [hu6v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u6.val) (i := 48) hult b54.val
    have hadd : u6.val ||| b54.val * 2^48 = u6.val + b54.val * 2^48 := by
      calc u6.val ||| b54.val * 2^48
          = u6.val ||| 2^48 * b54.val := by rw [Nat.mul_comm]
        _ = 2^48 * b54.val ||| u6.val := Nat.lor_comm _ _
        _ = 2^48 * b54.val + u6.val := hor.symm
        _ = u6.val + b54.val * 2^48 := by ring
    simp only [hy6, UScalar.val_or, ht6v]
    rw [hadd, hu6v]
    all_goals ring
  step as ⟨wn6, hwn6⟩
  try simp only [spec_ok]
  -- j = 7: byte 55
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with (range_next_lt_spec iter6 (by simp [hs4, he4, hs5, he5, hs6, he6, hend, hst]; all_goals scalar_tac)) as ⟨o7, iter7, ho7, hs7, he7⟩
  simp only [ho7]
  step as ⟨p7, hp7⟩
  step as ⟨q7, hq7⟩
  have hq7v : q7.val = 55 := by
    simp [hq7, hp7, hst, hs4, he4, hs5, he5, hs6, he6]
    all_goals scalar_tac
  step as ⟨x7, hx7⟩
  simp [hb, hq7v] at hx7
  step with UScalar.cast.step_spec as ⟨c7, hc7⟩
  have hc7v : c7.val = b55.val := by
    rw [hc7, UScalar.cast_val_eq, hx7]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s7, hsh7⟩
  have hsv7 : s7.val = 56 := by
    simp [hsh7, hst, hs4, he4, hs5, he5, hs6, he6]
    all_goals scalar_tac
  step as ⟨t7, ht7⟩
  have ht7v : t7.val = b55.val * 2^56 := by
    rw [ht7]
    simp [hsv7, hc7v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u7, hu7⟩
  simp [hwn6, hw] at hu7
  have hu7v : u7.val = b48.val + b49.val * 2^8 + b50.val * 2^16 + b51.val * 2^24 + b52.val * 2^32 + b53.val * 2^40 + b54.val * 2^48 := by rw [hu7]; exact hy6v
  step as ⟨y7, hy7⟩
  have hy7v : y7.val = b48.val + b49.val * 2^8 + b50.val * 2^16 + b51.val * 2^24 + b52.val * 2^32 + b53.val * 2^40 + b54.val * 2^48 + b55.val * 2^56 := by
    have hult : u7.val < 2^56 := by rw [hu7v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u7.val) (i := 56) hult b55.val
    have hadd : u7.val ||| b55.val * 2^56 = u7.val + b55.val * 2^56 := by
      calc u7.val ||| b55.val * 2^56
          = u7.val ||| 2^56 * b55.val := by rw [Nat.mul_comm]
        _ = 2^56 * b55.val ||| u7.val := Nat.lor_comm _ _
        _ = 2^56 * b55.val + u7.val := hor.symm
        _ = u7.val + b55.val * 2^56 := by ring
    simp only [hy7, UScalar.val_or, ht7v]
    rw [hadd, hu7v]
    all_goals ring
  step as ⟨wn7, hwn7⟩
  try simp only [spec_ok]
  -- exit (8 ≥ 8)
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with (range_next_ge_spec iter7 (by simp [he7, he6, he5, he4, hend, hs7, hs6, hs5, hs4]; all_goals scalar_tac)) as ⟨oX, iterX, hoX, hrX⟩
  simp only [hoX]
  try simp only [spec_ok]
  refine ⟨y7, ?_, hy7v⟩
  simp [hwn4, hwn5, hwn6, hwn7, hw, Array.set_val_eq]

/-- Inner byte loop, outer index 6: word 6 accumulates bytes
    48..55 little-endian; the other words are untouched.
    Iterations 0..3 here; 4..7 + exit in `bytes_word_loop_tail_6`
    (the 8-fold monolith exceeds the elaboration budget — METHOD 4). -/
theorem bytes_word_loop_spec_6
    (bytes : Std.Array Std.U8 64#usize)
    (words : Std.Array Std.U64 8#usize)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63 : Std.U8)
    (w0 w1 w2 w3 w4 w5 w6 w7 : U64)
    (hb : (↑bytes : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63])
    (hw : (↑words : List U64) = [w0, w1, w2, w3, w4, w5, w6, w7])
    (hz : w6.val = 0) :
    backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0 { start := 0#usize, «end» := 8#usize } bytes words 6#usize
      ⦃ ws => ∃ v : U64, (↑ws : List U64) = [w0, w1, w2, w3, w4, w5, v, w7] ∧
          v.val = b48.val + b49.val * 2^8 + b50.val * 2^16 + b51.val * 2^24 + b52.val * 2^32 + b53.val * 2^40 + b54.val * 2^48 + b55.val * 2^56 ⦄ := by
  have hsz64 : (U64.size : ℕ) = 2^64 := by scalar_tac
  have hbb48 : b48.val < 2^8 := by scalar_tac
  have hbb49 : b49.val < 2^8 := by scalar_tac
  have hbb50 : b50.val < 2^8 := by scalar_tac
  have hbb51 : b51.val < 2^8 := by scalar_tac
  unfold backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0
  -- j = 0: byte 48
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with range_next_lt_spec as ⟨o0, iter0, ho0, hs0, he0⟩
  simp only [ho0]
  step as ⟨p0, hp0⟩
  step as ⟨q0, hq0⟩
  have hq0v : q0.val = 48 := by
    simp [hq0, hp0]
    all_goals scalar_tac
  step as ⟨x0, hx0⟩
  simp [hb, hq0v] at hx0
  step with UScalar.cast.step_spec as ⟨c0, hc0⟩
  have hc0v : c0.val = b48.val := by
    rw [hc0, UScalar.cast_val_eq, hx0]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s0, hsh0⟩
  have hsv0 : s0.val = 0 := by
    simp [hsh0]
    all_goals scalar_tac
  step as ⟨t0, ht0⟩
  have ht0v : t0.val = b48.val * 2^0 := by
    rw [ht0]
    simp [hsv0, hc0v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u0, hu0⟩
  simp [hw] at hu0
  have hu0v : u0.val = 0 := by rw [hu0]; exact hz
  step as ⟨y0, hy0⟩
  have hy0v : y0.val = b48.val := by
    simp [hy0, UScalar.val_or, hu0v, ht0v]
  step as ⟨wn0, hwn0⟩
  try simp only [spec_ok]
  -- j = 1: byte 49
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with range_next_lt_spec as ⟨o1, iter1, ho1, hs1, he1⟩
  simp only [ho1]
  step as ⟨p1, hp1⟩
  step as ⟨q1, hq1⟩
  have hq1v : q1.val = 49 := by
    simp [hq1, hp1, hs0, he0]
    all_goals scalar_tac
  step as ⟨x1, hx1⟩
  simp [hb, hq1v] at hx1
  step with UScalar.cast.step_spec as ⟨c1, hc1⟩
  have hc1v : c1.val = b49.val := by
    rw [hc1, UScalar.cast_val_eq, hx1]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s1, hsh1⟩
  have hsv1 : s1.val = 8 := by
    simp [hsh1, hs0, he0]
    all_goals scalar_tac
  step as ⟨t1, ht1⟩
  have ht1v : t1.val = b49.val * 2^8 := by
    rw [ht1]
    simp [hsv1, hc1v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u1, hu1⟩
  simp [hwn0, hw] at hu1
  have hu1v : u1.val = b48.val := by rw [hu1]; exact hy0v
  step as ⟨y1, hy1⟩
  have hy1v : y1.val = b48.val + b49.val * 2^8 := by
    have hult : u1.val < 2^8 := by rw [hu1v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u1.val) (i := 8) hult b49.val
    have hadd : u1.val ||| b49.val * 2^8 = u1.val + b49.val * 2^8 := by
      calc u1.val ||| b49.val * 2^8
          = u1.val ||| 2^8 * b49.val := by rw [Nat.mul_comm]
        _ = 2^8 * b49.val ||| u1.val := Nat.lor_comm _ _
        _ = 2^8 * b49.val + u1.val := hor.symm
        _ = u1.val + b49.val * 2^8 := by ring
    simp only [hy1, UScalar.val_or, ht1v]
    rw [hadd, hu1v]
    all_goals ring
  step as ⟨wn1, hwn1⟩
  try simp only [spec_ok]
  -- j = 2: byte 50
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with range_next_lt_spec as ⟨o2, iter2, ho2, hs2, he2⟩
  simp only [ho2]
  step as ⟨p2, hp2⟩
  step as ⟨q2, hq2⟩
  have hq2v : q2.val = 50 := by
    simp [hq2, hp2, hs0, he0, hs1, he1]
    all_goals scalar_tac
  step as ⟨x2, hx2⟩
  simp [hb, hq2v] at hx2
  step with UScalar.cast.step_spec as ⟨c2, hc2⟩
  have hc2v : c2.val = b50.val := by
    rw [hc2, UScalar.cast_val_eq, hx2]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s2, hsh2⟩
  have hsv2 : s2.val = 16 := by
    simp [hsh2, hs0, he0, hs1, he1]
    all_goals scalar_tac
  step as ⟨t2, ht2⟩
  have ht2v : t2.val = b50.val * 2^16 := by
    rw [ht2]
    simp [hsv2, hc2v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u2, hu2⟩
  simp [hwn1, hw] at hu2
  have hu2v : u2.val = b48.val + b49.val * 2^8 := by rw [hu2]; exact hy1v
  step as ⟨y2, hy2⟩
  have hy2v : y2.val = b48.val + b49.val * 2^8 + b50.val * 2^16 := by
    have hult : u2.val < 2^16 := by rw [hu2v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u2.val) (i := 16) hult b50.val
    have hadd : u2.val ||| b50.val * 2^16 = u2.val + b50.val * 2^16 := by
      calc u2.val ||| b50.val * 2^16
          = u2.val ||| 2^16 * b50.val := by rw [Nat.mul_comm]
        _ = 2^16 * b50.val ||| u2.val := Nat.lor_comm _ _
        _ = 2^16 * b50.val + u2.val := hor.symm
        _ = u2.val + b50.val * 2^16 := by ring
    simp only [hy2, UScalar.val_or, ht2v]
    rw [hadd, hu2v]
    all_goals ring
  step as ⟨wn2, hwn2⟩
  try simp only [spec_ok]
  -- j = 3: byte 51
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with range_next_lt_spec as ⟨o3, iter3, ho3, hs3, he3⟩
  simp only [ho3]
  step as ⟨p3, hp3⟩
  step as ⟨q3, hq3⟩
  have hq3v : q3.val = 51 := by
    simp [hq3, hp3, hs0, he0, hs1, he1, hs2, he2]
    all_goals scalar_tac
  step as ⟨x3, hx3⟩
  simp [hb, hq3v] at hx3
  step with UScalar.cast.step_spec as ⟨c3, hc3⟩
  have hc3v : c3.val = b51.val := by
    rw [hc3, UScalar.cast_val_eq, hx3]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s3, hsh3⟩
  have hsv3 : s3.val = 24 := by
    simp [hsh3, hs0, he0, hs1, he1, hs2, he2]
    all_goals scalar_tac
  step as ⟨t3, ht3⟩
  have ht3v : t3.val = b51.val * 2^24 := by
    rw [ht3]
    simp [hsv3, hc3v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u3, hu3⟩
  simp [hwn2, hw] at hu3
  have hu3v : u3.val = b48.val + b49.val * 2^8 + b50.val * 2^16 := by rw [hu3]; exact hy2v
  step as ⟨y3, hy3⟩
  have hy3v : y3.val = b48.val + b49.val * 2^8 + b50.val * 2^16 + b51.val * 2^24 := by
    have hult : u3.val < 2^24 := by rw [hu3v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u3.val) (i := 24) hult b51.val
    have hadd : u3.val ||| b51.val * 2^24 = u3.val + b51.val * 2^24 := by
      calc u3.val ||| b51.val * 2^24
          = u3.val ||| 2^24 * b51.val := by rw [Nat.mul_comm]
        _ = 2^24 * b51.val ||| u3.val := Nat.lor_comm _ _
        _ = 2^24 * b51.val + u3.val := hor.symm
        _ = u3.val + b51.val * 2^24 := by ring
    simp only [hy3, UScalar.val_or, ht3v]
    rw [hadd, hu3v]
    all_goals ring
  step as ⟨wn3, hwn3⟩
  try simp only [spec_ok]
  -- refold and hand over to the tail lemma at the j = 4 boundary
  show backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0 iter3 bytes wn3 6#usize
    ⦃ ws => ∃ v : U64, (↑ws : List U64) = [w0, w1, w2, w3, w4, w5, v, w7] ∧
        v.val = b48.val + b49.val * 2^8 + b50.val * 2^16 + b51.val * 2^24 + b52.val * 2^32 + b53.val * 2^40 + b54.val * 2^48 + b55.val * 2^56 ⦄
  have hwn3l : (↑wn3 : List U64) = [w0, w1, w2, w3, w4, w5, y3, w7] := by
    simp [hwn0, hwn1, hwn2, hwn3, hw, Array.set_val_eq]
  have hst3 : iter3.start.val = 4 := by
    simp [hs3, hs2, hs1, hs0]
    all_goals scalar_tac
  have hend3 : iter3.«end» = 8#usize := by
    simp [he3, he2, he1, he0]
  exact bytes_word_loop_tail_6 bytes wn3 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63
    w0 w1 w2 w3 w4 w5 y3 w7 iter3 hb hwn3l hst3 hend3 hy3v

/-- Inner byte loop for word 7, iterations 4..7 + exit: continues the
    accumulation from the mid-state (bytes 56..59 absorbed). -/
theorem bytes_word_loop_tail_7
    (bytes : Std.Array Std.U8 64#usize)
    (words : Std.Array Std.U64 8#usize)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63 : Std.U8)
    (w0 w1 w2 w3 w4 w5 w6 w7 : U64)
    (iter : core.ops.range.Range Std.Usize)
    (hb : (↑bytes : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63])
    (hw : (↑words : List U64) = [w0, w1, w2, w3, w4, w5, w6, w7])
    (hst : iter.start.val = 4) (hend : iter.«end» = 8#usize)
    (hacc : w7.val = b56.val + b57.val * 2^8 + b58.val * 2^16 + b59.val * 2^24) :
    backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0 iter bytes words 7#usize
      ⦃ ws => ∃ v : U64, (↑ws : List U64) = [w0, w1, w2, w3, w4, w5, w6, v] ∧
          v.val = b56.val + b57.val * 2^8 + b58.val * 2^16 + b59.val * 2^24 + b60.val * 2^32 + b61.val * 2^40 + b62.val * 2^48 + b63.val * 2^56 ⦄ := by
  have hsz64 : (U64.size : ℕ) = 2^64 := by scalar_tac
  have hbb56 : b56.val < 2^8 := by scalar_tac
  have hbb57 : b57.val < 2^8 := by scalar_tac
  have hbb58 : b58.val < 2^8 := by scalar_tac
  have hbb59 : b59.val < 2^8 := by scalar_tac
  have hbb60 : b60.val < 2^8 := by scalar_tac
  have hbb61 : b61.val < 2^8 := by scalar_tac
  have hbb62 : b62.val < 2^8 := by scalar_tac
  have hbb63 : b63.val < 2^8 := by scalar_tac
  unfold backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0
  -- j = 4: byte 60
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with (range_next_lt_spec iter (by simp [hend, hst]; all_goals scalar_tac)) as ⟨o4, iter4, ho4, hs4, he4⟩
  simp only [ho4]
  step as ⟨p4, hp4⟩
  step as ⟨q4, hq4⟩
  have hq4v : q4.val = 60 := by
    simp [hq4, hp4, hst]
    all_goals scalar_tac
  step as ⟨x4, hx4⟩
  simp [hb, hq4v] at hx4
  step with UScalar.cast.step_spec as ⟨c4, hc4⟩
  have hc4v : c4.val = b60.val := by
    rw [hc4, UScalar.cast_val_eq, hx4]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s4, hsh4⟩
  have hsv4 : s4.val = 32 := by
    simp [hsh4, hst]
    all_goals scalar_tac
  step as ⟨t4, ht4⟩
  have ht4v : t4.val = b60.val * 2^32 := by
    rw [ht4]
    simp [hsv4, hc4v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u4, hu4⟩
  simp [hw] at hu4
  have hu4v : u4.val = b56.val + b57.val * 2^8 + b58.val * 2^16 + b59.val * 2^24 := by rw [hu4]; exact hacc
  step as ⟨y4, hy4⟩
  have hy4v : y4.val = b56.val + b57.val * 2^8 + b58.val * 2^16 + b59.val * 2^24 + b60.val * 2^32 := by
    have hult : u4.val < 2^32 := by rw [hu4v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u4.val) (i := 32) hult b60.val
    have hadd : u4.val ||| b60.val * 2^32 = u4.val + b60.val * 2^32 := by
      calc u4.val ||| b60.val * 2^32
          = u4.val ||| 2^32 * b60.val := by rw [Nat.mul_comm]
        _ = 2^32 * b60.val ||| u4.val := Nat.lor_comm _ _
        _ = 2^32 * b60.val + u4.val := hor.symm
        _ = u4.val + b60.val * 2^32 := by ring
    simp only [hy4, UScalar.val_or, ht4v]
    rw [hadd, hu4v]
    all_goals ring
  step as ⟨wn4, hwn4⟩
  try simp only [spec_ok]
  -- j = 5: byte 61
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with (range_next_lt_spec iter4 (by simp [hs4, he4, hend, hst]; all_goals scalar_tac)) as ⟨o5, iter5, ho5, hs5, he5⟩
  simp only [ho5]
  step as ⟨p5, hp5⟩
  step as ⟨q5, hq5⟩
  have hq5v : q5.val = 61 := by
    simp [hq5, hp5, hst, hs4, he4]
    all_goals scalar_tac
  step as ⟨x5, hx5⟩
  simp [hb, hq5v] at hx5
  step with UScalar.cast.step_spec as ⟨c5, hc5⟩
  have hc5v : c5.val = b61.val := by
    rw [hc5, UScalar.cast_val_eq, hx5]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s5, hsh5⟩
  have hsv5 : s5.val = 40 := by
    simp [hsh5, hst, hs4, he4]
    all_goals scalar_tac
  step as ⟨t5, ht5⟩
  have ht5v : t5.val = b61.val * 2^40 := by
    rw [ht5]
    simp [hsv5, hc5v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u5, hu5⟩
  simp [hwn4, hw] at hu5
  have hu5v : u5.val = b56.val + b57.val * 2^8 + b58.val * 2^16 + b59.val * 2^24 + b60.val * 2^32 := by rw [hu5]; exact hy4v
  step as ⟨y5, hy5⟩
  have hy5v : y5.val = b56.val + b57.val * 2^8 + b58.val * 2^16 + b59.val * 2^24 + b60.val * 2^32 + b61.val * 2^40 := by
    have hult : u5.val < 2^40 := by rw [hu5v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u5.val) (i := 40) hult b61.val
    have hadd : u5.val ||| b61.val * 2^40 = u5.val + b61.val * 2^40 := by
      calc u5.val ||| b61.val * 2^40
          = u5.val ||| 2^40 * b61.val := by rw [Nat.mul_comm]
        _ = 2^40 * b61.val ||| u5.val := Nat.lor_comm _ _
        _ = 2^40 * b61.val + u5.val := hor.symm
        _ = u5.val + b61.val * 2^40 := by ring
    simp only [hy5, UScalar.val_or, ht5v]
    rw [hadd, hu5v]
    all_goals ring
  step as ⟨wn5, hwn5⟩
  try simp only [spec_ok]
  -- j = 6: byte 62
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with (range_next_lt_spec iter5 (by simp [hs4, he4, hs5, he5, hend, hst]; all_goals scalar_tac)) as ⟨o6, iter6, ho6, hs6, he6⟩
  simp only [ho6]
  step as ⟨p6, hp6⟩
  step as ⟨q6, hq6⟩
  have hq6v : q6.val = 62 := by
    simp [hq6, hp6, hst, hs4, he4, hs5, he5]
    all_goals scalar_tac
  step as ⟨x6, hx6⟩
  simp [hb, hq6v] at hx6
  step with UScalar.cast.step_spec as ⟨c6, hc6⟩
  have hc6v : c6.val = b62.val := by
    rw [hc6, UScalar.cast_val_eq, hx6]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s6, hsh6⟩
  have hsv6 : s6.val = 48 := by
    simp [hsh6, hst, hs4, he4, hs5, he5]
    all_goals scalar_tac
  step as ⟨t6, ht6⟩
  have ht6v : t6.val = b62.val * 2^48 := by
    rw [ht6]
    simp [hsv6, hc6v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u6, hu6⟩
  simp [hwn5, hw] at hu6
  have hu6v : u6.val = b56.val + b57.val * 2^8 + b58.val * 2^16 + b59.val * 2^24 + b60.val * 2^32 + b61.val * 2^40 := by rw [hu6]; exact hy5v
  step as ⟨y6, hy6⟩
  have hy6v : y6.val = b56.val + b57.val * 2^8 + b58.val * 2^16 + b59.val * 2^24 + b60.val * 2^32 + b61.val * 2^40 + b62.val * 2^48 := by
    have hult : u6.val < 2^48 := by rw [hu6v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u6.val) (i := 48) hult b62.val
    have hadd : u6.val ||| b62.val * 2^48 = u6.val + b62.val * 2^48 := by
      calc u6.val ||| b62.val * 2^48
          = u6.val ||| 2^48 * b62.val := by rw [Nat.mul_comm]
        _ = 2^48 * b62.val ||| u6.val := Nat.lor_comm _ _
        _ = 2^48 * b62.val + u6.val := hor.symm
        _ = u6.val + b62.val * 2^48 := by ring
    simp only [hy6, UScalar.val_or, ht6v]
    rw [hadd, hu6v]
    all_goals ring
  step as ⟨wn6, hwn6⟩
  try simp only [spec_ok]
  -- j = 7: byte 63
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with (range_next_lt_spec iter6 (by simp [hs4, he4, hs5, he5, hs6, he6, hend, hst]; all_goals scalar_tac)) as ⟨o7, iter7, ho7, hs7, he7⟩
  simp only [ho7]
  step as ⟨p7, hp7⟩
  step as ⟨q7, hq7⟩
  have hq7v : q7.val = 63 := by
    simp [hq7, hp7, hst, hs4, he4, hs5, he5, hs6, he6]
    all_goals scalar_tac
  step as ⟨x7, hx7⟩
  simp [hb, hq7v] at hx7
  step with UScalar.cast.step_spec as ⟨c7, hc7⟩
  have hc7v : c7.val = b63.val := by
    rw [hc7, UScalar.cast_val_eq, hx7]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s7, hsh7⟩
  have hsv7 : s7.val = 56 := by
    simp [hsh7, hst, hs4, he4, hs5, he5, hs6, he6]
    all_goals scalar_tac
  step as ⟨t7, ht7⟩
  have ht7v : t7.val = b63.val * 2^56 := by
    rw [ht7]
    simp [hsv7, hc7v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u7, hu7⟩
  simp [hwn6, hw] at hu7
  have hu7v : u7.val = b56.val + b57.val * 2^8 + b58.val * 2^16 + b59.val * 2^24 + b60.val * 2^32 + b61.val * 2^40 + b62.val * 2^48 := by rw [hu7]; exact hy6v
  step as ⟨y7, hy7⟩
  have hy7v : y7.val = b56.val + b57.val * 2^8 + b58.val * 2^16 + b59.val * 2^24 + b60.val * 2^32 + b61.val * 2^40 + b62.val * 2^48 + b63.val * 2^56 := by
    have hult : u7.val < 2^56 := by rw [hu7v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u7.val) (i := 56) hult b63.val
    have hadd : u7.val ||| b63.val * 2^56 = u7.val + b63.val * 2^56 := by
      calc u7.val ||| b63.val * 2^56
          = u7.val ||| 2^56 * b63.val := by rw [Nat.mul_comm]
        _ = 2^56 * b63.val ||| u7.val := Nat.lor_comm _ _
        _ = 2^56 * b63.val + u7.val := hor.symm
        _ = u7.val + b63.val * 2^56 := by ring
    simp only [hy7, UScalar.val_or, ht7v]
    rw [hadd, hu7v]
    all_goals ring
  step as ⟨wn7, hwn7⟩
  try simp only [spec_ok]
  -- exit (8 ≥ 8)
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with (range_next_ge_spec iter7 (by simp [he7, he6, he5, he4, hend, hs7, hs6, hs5, hs4]; all_goals scalar_tac)) as ⟨oX, iterX, hoX, hrX⟩
  simp only [hoX]
  try simp only [spec_ok]
  refine ⟨y7, ?_, hy7v⟩
  simp [hwn4, hwn5, hwn6, hwn7, hw, Array.set_val_eq]

/-- Inner byte loop, outer index 7: word 7 accumulates bytes
    56..63 little-endian; the other words are untouched.
    Iterations 0..3 here; 4..7 + exit in `bytes_word_loop_tail_7`
    (the 8-fold monolith exceeds the elaboration budget — METHOD 4). -/
theorem bytes_word_loop_spec_7
    (bytes : Std.Array Std.U8 64#usize)
    (words : Std.Array Std.U64 8#usize)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63 : Std.U8)
    (w0 w1 w2 w3 w4 w5 w6 w7 : U64)
    (hb : (↑bytes : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63])
    (hw : (↑words : List U64) = [w0, w1, w2, w3, w4, w5, w6, w7])
    (hz : w7.val = 0) :
    backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0 { start := 0#usize, «end» := 8#usize } bytes words 7#usize
      ⦃ ws => ∃ v : U64, (↑ws : List U64) = [w0, w1, w2, w3, w4, w5, w6, v] ∧
          v.val = b56.val + b57.val * 2^8 + b58.val * 2^16 + b59.val * 2^24 + b60.val * 2^32 + b61.val * 2^40 + b62.val * 2^48 + b63.val * 2^56 ⦄ := by
  have hsz64 : (U64.size : ℕ) = 2^64 := by scalar_tac
  have hbb56 : b56.val < 2^8 := by scalar_tac
  have hbb57 : b57.val < 2^8 := by scalar_tac
  have hbb58 : b58.val < 2^8 := by scalar_tac
  have hbb59 : b59.val < 2^8 := by scalar_tac
  unfold backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0
  -- j = 0: byte 56
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with range_next_lt_spec as ⟨o0, iter0, ho0, hs0, he0⟩
  simp only [ho0]
  step as ⟨p0, hp0⟩
  step as ⟨q0, hq0⟩
  have hq0v : q0.val = 56 := by
    simp [hq0, hp0]
    all_goals scalar_tac
  step as ⟨x0, hx0⟩
  simp [hb, hq0v] at hx0
  step with UScalar.cast.step_spec as ⟨c0, hc0⟩
  have hc0v : c0.val = b56.val := by
    rw [hc0, UScalar.cast_val_eq, hx0]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s0, hsh0⟩
  have hsv0 : s0.val = 0 := by
    simp [hsh0]
    all_goals scalar_tac
  step as ⟨t0, ht0⟩
  have ht0v : t0.val = b56.val * 2^0 := by
    rw [ht0]
    simp [hsv0, hc0v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u0, hu0⟩
  simp [hw] at hu0
  have hu0v : u0.val = 0 := by rw [hu0]; exact hz
  step as ⟨y0, hy0⟩
  have hy0v : y0.val = b56.val := by
    simp [hy0, UScalar.val_or, hu0v, ht0v]
  step as ⟨wn0, hwn0⟩
  try simp only [spec_ok]
  -- j = 1: byte 57
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with range_next_lt_spec as ⟨o1, iter1, ho1, hs1, he1⟩
  simp only [ho1]
  step as ⟨p1, hp1⟩
  step as ⟨q1, hq1⟩
  have hq1v : q1.val = 57 := by
    simp [hq1, hp1, hs0, he0]
    all_goals scalar_tac
  step as ⟨x1, hx1⟩
  simp [hb, hq1v] at hx1
  step with UScalar.cast.step_spec as ⟨c1, hc1⟩
  have hc1v : c1.val = b57.val := by
    rw [hc1, UScalar.cast_val_eq, hx1]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s1, hsh1⟩
  have hsv1 : s1.val = 8 := by
    simp [hsh1, hs0, he0]
    all_goals scalar_tac
  step as ⟨t1, ht1⟩
  have ht1v : t1.val = b57.val * 2^8 := by
    rw [ht1]
    simp [hsv1, hc1v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u1, hu1⟩
  simp [hwn0, hw] at hu1
  have hu1v : u1.val = b56.val := by rw [hu1]; exact hy0v
  step as ⟨y1, hy1⟩
  have hy1v : y1.val = b56.val + b57.val * 2^8 := by
    have hult : u1.val < 2^8 := by rw [hu1v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u1.val) (i := 8) hult b57.val
    have hadd : u1.val ||| b57.val * 2^8 = u1.val + b57.val * 2^8 := by
      calc u1.val ||| b57.val * 2^8
          = u1.val ||| 2^8 * b57.val := by rw [Nat.mul_comm]
        _ = 2^8 * b57.val ||| u1.val := Nat.lor_comm _ _
        _ = 2^8 * b57.val + u1.val := hor.symm
        _ = u1.val + b57.val * 2^8 := by ring
    simp only [hy1, UScalar.val_or, ht1v]
    rw [hadd, hu1v]
    all_goals ring
  step as ⟨wn1, hwn1⟩
  try simp only [spec_ok]
  -- j = 2: byte 58
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with range_next_lt_spec as ⟨o2, iter2, ho2, hs2, he2⟩
  simp only [ho2]
  step as ⟨p2, hp2⟩
  step as ⟨q2, hq2⟩
  have hq2v : q2.val = 58 := by
    simp [hq2, hp2, hs0, he0, hs1, he1]
    all_goals scalar_tac
  step as ⟨x2, hx2⟩
  simp [hb, hq2v] at hx2
  step with UScalar.cast.step_spec as ⟨c2, hc2⟩
  have hc2v : c2.val = b58.val := by
    rw [hc2, UScalar.cast_val_eq, hx2]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s2, hsh2⟩
  have hsv2 : s2.val = 16 := by
    simp [hsh2, hs0, he0, hs1, he1]
    all_goals scalar_tac
  step as ⟨t2, ht2⟩
  have ht2v : t2.val = b58.val * 2^16 := by
    rw [ht2]
    simp [hsv2, hc2v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u2, hu2⟩
  simp [hwn1, hw] at hu2
  have hu2v : u2.val = b56.val + b57.val * 2^8 := by rw [hu2]; exact hy1v
  step as ⟨y2, hy2⟩
  have hy2v : y2.val = b56.val + b57.val * 2^8 + b58.val * 2^16 := by
    have hult : u2.val < 2^16 := by rw [hu2v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u2.val) (i := 16) hult b58.val
    have hadd : u2.val ||| b58.val * 2^16 = u2.val + b58.val * 2^16 := by
      calc u2.val ||| b58.val * 2^16
          = u2.val ||| 2^16 * b58.val := by rw [Nat.mul_comm]
        _ = 2^16 * b58.val ||| u2.val := Nat.lor_comm _ _
        _ = 2^16 * b58.val + u2.val := hor.symm
        _ = u2.val + b58.val * 2^16 := by ring
    simp only [hy2, UScalar.val_or, ht2v]
    rw [hadd, hu2v]
    all_goals ring
  step as ⟨wn2, hwn2⟩
  try simp only [spec_ok]
  -- j = 3: byte 59
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0.body]
  step with range_next_lt_spec as ⟨o3, iter3, ho3, hs3, he3⟩
  simp only [ho3]
  step as ⟨p3, hp3⟩
  step as ⟨q3, hq3⟩
  have hq3v : q3.val = 59 := by
    simp [hq3, hp3, hs0, he0, hs1, he1, hs2, he2]
    all_goals scalar_tac
  step as ⟨x3, hx3⟩
  simp [hb, hq3v] at hx3
  step with UScalar.cast.step_spec as ⟨c3, hc3⟩
  have hc3v : c3.val = b59.val := by
    rw [hc3, UScalar.cast_val_eq, hx3]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  step as ⟨s3, hsh3⟩
  have hsv3 : s3.val = 24 := by
    simp [hsh3, hs0, he0, hs1, he1, hs2, he2]
    all_goals scalar_tac
  step as ⟨t3, ht3⟩
  have ht3v : t3.val = b59.val * 2^24 := by
    rw [ht3]
    simp [hsv3, hc3v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨u3, hu3⟩
  simp [hwn2, hw] at hu3
  have hu3v : u3.val = b56.val + b57.val * 2^8 + b58.val * 2^16 := by rw [hu3]; exact hy2v
  step as ⟨y3, hy3⟩
  have hy3v : y3.val = b56.val + b57.val * 2^8 + b58.val * 2^16 + b59.val * 2^24 := by
    have hult : u3.val < 2^24 := by rw [hu3v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := u3.val) (i := 24) hult b59.val
    have hadd : u3.val ||| b59.val * 2^24 = u3.val + b59.val * 2^24 := by
      calc u3.val ||| b59.val * 2^24
          = u3.val ||| 2^24 * b59.val := by rw [Nat.mul_comm]
        _ = 2^24 * b59.val ||| u3.val := Nat.lor_comm _ _
        _ = 2^24 * b59.val + u3.val := hor.symm
        _ = u3.val + b59.val * 2^24 := by ring
    simp only [hy3, UScalar.val_or, ht3v]
    rw [hadd, hu3v]
    all_goals ring
  step as ⟨wn3, hwn3⟩
  try simp only [spec_ok]
  -- refold and hand over to the tail lemma at the j = 4 boundary
  show backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts_loop0_loop0 iter3 bytes wn3 7#usize
    ⦃ ws => ∃ v : U64, (↑ws : List U64) = [w0, w1, w2, w3, w4, w5, w6, v] ∧
        v.val = b56.val + b57.val * 2^8 + b58.val * 2^16 + b59.val * 2^24 + b60.val * 2^32 + b61.val * 2^40 + b62.val * 2^48 + b63.val * 2^56 ⦄
  have hwn3l : (↑wn3 : List U64) = [w0, w1, w2, w3, w4, w5, w6, y3] := by
    simp [hwn0, hwn1, hwn2, hwn3, hw, Array.set_val_eq]
  have hst3 : iter3.start.val = 4 := by
    simp [hs3, hs2, hs1, hs0]
    all_goals scalar_tac
  have hend3 : iter3.«end» = 8#usize := by
    simp [he3, he2, he1, he0]
  exact bytes_word_loop_tail_7 bytes wn3 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63
    w0 w1 w2 w3 w4 w5 w6 y3 iter3 hb hwn3l hst3 hend3 hy3v

end ScalarProofs
