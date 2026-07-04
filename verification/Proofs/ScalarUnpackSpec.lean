/- Proofs/ScalarUnpackSpec.lean — from_bytes_wide, stage 2: the outer
   unpack loop composes the eight per-word inner lemmas. -/
import Proofs.ScalarBytesSpec
open Aeneas Aeneas.Std Result
open curve25519

set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 600

namespace ScalarProofs

open Aeneas.Std.WP

/-- The outer unpack loop: eight inner passes fill words 0..7 with the
    64 bytes little-endian. One `bytes_word_loop_spec_I` per peel. -/
theorem bytes_unpack_spec (bytes : Std.Array Std.U8 64#usize)
    (words : Std.Array Std.U64 8#usize)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63 : Std.U8)
    (w0 w1 w2 w3 w4 w5 w6 w7 : U64)
    (hb : (↑bytes : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63])
    (hw : (↑words : List U64) = [w0, w1, w2, w3, w4, w5, w6, w7])
    (hz : w0.val = 0 ∧ w1.val = 0 ∧ w2.val = 0 ∧ w3.val = 0 ∧ w4.val = 0 ∧ w5.val = 0 ∧ w6.val = 0 ∧ w7.val = 0) :
    backend.serial.u64.scalar.Scalar52.from_bytes_wide_loop0 { start := 0#usize, «end» := 8#usize } bytes words
      ⦃ ws => ∃ v0 v1 v2 v3 v4 v5 v6 v7 : U64,
          (↑ws : List U64) = [v0, v1, v2, v3, v4, v5, v6, v7] ∧
          v0.val = b0.val + b1.val * 2^8 + b2.val * 2^16 + b3.val * 2^24 + b4.val * 2^32 + b5.val * 2^40 + b6.val * 2^48 + b7.val * 2^56 ∧
          v1.val = b8.val + b9.val * 2^8 + b10.val * 2^16 + b11.val * 2^24 + b12.val * 2^32 + b13.val * 2^40 + b14.val * 2^48 + b15.val * 2^56 ∧
          v2.val = b16.val + b17.val * 2^8 + b18.val * 2^16 + b19.val * 2^24 + b20.val * 2^32 + b21.val * 2^40 + b22.val * 2^48 + b23.val * 2^56 ∧
          v3.val = b24.val + b25.val * 2^8 + b26.val * 2^16 + b27.val * 2^24 + b28.val * 2^32 + b29.val * 2^40 + b30.val * 2^48 + b31.val * 2^56 ∧
          v4.val = b32.val + b33.val * 2^8 + b34.val * 2^16 + b35.val * 2^24 + b36.val * 2^32 + b37.val * 2^40 + b38.val * 2^48 + b39.val * 2^56 ∧
          v5.val = b40.val + b41.val * 2^8 + b42.val * 2^16 + b43.val * 2^24 + b44.val * 2^32 + b45.val * 2^40 + b46.val * 2^48 + b47.val * 2^56 ∧
          v6.val = b48.val + b49.val * 2^8 + b50.val * 2^16 + b51.val * 2^24 + b52.val * 2^32 + b53.val * 2^40 + b54.val * 2^48 + b55.val * 2^56 ∧
          v7.val = b56.val + b57.val * 2^8 + b58.val * 2^16 + b59.val * 2^24 + b60.val * 2^32 + b61.val * 2^40 + b62.val * 2^48 + b63.val * 2^56 ⦄ := by
  obtain ⟨hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7⟩ := hz
  unfold backend.serial.u64.scalar.Scalar52.from_bytes_wide_loop0
  -- outer iteration 0
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_loop0.body]
  step with range_next_lt_spec as ⟨o0, iter0, ho0, hs0, he0⟩
  simp only [ho0]
  step with (bytes_word_loop_spec_0 bytes words b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63
    w0 w1 w2 w3 w4 w5 w6 w7 hb hw hz0) as ⟨v0, ws0, hwl0, hv0⟩
  try simp only [spec_ok]
  -- outer iteration 1
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_loop0.body]
  step with (range_next_lt_spec iter0 (by simp [hs0, he0]; all_goals scalar_tac)) as ⟨o1, iter1, ho1, hs1, he1⟩
  simp only [ho1]
  have hidx1 : iter0.start = 1#usize := by
    have hv : iter0.start.val = 1 := by simp [hs0]; all_goals scalar_tac
    scalar_tac
  rw [hidx1]
  step with (bytes_word_loop_spec_1 bytes ws0 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63
    v0 w1 w2 w3 w4 w5 w6 w7 hb hwl0 hz1) as ⟨v1, ws1, hwl1, hv1⟩
  try simp only [spec_ok]
  -- outer iteration 2
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_loop0.body]
  step with (range_next_lt_spec iter1 (by simp [hs0, he0, hs1, he1]; all_goals scalar_tac)) as ⟨o2, iter2, ho2, hs2, he2⟩
  simp only [ho2]
  have hidx2 : iter1.start = 2#usize := by
    have hv : iter1.start.val = 2 := by simp [hs0, hs1]; all_goals scalar_tac
    scalar_tac
  rw [hidx2]
  step with (bytes_word_loop_spec_2 bytes ws1 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63
    v0 v1 w2 w3 w4 w5 w6 w7 hb hwl1 hz2) as ⟨v2, ws2, hwl2, hv2⟩
  try simp only [spec_ok]
  -- outer iteration 3
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_loop0.body]
  step with (range_next_lt_spec iter2 (by simp [hs0, he0, hs1, he1, hs2, he2]; all_goals scalar_tac)) as ⟨o3, iter3, ho3, hs3, he3⟩
  simp only [ho3]
  have hidx3 : iter2.start = 3#usize := by
    have hv : iter2.start.val = 3 := by simp [hs0, hs1, hs2]; all_goals scalar_tac
    scalar_tac
  rw [hidx3]
  step with (bytes_word_loop_spec_3 bytes ws2 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63
    v0 v1 v2 w3 w4 w5 w6 w7 hb hwl2 hz3) as ⟨v3, ws3, hwl3, hv3⟩
  try simp only [spec_ok]
  -- outer iteration 4
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_loop0.body]
  step with (range_next_lt_spec iter3 (by simp [hs0, he0, hs1, he1, hs2, he2, hs3, he3]; all_goals scalar_tac)) as ⟨o4, iter4, ho4, hs4, he4⟩
  simp only [ho4]
  have hidx4 : iter3.start = 4#usize := by
    have hv : iter3.start.val = 4 := by simp [hs0, hs1, hs2, hs3]; all_goals scalar_tac
    scalar_tac
  rw [hidx4]
  step with (bytes_word_loop_spec_4 bytes ws3 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63
    v0 v1 v2 v3 w4 w5 w6 w7 hb hwl3 hz4) as ⟨v4, ws4, hwl4, hv4⟩
  try simp only [spec_ok]
  -- outer iteration 5
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_loop0.body]
  step with (range_next_lt_spec iter4 (by simp [hs0, he0, hs1, he1, hs2, he2, hs3, he3, hs4, he4]; all_goals scalar_tac)) as ⟨o5, iter5, ho5, hs5, he5⟩
  simp only [ho5]
  have hidx5 : iter4.start = 5#usize := by
    have hv : iter4.start.val = 5 := by simp [hs0, hs1, hs2, hs3, hs4]; all_goals scalar_tac
    scalar_tac
  rw [hidx5]
  step with (bytes_word_loop_spec_5 bytes ws4 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63
    v0 v1 v2 v3 v4 w5 w6 w7 hb hwl4 hz5) as ⟨v5, ws5, hwl5, hv5⟩
  try simp only [spec_ok]
  -- outer iteration 6
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_loop0.body]
  step with (range_next_lt_spec iter5 (by simp [hs0, he0, hs1, he1, hs2, he2, hs3, he3, hs4, he4, hs5, he5]; all_goals scalar_tac)) as ⟨o6, iter6, ho6, hs6, he6⟩
  simp only [ho6]
  have hidx6 : iter5.start = 6#usize := by
    have hv : iter5.start.val = 6 := by simp [hs0, hs1, hs2, hs3, hs4, hs5]; all_goals scalar_tac
    scalar_tac
  rw [hidx6]
  step with (bytes_word_loop_spec_6 bytes ws5 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63
    v0 v1 v2 v3 v4 v5 w6 w7 hb hwl5 hz6) as ⟨v6, ws6, hwl6, hv6⟩
  try simp only [spec_ok]
  -- outer iteration 7
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_loop0.body]
  step with (range_next_lt_spec iter6 (by simp [hs0, he0, hs1, he1, hs2, he2, hs3, he3, hs4, he4, hs5, he5, hs6, he6]; all_goals scalar_tac)) as ⟨o7, iter7, ho7, hs7, he7⟩
  simp only [ho7]
  have hidx7 : iter6.start = 7#usize := by
    have hv : iter6.start.val = 7 := by simp [hs0, hs1, hs2, hs3, hs4, hs5, hs6]; all_goals scalar_tac
    scalar_tac
  rw [hidx7]
  step with (bytes_word_loop_spec_7 bytes ws6 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63
    v0 v1 v2 v3 v4 v5 v6 w7 hb hwl6 hz7) as ⟨v7, ws7, hwl7, hv7⟩
  try simp only [spec_ok]
  -- exit (8 ≥ 8)
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.from_bytes_wide_loop0.body]
  step with (range_next_ge_spec iter7 (by simp [hs0, he0, hs1, he1, hs2, he2, hs3, he3, hs4, he4, hs5, he5, hs6, he6, hs7, he7]; all_goals scalar_tac)) as ⟨oX, iterX, hoX, hrX⟩
  simp only [hoX]
  try simp only [spec_ok]
  exact ⟨v0, v1, v2, v3, v4, v5, v6, v7, hwl7, hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7⟩

end ScalarProofs
