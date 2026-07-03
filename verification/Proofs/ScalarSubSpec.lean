/- ──────────────────────────────────────────────────────────────────────────────
   Proofs/ScalarSubSpec.lean — Scalar52 subtraction mod ℓ (value + bounds)

   WHAT THIS FILE CONTAINS
   The full two-clause spec for the transpiled `Scalar52::sub`:
   given limb-bounded inputs, `sub a b` never panics and returns s with
     scVal s = scVal a - scVal b            (if scVal b ≤ scVal a)
     scVal s = scVal a + ℓ - scVal b        (if scVal a < scVal b)
   — no hypotheses beyond ScBnd are needed: in the borrow branch the result
   is automatically < ℓ, and in the no-borrow branch it is exactly the
   ℕ-difference (callers derive canonicity per use-site; see scalar_sub_spec
   below and ScalarAddSpec.lean).

   RUST ANALOG (solana curve25519 fork, src/backend/serial/u64/scalar.rs:177-191)
     let mut difference = Scalar52::ZERO; let mask = (1u64 << 52) - 1;
     let mut borrow: u64 = 0;
     for i in 0..5 {
         borrow = a[i].wrapping_sub(b[i] + (borrow >> 63));
         difference[i] = borrow & mask;
     }
     let underflow = Choice::from((borrow >> 63) as u8);
     difference.conditional_add_l(underflow);   // + ℓ iff underflow
   Transpiled: `Scalar52.sub` → `sub_loop` (5 iterations) →
   `conditional_add_l` → `conditional_add_l_loop` (5 iterations), in
   gen/CurveScalar/Funs.lean. The `subtle` Choice/conditional_select are
   faithful models in gen/CurveScalar/FunsExternal.lean (documented there).

   PROOF ARCHITECTURE (the post-OOM discipline, cf. control repo METHOD 4)
   1. `nat_and_mask52` / `nat_shift52` / `nat_shift63` — bit ops → %,/ .
   2. `sub_step_arith` — ONE limb's borrow accounting, an isolated ℕ lemma
      with a tiny context:  d + b + β_in = a + 2^52·β_out,  β ∈ {0,1}.
   3. `sub_loop_spec` — 5-fold unroll via loop_step/range_next_*_spec
      (infrastructure from Proofs/ScalarLoop.lean), producing the five
      per-limb equations and the borrow bit.
   4. `cond_add_l_spec` — 5-fold unroll of the conditional add of L, per-limb
      carry accounting (γ chain), both Choice cases.
   5. Telescoping is done at the scVal level over ℤ with explicitly stated
      linear combinations (certificates checked, never searched — the
      kernel-capacity lesson from the pasta campaign).
   6. `sub_val_spec` (general) and `scalar_sub_spec` (canonical certificate).

   ROLE IN THE PYRAMID
   Second brick of the scalar layer (after ScalarDenote's L_val): with add
   (ScalarAddSpec.lean) it gives the group ℤ/ℓ its verified + and −.
   ────────────────────────────────────────────────────────────────────────────── -/
import Proofs.ScalarDenote
import Proofs.ScalarLoop
import Mathlib.Tactic.LinearCombination
open Aeneas Aeneas.Std Result
open curve25519

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 300

namespace ScalarProofs

open Aeneas.Std.WP

/-! ### Bit-op ↔ arithmetic conversion (ℕ level)

The scalar code uses the 52-bit mask and shifts by 52 / 63; convert them to
`%` / `/` so `omega` can reason. Same pattern as the field layer's
`nat_and_mask` / `nat_shift_div` (Proofs/ReduceSpec.lean), at the scalar
radix. 4503599627370495 = 2^52 − 1, 4503599627370496 = 2^52. -/

theorem nat_and_mask52 (n : ℕ) : n &&& (2^52 - 1) = n % 2^52 :=
  Nat.and_two_pow_sub_one_eq_mod n 52

theorem nat_shift52 (n : ℕ) : n >>> 52 = n / 2^52 := by
  simp [Nat.shiftRight_eq_div_pow]

theorem nat_shift63 (n : ℕ) : n >>> 63 = n / 2^63 := by
  simp [Nat.shiftRight_eq_div_pow]

/-! ### The isolated per-limb borrow step (ℕ, tiny context) -/

/-- One limb of the subtraction loop, as pure ℕ arithmetic.

    MATH: for a, b < 2^52 and borrow-in bit β ∈ {0,1}, let
      w  = (a + 2^64 − (b + β)) % 2^64     (the wrapping_sub result)
      d  = w % 2^52                        (the stored limb, w &&& mask)
      β' = w / 2^63                        (the borrow-out bit, w >>> 63)
    then  β' ≤ 1  and  d + b + β = a + 2^52 · β'.

    WHY THIS SHAPE: the identity is stated with the correction on the LEFT so
    it lives entirely in ℕ (no truncated subtraction anywhere) — the exact
    discipline the toy system's proof used (curriculum Interlude, I.4).
    The context is five small naturals; `omega` decides it without any
    2^260-scale coefficients entering a certificate. -/
theorem sub_step_arith (a b β : ℕ) (ha : a < 2^52) (hb : b < 2^52) (hβ : β ≤ 1) :
    (a + 2^64 - (b + β)) % 2^64 / 2^63 ≤ 1 ∧
    (a + 2^64 - (b + β)) % 2^64 % 2^52 + b + β
      = a + 2^52 * ((a + 2^64 - (b + β)) % 2^64 / 2^63) := by
  constructor
  · omega
  · omega


/-! ### ZERO's limbs -/

/-- `Scalar52::ZERO` is five zero limbs. Rust: scalar.rs:62. -/
theorem ZERO_limbs :
    (↑backend.serial.u64.scalar.Scalar52.ZERO : List U64) = [0#u64, 0#u64, 0#u64, 0#u64, 0#u64] := by
  unfold backend.serial.u64.scalar.Scalar52.ZERO
  rfl

/-! ### The subtraction loop, unrolled 5-fold

Same architecture as the field layer's `add_limbs_spec`
(Proofs/AddSpec.lean): `loop_step` peels an iteration, `range_next_lt_spec`
steps the iterator, `step` runs each body operation, and the 6th peel
(`range_next_ge_spec`, 5 ≥ 5) exits. The postcondition carries the five
per-limb borrow equations of `sub_step_arith` plus the final borrow bit. -/

/-- Limb-level spec for `sub_loop` started in its actual initial state
    (range 0..5, difference = ZERO, borrow = 0), for 52-bit-bounded inputs.

    MATH: there exist limbs d0..d4 (< 2^52) and borrow bits β1..β5 ∈ {0,1}:
      d_i + b_i + β_i = a_i + 2^52·β_{i+1}   (β_0 = 0)
    and the returned borrow word w has w >>> 63 = β5.
    Telescoping these five equations (done by the caller) gives
      scLimbs d + scVal b = scLimbs a + 2^260·β5. -/
theorem sub_loop_spec (a b : Sc) (mask : U64)
    (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : U64)
    (ha : (↑a : List U64) = [a0, a1, a2, a3, a4])
    (hb : (↑b : List U64) = [b0, b1, b2, b3, b4])
    (hmask : mask.val = 2^52 - 1)
    (hbnd : a0.val < 2^52 ∧ a1.val < 2^52 ∧ a2.val < 2^52 ∧ a3.val < 2^52 ∧ a4.val < 2^52 ∧
            b0.val < 2^52 ∧ b1.val < 2^52 ∧ b2.val < 2^52 ∧ b3.val < 2^52 ∧ b4.val < 2^52) :
    backend.serial.u64.scalar.Scalar52.sub_loop
        { start := 0#usize, «end» := 5#usize } a b
        backend.serial.u64.scalar.Scalar52.ZERO mask 0#u64
      ⦃ (dw : Sc × U64) => ∃ d0 d1 d2 d3 d4 : U64, ∃ β1 β2 β3 β4 β5 : ℕ,
          (↑dw.1 : List U64) = [d0, d1, d2, d3, d4] ∧
          β1 ≤ 1 ∧ β2 ≤ 1 ∧ β3 ≤ 1 ∧ β4 ≤ 1 ∧ β5 ≤ 1 ∧
          d0.val < 2^52 ∧ d1.val < 2^52 ∧ d2.val < 2^52 ∧ d3.val < 2^52 ∧ d4.val < 2^52 ∧
          d0.val + b0.val = a0.val + 2^52 * β1 ∧
          d1.val + b1.val + β1 = a1.val + 2^52 * β2 ∧
          d2.val + b2.val + β2 = a2.val + 2^52 * β3 ∧
          d3.val + b3.val + β3 = a3.val + 2^52 * β4 ∧
          d4.val + b4.val + β4 = a4.val + 2^52 * β5 ∧
          dw.2.val >>> 63 = β5 ⦄ := by
  obtain ⟨hA0, hA1, hA2, hA3, hA4, hB0, hB1, hB2, hB3, hB4⟩ := hbnd
  unfold backend.serial.u64.scalar.Scalar52.sub_loop
  -- Iteration 1 (i = 0, borrow-in = 0)
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.sub_loop.body,
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexUsizeU64.index,
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexMutUsizeU64.index_mut]
  step with range_next_lt_spec as ⟨o1, iter1, ho1, hs1, he1⟩
  simp only [ho1]
  step as ⟨x1, hx1⟩
  step as ⟨y1, hy1⟩
  simp [ha, hb] at hx1 hy1
  step as ⟨sh1, hsh1⟩
  step as ⟨t1, ht1⟩
  step as ⟨w1, hw1⟩
  step as ⟨p1, back1, hpe1, hbk1⟩
  step as ⟨m1, hm1⟩
  try simp only [spec_ok]
  -- Iteration 2 (i = 1)
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.sub_loop.body,
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexUsizeU64.index,
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexMutUsizeU64.index_mut]
  step with range_next_lt_spec as ⟨o2, iter2, ho2, hs2, he2⟩
  simp only [ho2]
  step as ⟨x2, hx2⟩
  step as ⟨y2, hy2⟩
  simp [ha, hb, hs1, he1] at hx2 hy2
  step as ⟨sh2, hsh2⟩
  have hsh2b : sh2.val ≤ 1 := by
    have h64 : w1.val < 2^64 := by scalar_tac
    rw [hsh2, nat_shift63]; omega
  have hy2b : y2.val < 2^52 := by simp only [hy2]; exact hB1
  step as ⟨t2, ht2⟩
  step as ⟨w2, hw2⟩
  step as ⟨p2, back2, hpe2, hbk2⟩
  step as ⟨m2, hm2⟩
  try simp only [spec_ok]
  -- Iteration 3 (i = 2)
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.sub_loop.body,
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexUsizeU64.index,
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexMutUsizeU64.index_mut]
  step with range_next_lt_spec as ⟨o3, iter3, ho3, hs3, he3⟩
  simp only [ho3]
  step as ⟨x3, hx3⟩
  step as ⟨y3, hy3⟩
  simp [ha, hb, hs1, he1, hs2, he2] at hx3 hy3
  step as ⟨sh3, hsh3⟩
  have hsh3b : sh3.val ≤ 1 := by
    have h64 : w2.val < 2^64 := by scalar_tac
    rw [hsh3, nat_shift63]; omega
  have hy3b : y3.val < 2^52 := by simp only [hy3]; exact hB2
  step as ⟨t3, ht3⟩
  step as ⟨w3, hw3⟩
  step as ⟨p3, back3, hpe3, hbk3⟩
  step as ⟨m3, hm3⟩
  try simp only [spec_ok]
  -- Iteration 4 (i = 3)
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.sub_loop.body,
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexUsizeU64.index,
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexMutUsizeU64.index_mut]
  step with range_next_lt_spec as ⟨o4, iter4, ho4, hs4, he4⟩
  simp only [ho4]
  step as ⟨x4, hx4⟩
  step as ⟨y4, hy4⟩
  simp [ha, hb, hs1, he1, hs2, he2, hs3, he3] at hx4 hy4
  step as ⟨sh4, hsh4⟩
  have hsh4b : sh4.val ≤ 1 := by
    have h64 : w3.val < 2^64 := by scalar_tac
    rw [hsh4, nat_shift63]; omega
  have hy4b : y4.val < 2^52 := by simp only [hy4]; exact hB3
  step as ⟨t4, ht4⟩
  step as ⟨w4, hw4⟩
  step as ⟨p4, back4, hpe4, hbk4⟩
  step as ⟨m4, hm4⟩
  try simp only [spec_ok]
  -- Iteration 5 (i = 4)
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.sub_loop.body,
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexUsizeU64.index,
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexMutUsizeU64.index_mut]
  step with range_next_lt_spec as ⟨o5, iter5, ho5, hs5, he5⟩
  simp only [ho5]
  step as ⟨x5, hx5⟩
  step as ⟨y5, hy5⟩
  simp [ha, hb, hs1, he1, hs2, he2, hs3, he3, hs4, he4] at hx5 hy5
  step as ⟨sh5, hsh5⟩
  have hsh5b : sh5.val ≤ 1 := by
    have h64 : w4.val < 2^64 := by scalar_tac
    rw [hsh5, nat_shift63]; omega
  have hy5b : y5.val < 2^52 := by simp only [hy5]; exact hB4
  step as ⟨t5, ht5⟩
  step as ⟨w5, hw5⟩
  step as ⟨p5, back5, hpe5, hbk5⟩
  step as ⟨m5, hm5⟩
  try simp only [spec_ok]
  -- Iteration 6: range exhausted, body returns done
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.sub_loop.body,
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexUsizeU64.index,
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexMutUsizeU64.index_mut]
  step with range_next_ge_spec as ⟨o6, iter6, ho6, hr6⟩
  simp only [ho6]
  try simp only [spec_ok]
  -- ── Final assembly: exhibit limbs m1..m5 and borrow bits w_k/2^63 ──
  -- Per-limb value facts. Limb 1 (borrow-in 0):
  have hshv1 : sh1.val = 0 := by rw [hsh1]; rfl
  have htv1 : t1.val = b0.val + 0 := by rw [ht1, hy1, hshv1]
  have hwv1 : w1.val = (a0.val + 2^64 - (b0.val + 0)) % 2^64 := by
    rw [hw1]; simp only [core.num.U64.wrapping_sub, UScalar.wrapping_sub_val_eq]
    have hsz : UScalar.size UScalarTy.U64 = 2^64 := by scalar_tac
    rw [hx1, htv1, hsz]; omega
  have hmv1 : m1.val = w1.val % 2^52 := by
    rw [hm1, UScalar.val_and, hmask, nat_and_mask52]
  have harith1 := sub_step_arith a0.val b0.val 0 hA0 hB0 (by omega)
  rw [← hwv1] at harith1
  -- Limb 2:
  have hshv2 : sh2.val = w1.val / 2^63 := by rw [hsh2, nat_shift63]
  have htv2 : t2.val = b1.val + w1.val / 2^63 := by rw [ht2, hy2, hshv2]
  have hwv2 : w2.val = (a1.val + 2^64 - (b1.val + w1.val / 2^63)) % 2^64 := by
    rw [hw2]; simp only [core.num.U64.wrapping_sub, UScalar.wrapping_sub_val_eq]
    have hsz : UScalar.size UScalarTy.U64 = 2^64 := by scalar_tac
    have h64w : w1.val < 2^64 := by scalar_tac
    rw [hx2, htv2, hsz]; omega
  have hmv2 : m2.val = w2.val % 2^52 := by
    rw [hm2, UScalar.val_and, hmask, nat_and_mask52]
  have harith2 := sub_step_arith a1.val b1.val (w1.val / 2^63) hA1 hB1 harith1.1
  rw [← hwv2] at harith2
  -- Limb 3:
  have hshv3 : sh3.val = w2.val / 2^63 := by rw [hsh3, nat_shift63]
  have htv3 : t3.val = b2.val + w2.val / 2^63 := by rw [ht3, hy3, hshv3]
  have hwv3 : w3.val = (a2.val + 2^64 - (b2.val + w2.val / 2^63)) % 2^64 := by
    rw [hw3]; simp only [core.num.U64.wrapping_sub, UScalar.wrapping_sub_val_eq]
    have hsz : UScalar.size UScalarTy.U64 = 2^64 := by scalar_tac
    have h64w : w2.val < 2^64 := by scalar_tac
    rw [hx3, htv3, hsz]; omega
  have hmv3 : m3.val = w3.val % 2^52 := by
    rw [hm3, UScalar.val_and, hmask, nat_and_mask52]
  have harith3 := sub_step_arith a2.val b2.val (w2.val / 2^63) hA2 hB2 harith2.1
  rw [← hwv3] at harith3
  -- Limb 4:
  have hshv4 : sh4.val = w3.val / 2^63 := by rw [hsh4, nat_shift63]
  have htv4 : t4.val = b3.val + w3.val / 2^63 := by rw [ht4, hy4, hshv4]
  have hwv4 : w4.val = (a3.val + 2^64 - (b3.val + w3.val / 2^63)) % 2^64 := by
    rw [hw4]; simp only [core.num.U64.wrapping_sub, UScalar.wrapping_sub_val_eq]
    have hsz : UScalar.size UScalarTy.U64 = 2^64 := by scalar_tac
    have h64w : w3.val < 2^64 := by scalar_tac
    rw [hx4, htv4, hsz]; omega
  have hmv4 : m4.val = w4.val % 2^52 := by
    rw [hm4, UScalar.val_and, hmask, nat_and_mask52]
  have harith4 := sub_step_arith a3.val b3.val (w3.val / 2^63) hA3 hB3 harith3.1
  rw [← hwv4] at harith4
  -- Limb 5:
  have hshv5 : sh5.val = w4.val / 2^63 := by rw [hsh5, nat_shift63]
  have htv5 : t5.val = b4.val + w4.val / 2^63 := by rw [ht5, hy5, hshv5]
  have hwv5 : w5.val = (a4.val + 2^64 - (b4.val + w4.val / 2^63)) % 2^64 := by
    rw [hw5]; simp only [core.num.U64.wrapping_sub, UScalar.wrapping_sub_val_eq]
    have hsz : UScalar.size UScalarTy.U64 = 2^64 := by scalar_tac
    have h64w : w4.val < 2^64 := by scalar_tac
    rw [hx5, htv5, hsz]; omega
  have hmv5 : m5.val = w5.val % 2^52 := by
    rw [hm5, UScalar.val_and, hmask, nat_and_mask52]
  have harith5 := sub_step_arith a4.val b4.val (w4.val / 2^63) hA4 hB4 harith4.1
  rw [← hwv5] at harith5
  -- Witnesses and discharge
  refine ⟨m1, m2, m3, m4, m5,
          w1.val / 2^63, w2.val / 2^63, w3.val / 2^63, w4.val / 2^63, w5.val / 2^63,
          ?_, harith1.1, harith2.1, harith3.1, harith4.1, harith5.1,
          by omega, by omega, by omega, by omega, by omega,
          ?_, ?_, ?_, ?_, ?_, nat_shift63 _⟩
  · -- the result array is ZERO overwritten at 0..4 with m1..m5
    simp [hbk1, hbk2, hbk3, hbk4, hbk5, Array.set_val_eq, ZERO_limbs,
          hs1, hs2, hs3, hs4]
  · rw [hmv1]; omega
  · rw [hmv2]; omega
  · rw [hmv3]; omega
  · rw [hmv4]; omega
  · rw [hmv5]; omega



/-- Step-spec for the `subtle` conditional select (faithful model). -/
theorem csel_step (a b : U64) (c : subtle.Choice) :
    U64.Insts.SubtleConditionallySelectable.conditional_select a b c
      ⦃ r => r = (if c.val = 0 then a else b) ⦄ := by
  unfold U64.Insts.SubtleConditionallySelectable.conditional_select
  simp only [spec_ok]

/-! ### The conditional add of L, unrolled

`conditional_add_l(self, c)` adds `c ? L : 0` limb-wise with carry
propagation (Rust scalar.rs:193-204). Two cases, two lemmas: the Choice
invariant gives `c.val ∈ {0,1}` (the `subtle` model in
gen/CurveScalar/FunsExternal.lean). -/

/-- `conditional_add_l` with condition 0: identity on 52-bit-bounded limbs. -/
theorem cond_add_l_zero_spec (s : Sc) (c : subtle.Choice)
    (s0 s1 s2 s3 s4 : U64)
    (hs : (↑s : List U64) = [s0, s1, s2, s3, s4])
    (hc : c.val = 0)
    (hbnd : s0.val < 2^52 ∧ s1.val < 2^52 ∧ s2.val < 2^52 ∧ s3.val < 2^52 ∧ s4.val < 2^52) :
    backend.serial.u64.scalar.Scalar52.conditional_add_l s c
      ⦃ (cw : U64 × Sc) => ∃ r0 r1 r2 r3 r4 : U64,
          (↑cw.2 : List U64) = [r0, r1, r2, r3, r4] ∧
          r0.val = s0.val ∧ r1.val = s1.val ∧ r2.val = s2.val ∧
          r3.val = s3.val ∧ r4.val = s4.val ⦄ := by
  obtain ⟨hS0, hS1, hS2, hS3, hS4⟩ := hbnd
  unfold backend.serial.u64.scalar.Scalar52.conditional_add_l
  step as ⟨sh, hsh⟩
  step as ⟨mask, hmask⟩
  have hmaskv : mask.val = 2^52 - 1 := by
    simp [hmask, hsh, U64.size_def, U64.numBits]
  unfold backend.serial.u64.scalar.Scalar52.conditional_add_l_loop
  -- Iteration 1 (i = 0, carry-in 0, addend 0)
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.conditional_add_l_loop.body,
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexUsizeU64.index,
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexMutUsizeU64.index_mut,
    U64.Insts.SubtleConditionallySelectable.conditional_select,
    hc, reduceIte, bind_tc_ok]
  step with range_next_lt_spec as ⟨o1, iter1, ho1, hs1, he1⟩
  simp only [ho1]
  step as ⟨l1, hl1⟩
  step as ⟨g1, hg1⟩
  step as ⟨u1, hu1⟩
  simp [hs] at hu1
  step as ⟨v1, hv1⟩
  step as ⟨cy1, hcy1⟩
  step as ⟨q1, bk1, hq1, hbk1⟩
  step as ⟨r1, hr1⟩
  try simp only [spec_ok]
  have hgv1 : g1.val = 0 := by rw [hg1]; rfl
  have hcyv1 : cy1.val = s0.val := by rw [hcy1, hv1, hu1, hgv1]; simp
  have hcyb1 : cy1.val < 2^52 := by rw [hcyv1]; exact hS0
  have hrv1 : r1.val = s0.val := by
    rw [hr1, UScalar.val_and, hmaskv, nat_and_mask52, hcyv1, Nat.mod_eq_of_lt hS0]
  -- Iteration 2 (i = 1)
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.conditional_add_l_loop.body,
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexUsizeU64.index,
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexMutUsizeU64.index_mut,
    U64.Insts.SubtleConditionallySelectable.conditional_select,
    hc, reduceIte, bind_tc_ok]
  step with range_next_lt_spec as ⟨o2, iter2, ho2, hs2, he2⟩
  simp only [ho2]
  step as ⟨l2, hl2⟩
  step as ⟨g2, hg2⟩
  step as ⟨u2, hu2⟩
  simp [hbk1, Array.set_val_eq, hs, hs1, he1] at hu2
  have hgv2 : g2.val = 0 := by rw [hg2, nat_shift52, hcyv1]; omega
  step as ⟨v2, hv2⟩
  step as ⟨cy2, hcy2⟩
  step as ⟨q2, bk2, hq2, hbk2⟩
  step as ⟨r2, hr2⟩
  try simp only [spec_ok]
  have hcyv2 : cy2.val = s1.val := by rw [hcy2, hv2, hu2, hgv2]; simp
  have hcyb2 : cy2.val < 2^52 := by rw [hcyv2]; exact hS1
  have hrv2 : r2.val = s1.val := by
    rw [hr2, UScalar.val_and, hmaskv, nat_and_mask52, hcyv2, Nat.mod_eq_of_lt hS1]
  -- Iteration 3 (i = 2)
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.conditional_add_l_loop.body,
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexUsizeU64.index,
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexMutUsizeU64.index_mut,
    U64.Insts.SubtleConditionallySelectable.conditional_select,
    hc, reduceIte, bind_tc_ok]
  step with range_next_lt_spec as ⟨o3, iter3, ho3, hs3, he3⟩
  simp only [ho3]
  step as ⟨l3, hl3⟩
  step as ⟨g3, hg3⟩
  step as ⟨u3, hu3⟩
  simp [hbk1, hbk2, Array.set_val_eq, hs, hs1, he1, hs2, he2] at hu3
  have hgv3 : g3.val = 0 := by rw [hg3, nat_shift52, hcyv2]; omega
  step as ⟨v3, hv3⟩
  step as ⟨cy3, hcy3⟩
  step as ⟨q3, bk3, hq3, hbk3⟩
  step as ⟨r3, hr3⟩
  try simp only [spec_ok]
  have hcyv3 : cy3.val = s2.val := by rw [hcy3, hv3, hu3, hgv3]; simp
  have hcyb3 : cy3.val < 2^52 := by rw [hcyv3]; exact hS2
  have hrv3 : r3.val = s2.val := by
    rw [hr3, UScalar.val_and, hmaskv, nat_and_mask52, hcyv3, Nat.mod_eq_of_lt hS2]
  -- Iteration 4 (i = 3)
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.conditional_add_l_loop.body,
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexUsizeU64.index,
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexMutUsizeU64.index_mut,
    U64.Insts.SubtleConditionallySelectable.conditional_select,
    hc, reduceIte, bind_tc_ok]
  step with range_next_lt_spec as ⟨o4, iter4, ho4, hs4, he4⟩
  simp only [ho4]
  step as ⟨l4, hl4⟩
  step as ⟨g4, hg4⟩
  step as ⟨u4, hu4⟩
  simp [hbk1, hbk2, hbk3, Array.set_val_eq, hs, hs1, he1, hs2, he2, hs3, he3] at hu4
  have hgv4 : g4.val = 0 := by rw [hg4, nat_shift52, hcyv3]; omega
  step as ⟨v4, hv4⟩
  step as ⟨cy4, hcy4⟩
  step as ⟨q4, bk4, hq4, hbk4⟩
  step as ⟨r4, hr4⟩
  try simp only [spec_ok]
  have hcyv4 : cy4.val = s3.val := by rw [hcy4, hv4, hu4, hgv4]; simp
  have hcyb4 : cy4.val < 2^52 := by rw [hcyv4]; exact hS3
  have hrv4 : r4.val = s3.val := by
    rw [hr4, UScalar.val_and, hmaskv, nat_and_mask52, hcyv4, Nat.mod_eq_of_lt hS3]
  -- Iteration 5 (i = 4)
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.conditional_add_l_loop.body,
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexUsizeU64.index,
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexMutUsizeU64.index_mut,
    U64.Insts.SubtleConditionallySelectable.conditional_select,
    hc, reduceIte, bind_tc_ok]
  step with range_next_lt_spec as ⟨o5, iter5, ho5, hs5, he5⟩
  simp only [ho5]
  step as ⟨l5, hl5⟩
  step as ⟨g5, hg5⟩
  step as ⟨u5, hu5⟩
  simp [hbk1, hbk2, hbk3, hbk4, Array.set_val_eq, hs, hs1, he1, hs2, he2, hs3, he3,
        hs4, he4] at hu5
  have hgv5 : g5.val = 0 := by rw [hg5, nat_shift52, hcyv4]; omega
  step as ⟨v5, hv5⟩
  step as ⟨cy5, hcy5⟩
  step as ⟨q5, bk5, hq5, hbk5⟩
  step as ⟨r5, hr5⟩
  try simp only [spec_ok]
  have hcyv5 : cy5.val = s4.val := by rw [hcy5, hv5, hu5, hgv5]; simp
  have hrv5 : r5.val = s4.val := by
    rw [hr5, UScalar.val_and, hmaskv, nat_and_mask52, hcyv5, Nat.mod_eq_of_lt hS4]
  -- Iteration 6: exhausted
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.conditional_add_l_loop.body]
  step with range_next_ge_spec as ⟨o6, iter6, ho6, hr6⟩
  simp only [ho6]
  try simp only [spec_ok]
  refine ⟨r1, r2, r3, r4, r5, ?_, hrv1, hrv2, hrv3, hrv4, hrv5⟩
  simp [hbk1, hbk2, hbk3, hbk4, hbk5, Array.set_val_eq, hs,
        hs1, hs2, hs3, hs4]


/-- `conditional_add_l` with condition 1: adds L limb-wise with carry.
    Proven by the same borrow/carry-loop technique as `sub_loop_spec`, with
    the addend stepped as its own value (`ad_i = L[i]`) rather than folded,
    so the `index_mut` write-back matches `sub_loop_spec`'s working pattern. -/
theorem cond_add_l_one_spec (s : Sc) (c : subtle.Choice)
    (s0 s1 s2 s3 s4 : U64)
    (hs : (↑s : List U64) = [s0, s1, s2, s3, s4])
    (hc : c.val = 1)
    (hbnd : s0.val < 2^52 ∧ s1.val < 2^52 ∧ s2.val < 2^52 ∧ s3.val < 2^52 ∧ s4.val < 2^52) :
    backend.serial.u64.scalar.Scalar52.conditional_add_l s c
      ⦃ (cw : U64 × Sc) => ∃ r0 r1 r2 r3 r4 : U64, ∃ γ1 γ2 γ3 γ4 γ5 : ℕ,
          (↑cw.2 : List U64) = [r0, r1, r2, r3, r4] ∧
          γ1 ≤ 1 ∧ γ2 ≤ 1 ∧ γ3 ≤ 1 ∧ γ4 ≤ 1 ∧ γ5 ≤ 1 ∧
          r0.val < 2^52 ∧ r1.val < 2^52 ∧ r2.val < 2^52 ∧ r3.val < 2^52 ∧ r4.val < 2^52 ∧
          r0.val + 2^52 * γ1 = s0.val + 671914833335277 ∧
          r1.val + 2^52 * γ2 = s1.val + 3916664325105025 + γ1 ∧
          r2.val + 2^52 * γ3 = s2.val + 1367801 + γ2 ∧
          r3.val + 2^52 * γ4 = s3.val + 0 + γ3 ∧
          r4.val + 2^52 * γ5 = s4.val + 17592186044416 + γ4 ⦄ := by
  obtain ⟨hS0, hS1, hS2, hS3, hS4⟩ := hbnd
  unfold backend.serial.u64.scalar.Scalar52.conditional_add_l
  step as ⟨sh, hsh⟩
  step as ⟨mask, hmask⟩
  have hmaskv : mask.val = 2^52 - 1 := by
    simp [hmask, hsh, U64.size_def, U64.numBits]
  unfold backend.serial.u64.scalar.Scalar52.conditional_add_l_loop
  -- Iteration 1 (i = 0, L[0] = 671914833335277)
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.conditional_add_l_loop.body,
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexUsizeU64.index,
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexMutUsizeU64.index_mut,
    bind_tc_ok]
  step with range_next_lt_spec as ⟨o1, iter1, ho1, hs1, he1⟩
  simp only [ho1]
  step as ⟨l1, hl1⟩
  simp [L_limbs] at hl1
  step with csel_step as ⟨ad1, had1⟩
  rw [hc] at had1; norm_num at had1
  have hadv1 : ad1.val = 671914833335277 := by rw [had1, hl1]; rfl
  step as ⟨g1, hg1⟩
  have hgb1 : g1.val = 0 := by rw [hg1]; rfl
  step as ⟨u1, hu1⟩
  simp [hs] at hu1
  have hub1 : u1.val < 2^52 := by rw [hu1]; exact hS0
  step as ⟨v1, hv1⟩
  have hvv1 : v1.val = u1.val := by rw [hv1, hgb1]; simp
  step as ⟨cy1, hcy1⟩
  have hcyv1 : cy1.val = u1.val + 671914833335277 := by rw [hcy1, hvv1, hadv1]
  have hcyb1 : cy1.val < 2^53 := by rw [hcyv1]; omega
  step as ⟨q1, bk1, hq1, hbk1⟩
  step as ⟨r1, hr1⟩
  try simp only [spec_ok]
  have hrv1 : r1.val = cy1.val % 2^52 := by
    rw [hr1, UScalar.val_and, hmaskv, nat_and_mask52]
  -- Iteration 2 (i = 1, L[1] = 3916664325105025)
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.conditional_add_l_loop.body,
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexUsizeU64.index,
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexMutUsizeU64.index_mut,
    bind_tc_ok]
  step with range_next_lt_spec as ⟨o2, iter2, ho2, hs2, he2⟩
  simp only [ho2]
  step as ⟨l2, hl2⟩
  simp [L_limbs, hs1, he1] at hl2
  step with csel_step as ⟨ad2, had2⟩
  rw [hc] at had2; norm_num at had2
  have hadv2 : ad2.val = 3916664325105025 := by rw [had2, hl2]; rfl
  step as ⟨g2, hg2⟩
  have hgeq2 : g2.val = cy1.val / 2^52 := by rw [hg2, nat_shift52]
  have hgb2 : g2.val ≤ 1 := by rw [hgeq2]; omega
  step as ⟨u2, hu2⟩
  simp [hbk1, Array.set_val_eq, hs, hs1, he1] at hu2
  have hub2 : u2.val < 2^52 := by rw [hu2]; exact hS1
  step as ⟨v2, hv2⟩
  have hvv2 : v2.val = g2.val + u2.val := by rw [hv2]
  step as ⟨cy2, hcy2⟩
  have hcyv2 : cy2.val = g2.val + u2.val + 3916664325105025 := by rw [hcy2, hvv2, hadv2]
  have hcyb2 : cy2.val < 2^53 := by rw [hcyv2]; omega
  step as ⟨q2, bk2, hq2, hbk2⟩
  step as ⟨r2, hr2⟩
  try simp only [spec_ok]
  have hrv2 : r2.val = cy2.val % 2^52 := by
    rw [hr2, UScalar.val_and, hmaskv, nat_and_mask52]
  -- Iteration 3 (i = 2, L[2] = 1367801)
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.conditional_add_l_loop.body,
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexUsizeU64.index,
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexMutUsizeU64.index_mut,
    bind_tc_ok]
  step with range_next_lt_spec as ⟨o3, iter3, ho3, hs3, he3⟩
  simp only [ho3]
  step as ⟨l3, hl3⟩
  simp [L_limbs, hs1, he1, hs2, he2] at hl3
  step with csel_step as ⟨ad3, had3⟩
  rw [hc] at had3; norm_num at had3
  have hadv3 : ad3.val = 1367801 := by rw [had3, hl3]; rfl
  step as ⟨g3, hg3⟩
  have hgeq3 : g3.val = cy2.val / 2^52 := by rw [hg3, nat_shift52]
  have hgb3 : g3.val ≤ 1 := by rw [hgeq3]; omega
  step as ⟨u3, hu3⟩
  simp [hbk1, hbk2, Array.set_val_eq, hs, hs1, he1, hs2, he2] at hu3
  have hub3 : u3.val < 2^52 := by rw [hu3]; exact hS2
  step as ⟨v3, hv3⟩
  have hvv3 : v3.val = g3.val + u3.val := by rw [hv3]
  step as ⟨cy3, hcy3⟩
  have hcyv3 : cy3.val = g3.val + u3.val + 1367801 := by rw [hcy3, hvv3, hadv3]
  have hcyb3 : cy3.val < 2^53 := by rw [hcyv3]; omega
  step as ⟨q3, bk3, hq3, hbk3⟩
  step as ⟨r3, hr3⟩
  try simp only [spec_ok]
  have hrv3 : r3.val = cy3.val % 2^52 := by
    rw [hr3, UScalar.val_and, hmaskv, nat_and_mask52]
  -- Iteration 4 (i = 3, L[3] = 0)
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.conditional_add_l_loop.body,
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexUsizeU64.index,
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexMutUsizeU64.index_mut,
    bind_tc_ok]
  step with range_next_lt_spec as ⟨o4, iter4, ho4, hs4, he4⟩
  simp only [ho4]
  step as ⟨l4, hl4⟩
  simp [L_limbs, hs1, he1, hs2, he2, hs3, he3] at hl4
  step with csel_step as ⟨ad4, had4⟩
  rw [hc] at had4; norm_num at had4
  have hadv4 : ad4.val = 0 := by rw [had4, hl4]; rfl
  step as ⟨g4, hg4⟩
  have hgeq4 : g4.val = cy3.val / 2^52 := by rw [hg4, nat_shift52]
  have hgb4 : g4.val ≤ 1 := by rw [hgeq4]; omega
  step as ⟨u4, hu4⟩
  simp [hbk1, hbk2, hbk3, Array.set_val_eq, hs, hs1, he1, hs2, he2, hs3, he3] at hu4
  have hub4 : u4.val < 2^52 := by rw [hu4]; exact hS3
  step as ⟨v4, hv4⟩
  have hvv4 : v4.val = g4.val + u4.val := by rw [hv4]
  step as ⟨cy4, hcy4⟩
  have hcyv4 : cy4.val = g4.val + u4.val + 0 := by rw [hcy4, hvv4, hadv4]
  have hcyb4 : cy4.val < 2^53 := by rw [hcyv4]; omega
  step as ⟨q4, bk4, hq4, hbk4⟩
  step as ⟨r4, hr4⟩
  try simp only [spec_ok]
  have hrv4 : r4.val = cy4.val % 2^52 := by
    rw [hr4, UScalar.val_and, hmaskv, nat_and_mask52]
  -- Iteration 5 (i = 4, L[4] = 17592186044416)
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.conditional_add_l_loop.body,
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexUsizeU64.index,
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexMutUsizeU64.index_mut,
    bind_tc_ok]
  step with range_next_lt_spec as ⟨o5, iter5, ho5, hs5, he5⟩
  simp only [ho5]
  step as ⟨l5, hl5⟩
  simp [L_limbs, hs1, he1, hs2, he2, hs3, he3, hs4, he4] at hl5
  step with csel_step as ⟨ad5, had5⟩
  rw [hc] at had5; norm_num at had5
  have hadv5 : ad5.val = 17592186044416 := by rw [had5, hl5]; rfl
  step as ⟨g5, hg5⟩
  have hgeq5 : g5.val = cy4.val / 2^52 := by rw [hg5, nat_shift52]
  have hgb5 : g5.val ≤ 1 := by rw [hgeq5]; omega
  step as ⟨u5, hu5⟩
  simp [hbk1, hbk2, hbk3, hbk4, Array.set_val_eq, hs, hs1, he1, hs2, he2, hs3, he3, hs4, he4] at hu5
  have hub5 : u5.val < 2^52 := by rw [hu5]; exact hS4
  step as ⟨v5, hv5⟩
  have hvv5 : v5.val = g5.val + u5.val := by rw [hv5]
  step as ⟨cy5, hcy5⟩
  have hcyv5 : cy5.val = g5.val + u5.val + 17592186044416 := by rw [hcy5, hvv5, hadv5]
  have hcyb5 : cy5.val < 2^53 := by rw [hcyv5]; omega
  step as ⟨q5, bk5, hq5, hbk5⟩
  step as ⟨r5, hr5⟩
  try simp only [spec_ok]
  have hrv5 : r5.val = cy5.val % 2^52 := by
    rw [hr5, UScalar.val_and, hmaskv, nat_and_mask52]
  -- Iteration 6: exhausted
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.conditional_add_l_loop.body]
  step with range_next_ge_spec as ⟨o6, iter6, ho6, hr6⟩
  simp only [ho6]
  try simp only [spec_ok]
  refine ⟨r1, r2, r3, r4, r5,
          cy1.val / 2^52, cy2.val / 2^52, cy3.val / 2^52, cy4.val / 2^52, cy5.val / 2^52,
          ?_, by omega, by omega, by omega, by omega, by omega,
          by rw [hrv1]; omega, by rw [hrv2]; omega, by rw [hrv3]; omega,
          by rw [hrv4]; omega, by rw [hrv5]; omega,
          ?_, ?_, ?_, ?_, ?_⟩
  · simp [hbk1, hbk2, hbk3, hbk4, hbk5, Array.set_val_eq, hs, hs1, hs2, hs3, hs4]
  · rw [hrv1, hcyv1, hu1]; omega
  · rw [hrv2, hcyv2, hu2, hgeq2]; omega
  · rw [hrv3, hcyv3, hu3, hgeq3]; omega
  · rw [hrv4, hcyv4, hu4, hgeq4]; omega
  · rw [hrv5, hcyv5, hu5, hgeq5]; omega

/-- Telescoping the five borrow equations to the value level (ℕ).
    Given the per-limb identities d_i + b_i + β_i = a_i + 2^52·β_{i+1}
    (β_0 = 0), the weighted sum gives
      scLimbs d + scLimbs b = scLimbs a + 2^260·β5.
    Coefficients reach 2^260; stated as an explicit linear identity so the
    kernel checks (never searches) it — the METHOD-4 discipline. -/
theorem sub_telescope
    (d0 d1 d2 d3 d4 b0 b1 b2 b3 b4 a0 a1 a2 a3 a4 : ℕ)
    (β1 β2 β3 β4 β5 : ℕ)
    (e0 : d0 + b0 = a0 + 2^52 * β1)
    (e1 : d1 + b1 + β1 = a1 + 2^52 * β2)
    (e2 : d2 + b2 + β2 = a2 + 2^52 * β3)
    (e3 : d3 + b3 + β3 = a3 + 2^52 * β4)
    (e4 : d4 + b4 + β4 = a4 + 2^52 * β5) :
    (d0 + 2^52*d1 + 2^104*d2 + 2^156*d3 + 2^208*d4)
      + (b0 + 2^52*b1 + 2^104*b2 + 2^156*b3 + 2^208*b4)
      = (a0 + 2^52*a1 + 2^104*a2 + 2^156*a3 + 2^208*a4) + 2^260 * β5 := by
  omega

/-- Telescoping the conditional-add carry chain (same shape as `sub_telescope`):
    r_i + 2^52·γ_{i+1} = s_i + c_i + γ_i (γ_0 = 0) sums to
      scLimbs r + 2^260·γ5 = scLimbs s + scLimbs c. -/
theorem add_telescope
    (r0 r1 r2 r3 r4 s0 s1 s2 s3 s4 c0 c1 c2 c3 c4 : ℕ)
    (γ1 γ2 γ3 γ4 γ5 : ℕ)
    (e0 : r0 + 2^52 * γ1 = s0 + c0)
    (e1 : r1 + 2^52 * γ2 = s1 + c1 + γ1)
    (e2 : r2 + 2^52 * γ3 = s2 + c2 + γ2)
    (e3 : r3 + 2^52 * γ4 = s3 + c3 + γ3)
    (e4 : r4 + 2^52 * γ5 = s4 + c4 + γ4) :
    (r0 + 2^52*r1 + 2^104*r2 + 2^156*r3 + 2^208*r4) + 2^260 * γ5
      = (s0 + 2^52*s1 + 2^104*s2 + 2^156*s3 + 2^208*s4)
        + (c0 + 2^52*c1 + 2^104*c2 + 2^156*c3 + 2^208*c4) := by
  omega

/-! ### Top-level subtraction value spec -/

/-- **Scalar subtraction is correct mod ℓ.** For limb-bounded inputs with
    canonical subtrahend (scVal b < ℓ), the transpiled `Scalar52::sub`
    denotes ⟦a⟧ − ⟦b⟧ in `ZMod ℓ`. Assembly of `sub_loop_spec` (borrow
    chain) and `cond_add_l_{zero,one}_spec` (conditional +ℓ) through the
    two telescopes; the bind is applied manually via `spec_bind` to keep
    full control of the postcondition destructuring. The post also
    exposes the result's limbs with their 52-bit bounds (both branches
    end in mask-&-store loops), so downstream compositions —
    `montgomery_reduce`'s final canonicalization feeding `mul_internal`
    again — can consume the result without re-proving boundedness. -/
theorem sub_val_spec (a b : Sc)
    (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : U64)
    (ha : (↑a : List U64) = [a0, a1, a2, a3, a4])
    (hb : (↑b : List U64) = [b0, b1, b2, b3, b4])
    (hab : a0.val < 2^52 ∧ a1.val < 2^52 ∧ a2.val < 2^52 ∧ a3.val < 2^52 ∧ a4.val < 2^52)
    (hbb : b0.val < 2^52 ∧ b1.val < 2^52 ∧ b2.val < 2^52 ∧ b3.val < 2^52 ∧ b4.val < 2^52)
    (hcb : scVal b ≤ Ell) :
    backend.serial.u64.scalar.Scalar52.sub a b
      ⦃ r => (∃ s0 s1 s2 s3 s4 : U64, (↑r : List U64) = [s0, s1, s2, s3, s4] ∧
              s0.val < 2^52 ∧ s1.val < 2^52 ∧ s2.val < 2^52 ∧ s3.val < 2^52 ∧ s4.val < 2^52) ∧
            scDenote r = scDenote a - scDenote b ⦄ := by
  obtain ⟨hA0, hA1, hA2, hA3, hA4⟩ := hab
  obtain ⟨hB0, hB1, hB2, hB3, hB4⟩ := hbb
  unfold backend.serial.u64.scalar.Scalar52.sub
  step as ⟨sh, hsh⟩
  step as ⟨mask, hmask⟩
  have hmaskv : mask.val = 2^52 - 1 := by
    simp [hmask, hsh, U64.size_def, U64.numBits]
  -- bind the borrow loop manually
  apply spec_bind (sub_loop_spec a b mask a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 ha hb hmaskv
      ⟨hA0, hA1, hA2, hA3, hA4, hB0, hB1, hB2, hB3, hB4⟩)
  rintro ⟨dw, w⟩ ⟨d0, d1, d2, d3, d4, β1, β2, β3, β4, β5, hdl,
    hβ1, hβ2, hβ3, hβ4, hβ5, hd0, hd1, hd2, hd3, hd4,
    he0, he1, he2, he3, he4, hbor⟩
  simp only at hdl hbor
  show (do
    let i1 ← w >>> 63#i32
    let i2 ← lift (UScalar.cast UScalarTy.U8 i1)
    let c ← subtle.Choice.Insts.CoreConvertFromU8.from i2
    let (_, difference1) ← dw.conditional_add_l c
    ok difference1) ⦃ r =>
      (∃ s0 s1 s2 s3 s4 : U64, (↑r : List U64) = [s0, s1, s2, s3, s4] ∧
        s0.val < 2^52 ∧ s1.val < 2^52 ∧ s2.val < 2^52 ∧ s3.val < 2^52 ∧ s4.val < 2^52) ∧
      scDenote r = scDenote a - scDenote b ⦄
  -- borrow >>> 63, cast, Choice
  step as ⟨i1, hi1⟩
  have hi1v : i1.val = β5 := by rw [hi1]; exact hbor
  step as ⟨i2, hi2⟩
  -- Choice.from is the identity model; inline c := i2
  simp only [subtle.Choice.Insts.CoreConvertFromU8.from, bind_tc_ok]
  set cc := i2 with hccdef
  have hccv : cc.val = β5 := by
    have hb5 : β5 < 2^8 := by omega
    rw [hi2, UScalar.cast_val_eq, hi1v]
    simp only [UScalarTy.U8, UScalarTy.numBits]
    omega
  have hdb : d0.val < 2^52 ∧ d1.val < 2^52 ∧ d2.val < 2^52 ∧ d3.val < 2^52 ∧ d4.val < 2^52 :=
    ⟨hd0, hd1, hd2, hd3, hd4⟩
  have hTsub : scLimbs d0 d1 d2 d3 d4 + scLimbs b0 b1 b2 b3 b4
      = scLimbs a0 a1 a2 a3 a4 + 2^260 * β5 := by
    unfold scLimbs
    exact sub_telescope _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ he0 he1 he2 he3 he4
  have hsva : scVal a = scLimbs a0 a1 a2 a3 a4 := scVal_eq a a0 a1 a2 a3 a4 ha
  have hsvb : scVal b = scLimbs b0 b1 b2 b3 b4 := scVal_eq b b0 b1 b2 b3 b4 hb
  rcases (Nat.le_one_iff_eq_zero_or_eq_one.mp hβ5) with hβz | hβo
  · -- β5 = 0: no underflow, cond-add is identity on values
    have hc0 : cc.val = 0 := by rw [hccv, hβz]
    apply spec_bind (cond_add_l_zero_spec dw cc d0 d1 d2 d3 d4 hdl hc0 hdb)
    rintro ⟨cw1, cw2⟩ ⟨r0, r1, r2, r3, r4, hrl, hr0, hr1, hr2, hr3, hr4⟩
    simp only at hrl
    show (∃ s0 s1 s2 s3 s4 : U64, (↑cw2 : List U64) = [s0, s1, s2, s3, s4] ∧
        s0.val < 2^52 ∧ s1.val < 2^52 ∧ s2.val < 2^52 ∧ s3.val < 2^52 ∧ s4.val < 2^52) ∧
      scDenote cw2 = scDenote a - scDenote b
    refine ⟨⟨r0, r1, r2, r3, r4, hrl,
      by omega, by omega, by omega, by omega, by omega⟩, ?_⟩
    have hcwval : scVal cw2 = scLimbs d0 d1 d2 d3 d4 := by
      rw [scVal_eq cw2 r0 r1 r2 r3 r4 hrl]; unfold scLimbs; rw [hr0, hr1, hr2, hr3, hr4]
    have key : scVal cw2 + scVal b = scVal a := by
      rw [hcwval, hsva, hsvb]; rw [hβz] at hTsub; simpa using hTsub
    have hc := congrArg (Nat.cast (R := ZMod Ell)) key
    push_cast at hc
    simp only [scDenote]; rw [eq_sub_iff_add_eq]; exact hc
  · -- β5 = 1: underflow; +ℓ, and the 2^260 wrap cancels in ZMod ℓ
    have hc1 : cc.val = 1 := by rw [hccv, hβo]
    apply spec_bind (cond_add_l_one_spec dw cc d0 d1 d2 d3 d4 hdl hc1 hdb)
    rintro ⟨cw1, cw2⟩ ⟨r0, r1, r2, r3, r4, γ1, γ2, γ3, γ4, γ5, hrl,
      hgb1, hgb2, hgb3, hgb4, hgb5, hrb0, hrb1, hrb2, hrb3, hrb4,
      hf0, hf1, hf2, hf3, hf4⟩
    simp only at hrl
    show (∃ s0 s1 s2 s3 s4 : U64, (↑cw2 : List U64) = [s0, s1, s2, s3, s4] ∧
        s0.val < 2^52 ∧ s1.val < 2^52 ∧ s2.val < 2^52 ∧ s3.val < 2^52 ∧ s4.val < 2^52) ∧
      scDenote cw2 = scDenote a - scDenote b
    refine ⟨⟨r0, r1, r2, r3, r4, hrl, hrb0, hrb1, hrb2, hrb3, hrb4⟩, ?_⟩
    have hLsum : (671914833335277 + 2^52*3916664325105025 + 2^104*1367801
        + 2^156*0 + 2^208*17592186044416 : ℕ) = Ell := by unfold Ell; norm_num
    have hTadd : scLimbs r0 r1 r2 r3 r4 + 2^260 * γ5 = scLimbs d0 d1 d2 d3 d4 + Ell := by
      have h := add_telescope r0.val r1.val r2.val r3.val r4.val
        d0.val d1.val d2.val d3.val d4.val
        671914833335277 3916664325105025 1367801 0 17592186044416
        γ1 γ2 γ3 γ4 γ5 hf0 hf1 hf2 hf3 hf4
      unfold scLimbs; rw [← hLsum]; linear_combination h
    have hblt : scLimbs b0 b1 b2 b3 b4 ≤ Ell := by rw [← hsvb]; exact hcb
    -- γ5 = 1, derived with scLimbs kept as opaque atoms (no 2^52i unfold →
    -- omega stays cheap: 4 atoms + one 2^260 literal + Ell as an atom)
    have hrlt : scLimbs r0 r1 r2 r3 r4 < 2^260 := by unfold scLimbs; omega
    have hd_eq : scLimbs d0 d1 d2 d3 d4 + scLimbs b0 b1 b2 b3 b4
        = scLimbs a0 a1 a2 a3 a4 + 2^260 := by rw [hβo] at hTsub; simpa using hTsub
    have hγ5 : γ5 = 1 := by
      -- atoms: R,D,B,A := scLimbs …, Ell; facts below force γ5 = 1
      have hRnn : 0 ≤ scLimbs a0 a1 a2 a3 a4 := Nat.zero_le _
      omega
    have hc := congrArg (Nat.cast (R := ZMod Ell)) hTadd
    have hc2 := congrArg (Nat.cast (R := ZMod Ell)) hTsub
    have hEz : (Ell : ZMod Ell) = 0 := ZMod.natCast_self Ell
    simp only [scDenote, scVal_eq cw2 r0 r1 r2 r3 r4 hrl, hsva, hsvb, hβo, hγ5]
    rw [hγ5] at hc
    rw [hβo] at hc2
    push_cast at hc hc2 ⊢
    rw [hEz] at hc
    linear_combination hc + hc2

end ScalarProofs
