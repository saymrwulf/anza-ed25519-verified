/- ──────────────────────────────────────────────────────────────────────────────
   Proofs/ScalarMontSpec.lean — Scalar52 Montgomery reduction (phase B) and
   the full multiplication `Scalar52::mul` (phase C).

   `montgomery_reduce z` folds a 9-limb double-width value Z = Σ z_k·2^52k
   down by R = 2^260: five `part1` rounds pick nonce digits n_k with
   (sum + n_k·L₀) ≡ 0 (mod 2^52) — exact division, nothing is shifted out —
   and four `part2` rounds split exactly. Telescoping the nine round
   equations gives  scLimbs r · 2^260 = Z + N·ℓ  with N = Σ n_k·2^52k,
   so in ZMod ℓ:  ⟦r⟧ · 2^260 = Z.  The final canonicalization is the
   already-proven `sub r L` (⟦L⟧ = 0).

   The arithmetic heart is the constant identity
       LFACTOR · L₀ ≡ −1 (mod 2^52),
   1439961107955227 · 671914833335277 + 1 = 214835089243030 · 2^52,
   kernel-checked by norm_num (`mont_key`).

   `mul a b` then composes: montgomery_reduce (mul_internal a b) gives
   ⟦ab⟧·R⁻¹; a second round against RR ≡ R² (mod ℓ) multiplies R back in:
   ⟦mul a b⟧ = ⟦a⟧·⟦b⟧. The first reduction needs the honest Montgomery
   hypothesis  scVal a · scVal b < 2^260·ℓ  (callers with canonical
   scalars satisfy it: ℓ² < 2^260·ℓ); the second is unconditional because
   scVal RR < ℓ.
   ────────────────────────────────────────────────────────────────────────────── -/
import Proofs.ScalarSubSpec
import Proofs.ScalarMulSpec
open Aeneas Aeneas.Std Result
open curve25519

set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 600

namespace ScalarProofs

open Aeneas.Std.WP

/-! ### The Montgomery constant identity -/

/-- The transpiled `constants::LFACTOR` value. -/
theorem LFACTOR_val : backend.serial.u64.constants.LFACTOR.val = 1439961107955227 := by
  unfold backend.serial.u64.constants.LFACTOR; rfl

/-- **The defining property of LFACTOR**: LFACTOR·L₀ ≡ −1 (mod 2^52),
    stated as an exact ℕ identity. Kernel-checked literal arithmetic. -/
theorem mont_key : (1:ℕ) + 1439961107955227 * 671914833335277 = 214835089243030 * 2^52 := by
  norm_num

/-- **Montgomery cancellation**: with the nonce p = (s·LFACTOR) mod 2^52,
    the sum s + p·L₀ has zero low 52 bits — `part1`'s shift is an exact
    division. -/
theorem mont_cancel (s p : ℕ) (hp : p = (s * 1439961107955227) % 2^52) :
    (s + p * 671914833335277) % 2^52 = 0 := by
  have hmod : p ≡ s * 1439961107955227 [MOD 2^52] := hp ▸ (Nat.mod_modEq _ _)
  have h1 : s + p * 671914833335277
      ≡ s + s * 1439961107955227 * 671914833335277 [MOD 2^52] :=
    Nat.ModEq.add_left s (hmod.mul_right _)
  have h2 : s + s * 1439961107955227 * 671914833335277
      = s * 214835089243030 * 2^52 := by
    calc s + s * 1439961107955227 * 671914833335277
        = s * (1 + 1439961107955227 * 671914833335277) := by ring
      _ = s * (214835089243030 * 2^52) := by rw [mont_key]
      _ = s * 214835089243030 * 2^52 := by ring
  calc (s + p * 671914833335277) % 2^52
      = (s + s * 1439961107955227 * 671914833335277) % 2^52 := h1
    _ = 0 := by rw [h2]; exact Nat.mul_mod_left _ _

/-! ### The two round helpers -/

/-- **`part2` splits exactly**: carry·2^52 + w = sum, w < 2^52
    (scalar.rs:273-276 — mask and shift, nothing lost). -/
theorem part2_spec (sum : U128) :
    backend.serial.u64.scalar.Scalar52.montgomery_reduce.part2 sum
      ⦃ cw => cw.2.val < 2^52 ∧ cw.1.val * 2^52 + cw.2.val = sum.val ⦄ := by
  unfold backend.serial.u64.scalar.Scalar52.montgomery_reduce.part2
  step with UScalar.cast.step_spec as ⟨i, hi⟩
  have hiv : i.val = sum.val % 2^64 := by
    simp [hi, UScalar.cast_val_eq, U64.size, U128.size]
  step as ⟨i1, hi1⟩
  step as ⟨i2, hi2⟩
  have hi2v : i2.val = 2^52 - 1 := by
    simp [hi2, hi1, U64.size_def, U64.numBits]
  step as ⟨w, hw⟩
  have hwv : w.val = sum.val % 2^52 := by
    rw [hw, UScalar.val_and, hi2v, nat_and_mask52, hiv,
        Nat.mod_mod_of_dvd sum.val (by norm_num : (2:ℕ)^52 ∣ 2^64)]
  step as ⟨i3, hi3⟩
  have hi3v : i3.val = sum.val / 2^52 := by
    rw [hi3, Nat.shiftRight_eq_div_pow]
  try simp only [spec_ok]
  constructor
  · rw [hwv]; exact Nat.mod_lt _ (by norm_num)
  · rw [hi3v, hwv]; omega

/-- **`part1` divides exactly** (scalar.rs:268-271): the nonce digit
    p = (sum·LFACTOR) & mask52 makes sum + p·L₀ divisible by 2^52
    (`mont_cancel`), so the shifted carry satisfies the *equation*
    carry·2^52 = sum + p·L₀ — no information is discarded. The sum bound
    keeps the internal u128 addition from overflowing. -/
theorem part1_spec (sum : U128) (hs : sum.val < 2^124) :
    backend.serial.u64.scalar.Scalar52.montgomery_reduce.part1 sum
      ⦃ cw => cw.2.val < 2^52 ∧
              cw.1.val * 2^52 = sum.val + cw.2.val * 671914833335277 ⦄ := by
  unfold backend.serial.u64.scalar.Scalar52.montgomery_reduce.part1
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexUsizeU64.index
  step with UScalar.cast.step_spec as ⟨i, hi⟩
  have hiv : i.val = sum.val % 2^64 := by
    simp [hi, UScalar.cast_val_eq, U64.size, U128.size]
  step as ⟨i1, hi1⟩
  have hsz : UScalar.size UScalarTy.U64 = 2^64 := by scalar_tac
  have hi1v : i1.val = sum.val * 1439961107955227 % 2^64 := by
    rw [hi1]
    simp only [core.num.U64.wrapping_mul, UScalar.wrapping_mul_val_eq]
    rw [hiv, LFACTOR_val, hsz]
    exact Nat.mod_mul_mod ..
  step as ⟨i2, hi2⟩
  step as ⟨i3, hi3⟩
  have hi3v : i3.val = 2^52 - 1 := by
    simp [hi3, hi2, U64.size_def, U64.numBits]
  step as ⟨p, hp⟩
  have hpv : p.val = (sum.val * 1439961107955227) % 2^52 := by
    rw [hp, UScalar.val_and, hi3v, nat_and_mask52, hi1v,
        Nat.mod_mod_of_dvd _ (by norm_num : (2:ℕ)^52 ∣ 2^64)]
  have hpb : p.val < 2^52 := by rw [hpv]; exact Nat.mod_lt _ (by norm_num)
  step as ⟨i4, hi4⟩
  try simp [L_limbs] at hi4
  have hi4v : i4.val = 671914833335277 := by rw [hi4]; rfl
  step with m_spec as ⟨i5, hi5⟩
  have hi5v : i5.val = p.val * 671914833335277 := by rw [hi5, hi4v]
  have hi5b : i5.val < 2^102 := by
    rw [hi5v]
    calc p.val * 671914833335277 < 2^52 * 671914833335277 :=
          Nat.mul_lt_mul_of_lt_of_le hpb (le_refl _) (by norm_num)
      _ < 2^102 := by norm_num
  step as ⟨i6, hi6⟩
  have hi6v : i6.val = sum.val + p.val * 671914833335277 := by
    rw [hi6, hi5v]
  step as ⟨i7, hi7⟩
  have hdvd : (sum.val + p.val * 671914833335277) % 2^52 = 0 :=
    mont_cancel sum.val p.val hpv
  have hi7v : i7.val * 2^52 = sum.val + p.val * 671914833335277 := by
    rw [hi7, Nat.shiftRight_eq_div_pow, hi6v]
    omega
  try simp only [spec_ok]
  exact ⟨hpb, hi7v⟩

/-! ### The two value telescopes -/

/-- **Head telescope**: the five exact-division rounds E0–E4, weighted
    1, 2^52, …, 2^208 and summed, eliminate the carries c0–c3 and give
    the full Montgomery identity with the round-5..8 input state X′ on
    the left:  X′·2^260 = Z + N·ℓ.  One `linear_combination` certificate
    (verified numerically over random traces before formalization). -/
theorem mont_head_telescope
    (z0 z1 z2 z3 z4 z5 z6 z7 z8 n0 n1 n2 n3 n4 c0 c1 c2 c3 c4 : ℕ)
    (e0 : c0 * 2^52 = z0 + n0 * 671914833335277)
    (e1 : c1 * 2^52 = c0 + z1 + n0 * 3916664325105025 + n1 * 671914833335277)
    (e2 : c2 * 2^52 = c1 + z2 + n0 * 1367801 + n1 * 3916664325105025 + n2 * 671914833335277)
    (e3 : c3 * 2^52 = c2 + z3 + n1 * 1367801 + n2 * 3916664325105025 + n3 * 671914833335277)
    (e4 : c4 * 2^52 = c3 + z4 + n0 * 17592186044416 + n2 * 1367801 + n3 * 3916664325105025 + n4 * 671914833335277) :
    ((c4 + z5 + n1 * 17592186044416 + n3 * 1367801 + n4 * 3916664325105025) + 2^52 * (z6 + n2 * 17592186044416 + n4 * 1367801) + 2^104 * (z7 + n3 * 17592186044416) + 2^156 * (z8 + n4 * 17592186044416)) * 2^260
      = (z0 + 2^52 * z1 + 2^104 * z2 + 2^156 * z3 + 2^208 * z4 + 2^260 * z5 + 2^312 * z6 + 2^364 * z7 + 2^416 * z8)
        + (n0 + 2^52 * n1 + 2^104 * n2 + 2^156 * n3 + 2^208 * n4) * Ell := by
  unfold Ell
  linear_combination (e0 : (c0 * 2^52 : ℕ) = _) + 2^52 * e1 + 2^104 * e2
    + 2^156 * e3 + 2^208 * e4

/-- **Tail telescope**: the four exact-split rounds E5–E8, weighted
    1, 2^52, 2^104, 2^156, cancel c5–c7 and reassemble the input state:
    the result limbs plus top carry equal X′ exactly. -/
theorem mont_tail_telescope
    (z5 z6 z7 z8 n1 n2 n3 n4 c4 c5 c6 c7 c8 r0 r1 r2 r3 : ℕ)
    (e5 : c5 * 2^52 + r0 = c4 + z5 + n1 * 17592186044416 + n3 * 1367801 + n4 * 3916664325105025)
    (e6 : c6 * 2^52 + r1 = c5 + z6 + n2 * 17592186044416 + n4 * 1367801)
    (e7 : c7 * 2^52 + r2 = c6 + z7 + n3 * 17592186044416)
    (e8 : c8 * 2^52 + r3 = c7 + z8 + n4 * 17592186044416) :
    r0 + 2^52 * r1 + 2^104 * r2 + 2^156 * r3 + 2^208 * c8
      = (c4 + z5 + n1 * 17592186044416 + n3 * 1367801 + n4 * 3916664325105025) + 2^52 * (z6 + n2 * 17592186044416 + n4 * 1367801) + 2^104 * (z7 + n3 * 17592186044416) + 2^156 * (z8 + n4 * 17592186044416) := by
  linear_combination (e5 : (c5 * 2^52 + r0 : ℕ) = _) + 2^52 * e6
    + 2^104 * e7 + 2^156 * e8

/-- The standard Montgomery output bound: Z < R·ℓ and N < R force the
    pre-canonical result below 2ℓ. Atomic in `Ell` throughout. -/
theorem mont_bound (X N Z : ℕ) (hT : X * 2^260 = Z + N * Ell)
    (hZ : Z < 2^260 * Ell) (hN : N < 2^260) : X < 2 * Ell := by
  have h1 : N * Ell ≤ (2^260 - 1) * Ell :=
    Nat.mul_le_mul_right Ell (by omega)
  have h3 : 2^260 * X < 2^260 * (2 * Ell) := by
    calc 2^260 * X = X * 2^260 := Nat.mul_comm _ _
      _ = Z + N * Ell := hT
      _ ≤ Z + (2^260 - 1) * Ell := Nat.add_le_add_left h1 Z
      _ < 2^260 * Ell + (2^260 - 1) * Ell := Nat.add_lt_add_right hZ _
      _ ≤ 2^260 * (2 * Ell) := by
          have he : (2:ℕ)^260 * Ell + (2^260 - 1) * Ell
              = (2^260 + (2^260 - 1)) * Ell := by ring
          rw [he]
          have h2 : (2:ℕ)^260 + (2^260 - 1) ≤ 2^261 := by norm_num
          calc ((2:ℕ)^260 + (2^260 - 1)) * Ell ≤ 2^261 * Ell :=
                Nat.mul_le_mul_right Ell h2
            _ = 2^260 * (2 * Ell) := by ring
  exact Nat.lt_of_mul_lt_mul_left h3

/-! ### The walk, split at the round-4/round-5 boundary (METHOD 4: the
    74-step monolith exceeds the elaboration budget; each half is a
    `mul_internal`-sized walk) -/

/-- **Tail of the reduction** (rounds 5–8 + canonicalization): from the
    mid-state (carry4, n1..n4) and limbs 5..8, the four `part2` rounds
    produce limbs summing (with the top carry) to exactly the mid-state
    value X′; the trailing `sub _ L` subtracts ⟦L⟧ = 0. The hypothesis
    X′ < 2ℓ (provided by `mont_head_telescope` + `mont_bound` at the
    call site) keeps the top carry below 2^52 for the sub. -/
theorem mont_tail_spec (limbs : Std.Array Std.U128 9#usize)
    (z0 z1 z2 z3 z4 z5 z6 z7 z8 : Std.U128) (carry4 : Std.U128)
    (n1 n2 n3 n4 i3 i8 i21 : U64)
    (hl : (↑limbs : List Std.U128) = [z0, z1, z2, z3, z4, z5, z6, z7, z8])
    (hvi3 : i3.val = 3916664325105025) (hvi8 : i8.val = 1367801) (hvi21 : i21.val = 17592186044416)
    (hcb4 : carry4.val < 2^62)
    (hnb : n1.val < 2^52 ∧ n2.val < 2^52 ∧ n3.val < 2^52 ∧ n4.val < 2^52)
    (hzb : z5.val < 2^107 ∧ z6.val < 2^107 ∧ z7.val < 2^107 ∧ z8.val < 2^107)
    (hX : (carry4.val + z5.val + n1.val * 17592186044416 + n3.val * 1367801 + n4.val * 3916664325105025) + 2^52 * (z6.val + n2.val * 17592186044416 + n4.val * 1367801) + 2^104 * (z7.val + n3.val * 17592186044416) + 2^156 * (z8.val + n4.val * 17592186044416) < 2 * Ell) :
    (do
      let i28 ← Array.index_usize limbs 5#usize
      let i29 ← carry4 + i28
      let i30 ← backend.serial.u64.scalar.m n1 i21
      let i31 ← i29 + i30
      let i32 ← backend.serial.u64.scalar.m n3 i8
      let i33 ← i31 + i32
      let i34 ← backend.serial.u64.scalar.m n4 i3
      let i35 ← i33 + i34
      let (carry5, r0) ←
        backend.serial.u64.scalar.Scalar52.montgomery_reduce.part2 i35
      let i36 ← Array.index_usize limbs 6#usize
      let i37 ← carry5 + i36
      let i38 ← backend.serial.u64.scalar.m n2 i21
      let i39 ← i37 + i38
      let i40 ← backend.serial.u64.scalar.m n4 i8
      let i41 ← i39 + i40
      let (carry6, r1) ←
        backend.serial.u64.scalar.Scalar52.montgomery_reduce.part2 i41
      let i42 ← Array.index_usize limbs 7#usize
      let i43 ← carry6 + i42
      let i44 ← backend.serial.u64.scalar.m n3 i21
      let i45 ← i43 + i44
      let (carry7, r2) ←
        backend.serial.u64.scalar.Scalar52.montgomery_reduce.part2 i45
      let i46 ← Array.index_usize limbs 8#usize
      let i47 ← carry7 + i46
      let i48 ← backend.serial.u64.scalar.m n4 i21
      let i49 ← i47 + i48
      let (carry8, r3) ←
        backend.serial.u64.scalar.Scalar52.montgomery_reduce.part2 i49
      let r4 ← lift (UScalar.cast .U64 carry8)
      backend.serial.u64.scalar.Scalar52.sub
        (Array.make 5#usize [ r0, r1, r2, r3, r4 ])
        backend.serial.u64.constants.L)
      ⦃ r => (∃ s0 s1 s2 s3 s4 : U64, (↑r : List U64) = [s0, s1, s2, s3, s4] ∧
              s0.val < 2^52 ∧ s1.val < 2^52 ∧ s2.val < 2^52 ∧ s3.val < 2^52 ∧
              s4.val < 2^52) ∧
            scVal r < Ell ∧
            scDenote r = (((carry4.val + z5.val + n1.val * 17592186044416 + n3.val * 1367801 + n4.val * 3916664325105025) + 2^52 * (z6.val + n2.val * 17592186044416 + n4.val * 1367801) + 2^104 * (z7.val + n3.val * 17592186044416) + 2^156 * (z8.val + n4.val * 17592186044416) : ℕ) : ZMod Ell) ⦄ := by
  obtain ⟨hn1b, hn2b, hn3b, hn4b⟩ := hnb
  obtain ⟨hz5, hz6, hz7, hz8⟩ := hzb
  step as ⟨i28, hi28⟩
  simp [hl] at hi28
  have hvi28 : i28.val = z5.val := by rw [hi28]
  have hsi29 : carry4.val + i28.val < 2^128 := by omega
  step as ⟨i29, hi29⟩
  have hvi29 : i29.val = carry4.val + i28.val := by rw [hi29]
  have hbi29 : i29.val < 2^110 := by omega
  step with m_spec as ⟨i30, hi30⟩
  have hvi30 : i30.val = n1.val * 17592186044416 := by rw [hi30, hvi21]
  have hbi30 : i30.val < 2^104 := by rw [hvi30]; omega
  have hsi31 : i29.val + i30.val < 2^128 := by omega
  step as ⟨i31, hi31⟩
  have hvi31 : i31.val = i29.val + i30.val := by rw [hi31]
  have hbi31 : i31.val < 2^112 := by omega
  step with m_spec as ⟨i32, hi32⟩
  have hvi32 : i32.val = n3.val * 1367801 := by rw [hi32, hvi8]
  have hbi32 : i32.val < 2^104 := by rw [hvi32]; omega
  have hsi33 : i31.val + i32.val < 2^128 := by omega
  step as ⟨i33, hi33⟩
  have hvi33 : i33.val = i31.val + i32.val := by rw [hi33]
  have hbi33 : i33.val < 2^113 := by omega
  step with m_spec as ⟨i34, hi34⟩
  have hvi34 : i34.val = n4.val * 3916664325105025 := by rw [hi34, hvi3]
  have hbi34 : i34.val < 2^104 := by rw [hvi34]; omega
  have hsi35 : i33.val + i34.val < 2^128 := by omega
  step as ⟨i35, hi35⟩
  have hvi35 : i35.val = i33.val + i34.val := by rw [hi35]
  have hbi35 : i35.val < 2^114 := by omega
  step with (part2_spec i35) as ⟨carry5, r0, hr0b, hE5⟩
  rw [hvi35, hvi33, hvi31, hvi29, hvi28, hvi30, hvi32, hvi34] at hE5
  have hcb5 : carry5.val < 2^62 := by omega
  step as ⟨i36, hi36⟩
  simp [hl] at hi36
  have hvi36 : i36.val = z6.val := by rw [hi36]
  have hsi37 : carry5.val + i36.val < 2^128 := by omega
  step as ⟨i37, hi37⟩
  have hvi37 : i37.val = carry5.val + i36.val := by rw [hi37]
  have hbi37 : i37.val < 2^110 := by omega
  step with m_spec as ⟨i38, hi38⟩
  have hvi38 : i38.val = n2.val * 17592186044416 := by rw [hi38, hvi21]
  have hbi38 : i38.val < 2^104 := by rw [hvi38]; omega
  have hsi39 : i37.val + i38.val < 2^128 := by omega
  step as ⟨i39, hi39⟩
  have hvi39 : i39.val = i37.val + i38.val := by rw [hi39]
  have hbi39 : i39.val < 2^112 := by omega
  step with m_spec as ⟨i40, hi40⟩
  have hvi40 : i40.val = n4.val * 1367801 := by rw [hi40, hvi8]
  have hbi40 : i40.val < 2^104 := by rw [hvi40]; omega
  have hsi41 : i39.val + i40.val < 2^128 := by omega
  step as ⟨i41, hi41⟩
  have hvi41 : i41.val = i39.val + i40.val := by rw [hi41]
  have hbi41 : i41.val < 2^113 := by omega
  step with (part2_spec i41) as ⟨carry6, r1, hr1b, hE6⟩
  rw [hvi41, hvi39, hvi37, hvi36, hvi38, hvi40] at hE6
  have hcb6 : carry6.val < 2^62 := by omega
  step as ⟨i42, hi42⟩
  simp [hl] at hi42
  have hvi42 : i42.val = z7.val := by rw [hi42]
  have hsi43 : carry6.val + i42.val < 2^128 := by omega
  step as ⟨i43, hi43⟩
  have hvi43 : i43.val = carry6.val + i42.val := by rw [hi43]
  have hbi43 : i43.val < 2^110 := by omega
  step with m_spec as ⟨i44, hi44⟩
  have hvi44 : i44.val = n3.val * 17592186044416 := by rw [hi44, hvi21]
  have hbi44 : i44.val < 2^104 := by rw [hvi44]; omega
  have hsi45 : i43.val + i44.val < 2^128 := by omega
  step as ⟨i45, hi45⟩
  have hvi45 : i45.val = i43.val + i44.val := by rw [hi45]
  have hbi45 : i45.val < 2^112 := by omega
  step with (part2_spec i45) as ⟨carry7, r2, hr2b, hE7⟩
  rw [hvi45, hvi43, hvi42, hvi44] at hE7
  have hcb7 : carry7.val < 2^62 := by omega
  step as ⟨i46, hi46⟩
  simp [hl] at hi46
  have hvi46 : i46.val = z8.val := by rw [hi46]
  have hsi47 : carry7.val + i46.val < 2^128 := by omega
  step as ⟨i47, hi47⟩
  have hvi47 : i47.val = carry7.val + i46.val := by rw [hi47]
  have hbi47 : i47.val < 2^110 := by omega
  step with m_spec as ⟨i48, hi48⟩
  have hvi48 : i48.val = n4.val * 17592186044416 := by rw [hi48, hvi21]
  have hbi48 : i48.val < 2^104 := by rw [hvi48]; omega
  have hsi49 : i47.val + i48.val < 2^128 := by omega
  step as ⟨i49, hi49⟩
  have hvi49 : i49.val = i47.val + i48.val := by rw [hi49]
  have hbi49 : i49.val < 2^112 := by omega
  step with (part2_spec i49) as ⟨carry8, r3, hr3b, hE8⟩
  rw [hvi49, hvi47, hvi46, hvi48] at hE8

  -- reassemble the mid-state value and bound the top carry
  have hTt := mont_tail_telescope z5.val z6.val z7.val z8.val
    n1.val n2.val n3.val n4.val carry4.val carry5.val carry6.val carry7.val
    carry8.val r0.val r1.val r2.val r3.val hE5 hE6 hE7 hE8
  have hEll254 : 2 * Ell < 2^254 := by unfold Ell; norm_num
  have hc8b : carry8.val < 2^46 := by omega
  step with UScalar.cast.step_spec as ⟨r4, hr4⟩
  have hr4v : r4.val = carry8.val := by
    rw [hr4, UScalar.cast_val_eq]
    simp only [UScalarTy.U64, UScalarTy.numBits]
    omega
  have hr4b : r4.val < 2^52 := by omega

  -- canonicalize: sub _ L with ⟦L⟧ = 0
  have hmk : ((↑(Array.make 5#usize [r0, r1, r2, r3, r4])) : List U64)
      = [r0, r1, r2, r3, r4] := by simp [Array.make]
  apply spec_mono (sub_val_spec _ backend.serial.u64.constants.L
      r0 r1 r2 r3 r4 _ _ _ _ _ hmk L_limbs
      ⟨hr0b, hr1b, hr2b, hr3b, hr4b⟩
      (by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num)
      (by rw [L_val]))
  intro r hr
  obtain ⟨hbnds, ⟨β, hβle, heq, hguard⟩, hden⟩ := hr
  have hpre : scVal (Array.make 5#usize [r0, r1, r2, r3, r4])
      = scLimbs r0 r1 r2 r3 r4 := scVal_eq _ _ _ _ _ _ hmk
  have hpreX : scVal (Array.make 5#usize [r0, r1, r2, r3, r4])
      = (carry4.val + z5.val + n1.val * 17592186044416 + n3.val * 1367801
          + n4.val * 3916664325105025)
        + 2^52 * (z6.val + n2.val * 17592186044416 + n4.val * 1367801)
        + 2^104 * (z7.val + n3.val * 17592186044416)
        + 2^156 * (z8.val + n4.val * 17592186044416) := by
    rw [hpre]; unfold scLimbs; rw [hr4v]; exact hTt
  rw [L_val, hpreX] at heq
  rw [L_val, hpreX] at hguard
  refine ⟨hbnds, ?_, ?_⟩
  · -- canonicity: the sub-L canonicalization of a value below 2ℓ lands below ℓ
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hβle with h0 | h1
    · subst h0; omega
    · subst h1; have := hguard rfl; omega
  · rw [hden]
    have hEz : (Ell : ZMod Ell) = 0 := ZMod.natCast_self Ell
    have hL0 : scDenote backend.serial.u64.constants.L = 0 := by
      simp only [scDenote, L_val]; exact hEz
    rw [hL0, sub_zero]
    simp only [scDenote, hpreX]

end ScalarProofs
