/- ──────────────────────────────────────────────────────────────────────────────
   Proofs/ScalarFullMulSpec.lean — Scalar52 multiplication, phase C: `mul`.

   `mul a b` composes the proven pieces (scalar.rs:302-305):
       mul_internal a b            — nine exact schoolbook columns (phase A)
       montgomery_reduce           — ⟦ab'⟧·R = a·b with R = 2^260 (phase B)
       mul_internal ab' RR         — columns against RR ≡ R² (mod ℓ)
       montgomery_reduce           — ⟦r⟧·R = ⟦ab'⟧·R²  ⟹  ⟦r⟧ = ⟦ab'⟧·R
   so ⟦r⟧·R = ⟦ab'⟧·R·R = (⟦a⟧·⟦b⟧)·R, and R = 2^260 is a unit in ZMod ℓ
   (ℓ is odd), giving  ⟦mul a b⟧ = ⟦a⟧ · ⟦b⟧.

   The first reduction carries the honest Montgomery hypothesis
   scVal a · scVal b < 2^260·ℓ (canonical inputs satisfy it: ℓ² < 2^260·ℓ);
   the second needs nothing extra because scVal RR < ℓ.
   ────────────────────────────────────────────────────────────────────────────── -/
import Proofs.ScalarReduceSpec
open Aeneas Aeneas.Std Result
open curve25519

set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 600

namespace ScalarProofs

open Aeneas.Std.WP

/-! ### The RR constant: RR ≡ R² = 2^520 (mod ℓ) -/

/-- The transpiled `constants::RR` as a limb list. -/
theorem RR_limbs :
    (↑backend.serial.u64.constants.RR : List U64) =
      [2764609938444603#u64, 3768881411696287#u64, 1616719297148420#u64,
       1087343033131391#u64, 10175238647962#u64] := by
  unfold backend.serial.u64.constants.RR
  rfl

/-- The value of the transpiled RR constant. -/
theorem RR_scVal : scVal backend.serial.u64.constants.RR
    = 4185850391763183796333492317919282507600454137915443218209456916606550724923 := by
  rw [scVal_eq _ _ _ _ _ _ RR_limbs]
  unfold scLimbs
  norm_num

/-- RR is canonical (below ℓ). -/
theorem RR_lt : scVal backend.serial.u64.constants.RR < Ell := by
  rw [RR_scVal]; unfold Ell; norm_num

/-- **RR denotes R² = 2^520 in ZMod ℓ** — the exact division witness
    2^520 = RR + K·ℓ is kernel-checked literal arithmetic. -/
theorem RR_denote :
    ((4185850391763183796333492317919282507600454137915443218209456916606550724923 : ℕ)
      : ZMod Ell) = 2^520 := by
  have h : (2:ℕ)^520
      = 4185850391763183796333492317919282507600454137915443218209456916606550724923
        + 474284397516047136454946754595585670565175736652605875744292671501348828217547577
          * Ell := by
    unfold Ell; norm_num
  have hc := congrArg (Nat.cast (R := ZMod Ell)) h
  push_cast at hc
  -- push_cast evaluates 2^520 to its literal and kills the ↑Ell factor:
  -- hc : (2^520-literal : ZMod Ell) = RR + K·0
  have h2 : ((2:ZMod Ell))^520
      = (3432398830065304857490950399540696608634717650071652704697231729592771591698828026061279820330727277488648155695740429018560993999858321906287014145557528576 : ZMod Ell) := by norm_num
  rw [h2]
  push_cast
  rw [hc, ZMod.natCast_self Ell]
  ring

/-- 2^260 is a unit in ZMod ℓ (ℓ is odd). -/
theorem R_isUnit : IsUnit ((2 : ZMod Ell)^260) := by
  have hcop : Nat.Coprime 2 Ell := by
    unfold Ell
    norm_num
    exact ⟨3618502788666131106986593281521497120428558179689953803000975469142727125494,
           by norm_num⟩
  have h2 : IsUnit ((2 : ℕ) : ZMod Ell) := (ZMod.isUnit_iff_coprime 2 Ell).mpr hcop
  have h2' : IsUnit (2 : ZMod Ell) := by simpa using h2
  exact h2'.pow 260

/-- 52-bit product bound (both factors 52-bit). -/
theorem col_bound {x y : ℕ} (hx : x < 2^52) (hy : y < 2^52) : x * y < 2^104 := by
  have h := Nat.mul_lt_mul'' hx hy
  omega

/-! ### The full multiplication -/

/-- **Scalar multiplication is correct mod ℓ.** For limb-bounded inputs
    under the Montgomery hypothesis scVal a · scVal b < 2^260·ℓ (canonical
    inputs always satisfy it), the transpiled `Scalar52::mul` denotes
    ⟦a⟧·⟦b⟧ in ZMod ℓ, with a 52-bit-bounded limb representation. -/
theorem mul_spec (a b : Sc)
    (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : U64)
    (ha : (↑a : List U64) = [a0, a1, a2, a3, a4])
    (hb : (↑b : List U64) = [b0, b1, b2, b3, b4])
    (hab : a0.val < 2^52 ∧ a1.val < 2^52 ∧ a2.val < 2^52 ∧ a3.val < 2^52 ∧ a4.val < 2^52)
    (hbb : b0.val < 2^52 ∧ b1.val < 2^52 ∧ b2.val < 2^52 ∧ b3.val < 2^52 ∧ b4.val < 2^52)
    (hcab : scVal a * scVal b < 2^260 * Ell) :
    backend.serial.u64.scalar.Scalar52.mul a b
      ⦃ r => (∃ s0 s1 s2 s3 s4 : U64, (↑r : List U64) = [s0, s1, s2, s3, s4] ∧
              s0.val < 2^52 ∧ s1.val < 2^52 ∧ s2.val < 2^52 ∧ s3.val < 2^52 ∧
              s4.val < 2^52) ∧
            scDenote r = scDenote a * scDenote b ⦄ := by
  obtain ⟨hA0, hA1, hA2, hA3, hA4⟩ := hab
  obtain ⟨hB0, hB1, hB2, hB3, hB4⟩ := hbb
  unfold backend.serial.u64.scalar.Scalar52.mul
  -- ── columns of a·b ──
  apply spec_bind (mul_internal_spec a b a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 ha hb
      ⟨hA0, hA1, hA2, hA3, hA4, hB0, hB1, hB2, hB3, hB4⟩)
  rintro zz ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, hzl,
    hz0e, hz1e, hz2e, hz3e, hz4e, hz5e, hz6e, hz7e, hz8e⟩
  show (do
    let ab ← backend.serial.u64.scalar.Scalar52.montgomery_reduce zz
    let a2 ← backend.serial.u64.scalar.Scalar52.mul_internal ab
      backend.serial.u64.constants.RR
    backend.serial.u64.scalar.Scalar52.montgomery_reduce a2)
    ⦃ r => (∃ s0 s1 s2 s3 s4 : U64, (↑r : List U64) = [s0, s1, s2, s3, s4] ∧
            s0.val < 2^52 ∧ s1.val < 2^52 ∧ s2.val < 2^52 ∧ s3.val < 2^52 ∧
            s4.val < 2^52) ∧
          scDenote r = scDenote a * scDenote b ⦄
  -- column bounds and the column value identity
  have hzb0 : z0.val < 2^107 := by
    have := col_bound hA0 hB0; omega
  have hzb1 : z1.val < 2^107 := by
    have := col_bound hA0 hB1; have := col_bound hA1 hB0; omega
  have hzb2 : z2.val < 2^107 := by
    have := col_bound hA0 hB2; have := col_bound hA1 hB1
    have := col_bound hA2 hB0; omega
  have hzb3 : z3.val < 2^107 := by
    have := col_bound hA0 hB3; have := col_bound hA1 hB2
    have := col_bound hA2 hB1; have := col_bound hA3 hB0; omega
  have hzb4 : z4.val < 2^107 := by
    have := col_bound hA0 hB4; have := col_bound hA1 hB3
    have := col_bound hA2 hB2; have := col_bound hA3 hB1
    have := col_bound hA4 hB0; omega
  have hzb5 : z5.val < 2^107 := by
    have := col_bound hA1 hB4; have := col_bound hA2 hB3
    have := col_bound hA3 hB2; have := col_bound hA4 hB1; omega
  have hzb6 : z6.val < 2^107 := by
    have := col_bound hA2 hB4; have := col_bound hA3 hB3
    have := col_bound hA4 hB2; omega
  have hzb7 : z7.val < 2^107 := by
    have := col_bound hA3 hB4; have := col_bound hA4 hB3; omega
  have hzb8 : z8.val < 2^107 := by
    have := col_bound hA4 hB4; omega
  have hZval : z0.val + 2^52 * z1.val + 2^104 * z2.val + 2^156 * z3.val
      + 2^208 * z4.val + 2^260 * z5.val + 2^312 * z6.val + 2^364 * z7.val
      + 2^416 * z8.val = scVal a * scVal b := by
    rw [hz0e, hz1e, hz2e, hz3e, hz4e, hz5e, hz6e, hz7e, hz8e,
        scVal_eq a a0 a1 a2 a3 a4 ha, scVal_eq b b0 b1 b2 b3 b4 hb]
    unfold scLimbs
    ring
  have hZlt : z0.val + 2^52 * z1.val + 2^104 * z2.val + 2^156 * z3.val
      + 2^208 * z4.val + 2^260 * z5.val + 2^312 * z6.val + 2^364 * z7.val
      + 2^416 * z8.val < 2^260 * Ell := by rw [hZval]; exact hcab
  -- ── first reduction: ⟦ab'⟧·R = a·b ──
  apply spec_bind (montgomery_reduce_spec zz z0 z1 z2 z3 z4 z5 z6 z7 z8 hzl
      ⟨hzb0, hzb1, hzb2, hzb3, hzb4, hzb5, hzb6, hzb7, hzb8⟩ hZlt)
  rintro ab ⟨⟨ab0, ab1, ab2, ab3, ab4, habl, hab0, hab1, hab2, hab3, hab4⟩, habd⟩
  show (do
    let a2 ← backend.serial.u64.scalar.Scalar52.mul_internal ab
      backend.serial.u64.constants.RR
    backend.serial.u64.scalar.Scalar52.montgomery_reduce a2)
    ⦃ r => (∃ s0 s1 s2 s3 s4 : U64, (↑r : List U64) = [s0, s1, s2, s3, s4] ∧
            s0.val < 2^52 ∧ s1.val < 2^52 ∧ s2.val < 2^52 ∧ s3.val < 2^52 ∧
            s4.val < 2^52) ∧
          scDenote r = scDenote a * scDenote b ⦄
  -- RR limb values
  have hR0 : (2764609938444603#u64).val = 2764609938444603 := by rfl
  have hR1 : (3768881411696287#u64).val = 3768881411696287 := by rfl
  have hR2 : (1616719297148420#u64).val = 1616719297148420 := by rfl
  have hR3 : (1087343033131391#u64).val = 1087343033131391 := by rfl
  have hR4 : (10175238647962#u64).val = 10175238647962 := by rfl
  -- ── columns of ab'·RR ──
  apply spec_bind (mul_internal_spec ab backend.serial.u64.constants.RR
      ab0 ab1 ab2 ab3 ab4
      (2764609938444603#u64) (3768881411696287#u64) (1616719297148420#u64)
      (1087343033131391#u64) (10175238647962#u64)
      habl RR_limbs
      ⟨hab0, hab1, hab2, hab3, hab4,
       by rw [hR0]; norm_num, by rw [hR1]; norm_num, by rw [hR2]; norm_num,
       by rw [hR3]; norm_num, by rw [hR4]; norm_num⟩)
  rintro ww ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, hwl,
    hw0e, hw1e, hw2e, hw3e, hw4e, hw5e, hw6e, hw7e, hw8e⟩
  show backend.serial.u64.scalar.Scalar52.montgomery_reduce ww
    ⦃ r => (∃ s0 s1 s2 s3 s4 : U64, (↑r : List U64) = [s0, s1, s2, s3, s4] ∧
            s0.val < 2^52 ∧ s1.val < 2^52 ∧ s2.val < 2^52 ∧ s3.val < 2^52 ∧
            s4.val < 2^52) ∧
          scDenote r = scDenote a * scDenote b ⦄
  simp only [hR0, hR1, hR2, hR3, hR4] at hw0e hw1e hw2e hw3e hw4e hw5e hw6e hw7e hw8e
  -- column bounds (RR limbs are literals below 2^52: linear, omega-cheap)
  have hwb0 : w0.val < 2^107 := by omega
  have hwb1 : w1.val < 2^107 := by omega
  have hwb2 : w2.val < 2^107 := by omega
  have hwb3 : w3.val < 2^107 := by omega
  have hwb4 : w4.val < 2^107 := by omega
  have hwb5 : w5.val < 2^107 := by omega
  have hwb6 : w6.val < 2^107 := by omega
  have hwb7 : w7.val < 2^107 := by omega
  have hwb8 : w8.val < 2^107 := by omega
  have hsvab : scVal ab = scLimbs ab0 ab1 ab2 ab3 ab4 :=
    scVal_eq ab ab0 ab1 ab2 ab3 ab4 habl
  have hWval : w0.val + 2^52 * w1.val + 2^104 * w2.val + 2^156 * w3.val
      + 2^208 * w4.val + 2^260 * w5.val + 2^312 * w6.val + 2^364 * w7.val
      + 2^416 * w8.val
      = scVal ab
        * 4185850391763183796333492317919282507600454137915443218209456916606550724923 := by
    rw [hw0e, hw1e, hw2e, hw3e, hw4e, hw5e, hw6e, hw7e, hw8e, hsvab]
    unfold scLimbs
    ring
  have hablt : scVal ab < 2^260 := by
    rw [hsvab]; unfold scLimbs; omega
  have hWlt : w0.val + 2^52 * w1.val + 2^104 * w2.val + 2^156 * w3.val
      + 2^208 * w4.val + 2^260 * w5.val + 2^312 * w6.val + 2^364 * w7.val
      + 2^416 * w8.val < 2^260 * Ell := by
    rw [hWval]
    have hRRE :
        (4185850391763183796333492317919282507600454137915443218209456916606550724923 : ℕ)
          < Ell := by unfold Ell; norm_num
    exact Nat.mul_lt_mul'' hablt hRRE
  -- ── second reduction and the R-cancellation ──
  apply spec_mono (montgomery_reduce_spec ww w0 w1 w2 w3 w4 w5 w6 w7 w8 hwl
      ⟨hwb0, hwb1, hwb2, hwb3, hwb4, hwb5, hwb6, hwb7, hwb8⟩ hWlt)
  intro r hr
  refine ⟨hr.1, ?_⟩
  have hcW := congrArg (Nat.cast (R := ZMod Ell)) hWval
  push_cast at hcW
  have hcZ := congrArg (Nat.cast (R := ZMod Ell)) hZval
  push_cast at hcZ
  have hr2 := hr.2
  push_cast at hr2
  have habd2 := habd
  push_cast at habd2
  refine R_isUnit.mul_right_cancel ?_
  calc scDenote r * 2^260 = ((scVal ab : ℕ) : ZMod Ell)
          * ((4185850391763183796333492317919282507600454137915443218209456916606550724923 : ℕ)
              : ZMod Ell) := by
        rw [hr2]; push_cast; linear_combination hcW
    _ = ((scVal ab : ℕ) : ZMod Ell) * 2^520 := by rw [RR_denote]
    _ = (((scVal ab : ℕ) : ZMod Ell) * 2^260) * 2^260 := by ring
    _ = (((scVal a : ℕ) : ZMod Ell) * ((scVal b : ℕ) : ZMod Ell)) * 2^260 := by
        have hd : ((scVal ab : ℕ) : ZMod Ell) * 2^260
            = ((scVal a : ℕ) : ZMod Ell) * ((scVal b : ℕ) : ZMod Ell) := by
          simp only [scDenote] at habd2
          rw [habd2]; linear_combination hcZ
        rw [hd]
    _ = (scDenote a * scDenote b) * 2^260 := by simp only [scDenote]

end ScalarProofs
