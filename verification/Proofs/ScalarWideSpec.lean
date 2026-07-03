/- ──────────────────────────────────────────────────────────────────────────────
   Proofs/ScalarWideSpec.lean — toward the signature layer: hash-to-scalar.

   `Scalar::from_hash` reduces the 512-bit SHA-512 output to a scalar via
   `Scalar52::from_bytes_wide` (scalar.rs:89-116):
       words ← 64 bytes, little-endian, 8×u64
       lo, hi ← 5×52-bit limbs each (lo + 2^260·hi = the 512-bit value)
       lo' = montgomery_mul(lo, R)    -- ⟦lo'⟧ = ⟦lo⟧      (·R·R⁻¹)
       hi' = montgomery_mul(hi, RR)   -- ⟦hi'⟧ = ⟦hi⟧·2^260 (·R²·R⁻¹)
       add(hi', lo')                  -- ⟦result⟧ = the value mod ℓ

   This file provides the R constant lemmas (R ≡ 2^260 (mod ℓ), witness
   2^260 = R + 255·ℓ) and `montgomery_mul_spec`, the single Montgomery
   round: ⟦montgomery_mul a b⟧·2^260 = ⟦a⟧·⟦b⟧ with canonical bounded
   output — the composition of the proven `mul_internal_spec` and
   `montgomery_reduce_spec`, exactly the first half of `mul_spec`.

   The unpack walk (`from_bytes_wide` itself) builds on these next.
   ────────────────────────────────────────────────────────────────────────────── -/
import Proofs.ScalarFullMulSpec
open Aeneas Aeneas.Std Result
open curve25519

set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 600

namespace ScalarProofs

open Aeneas.Std.WP

/-! ### The R constant: R ≡ 2^260 (mod ℓ) -/

/-- The transpiled `constants::R` as a limb list. -/
theorem R_limbs :
    (↑backend.serial.u64.constants.R : List U64) =
      [4302102966953709#u64, 1049714374468698#u64, 4503599278581019#u64,
       4503599627370495#u64, 17592186044415#u64] := by
  unfold backend.serial.u64.constants.R
  rfl

/-- The value of the transpiled R constant. -/
theorem R_scVal : scVal backend.serial.u64.constants.R
    = 7237005577332262213973186563042994233755083008372585100823854863819240236781 := by
  rw [scVal_eq _ _ _ _ _ _ R_limbs]
  unfold scLimbs
  norm_num

/-- R is canonical (below ℓ). -/
theorem R_lt : scVal backend.serial.u64.constants.R < Ell := by
  rw [R_scVal]; unfold Ell; norm_num

/-- R's limbs are 52-bit bounded. -/
theorem R_bnd : ScBnd backend.serial.u64.constants.R := by
  refine ⟨_, _, _, _, _, R_limbs, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

/-- **R denotes 2^260 in ZMod ℓ** — witness 2^260 = R + 255·ℓ,
    kernel-checked literal arithmetic. -/
theorem R_denote :
    ((7237005577332262213973186563042994233755083008372585100823854863819240236781 : ℕ)
      : ZMod Ell) = 2^260 := by
  have h : (2:ℕ)^260
      = 7237005577332262213973186563042994233755083008372585100823854863819240236781
        + 255 * Ell := by
    unfold Ell; norm_num
  have hc := congrArg (Nat.cast (R := ZMod Ell)) h
  push_cast at hc
  have h2 : ((2:ZMod Ell))^260
      = (1852673427797059126777135760139006525652319754650249024631321344126610074238976 : ZMod Ell) := by
    norm_num
  rw [h2]
  push_cast
  rw [hc, ZMod.natCast_self Ell]
  ring

/-! ### The single Montgomery round -/

/-- **One Montgomery multiplication round**: for limb-bounded inputs under
    the Montgomery bound, `montgomery_mul a b` returns a canonical,
    bounded r with  ⟦r⟧·2^260 = ⟦a⟧·⟦b⟧  in ZMod ℓ. This is the first
    half of the proven `mul_spec`, exposed as its own certificate because
    `from_bytes_wide` uses single rounds against R and RR. -/
theorem montgomery_mul_spec (a b : Sc)
    (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : U64)
    (ha : (↑a : List U64) = [a0, a1, a2, a3, a4])
    (hb : (↑b : List U64) = [b0, b1, b2, b3, b4])
    (hab : a0.val < 2^52 ∧ a1.val < 2^52 ∧ a2.val < 2^52 ∧ a3.val < 2^52 ∧ a4.val < 2^52)
    (hbb : b0.val < 2^52 ∧ b1.val < 2^52 ∧ b2.val < 2^52 ∧ b3.val < 2^52 ∧ b4.val < 2^52)
    (hcab : scVal a * scVal b < 2^260 * Ell) :
    backend.serial.u64.scalar.Scalar52.montgomery_mul a b
      ⦃ r => (∃ s0 s1 s2 s3 s4 : U64, (↑r : List U64) = [s0, s1, s2, s3, s4] ∧
              s0.val < 2^52 ∧ s1.val < 2^52 ∧ s2.val < 2^52 ∧ s3.val < 2^52 ∧
              s4.val < 2^52) ∧
            scVal r < Ell ∧
            scDenote r * 2^260 = scDenote a * scDenote b ⦄ := by
  obtain ⟨hA0, hA1, hA2, hA3, hA4⟩ := hab
  obtain ⟨hB0, hB1, hB2, hB3, hB4⟩ := hbb
  unfold backend.serial.u64.scalar.Scalar52.montgomery_mul
  apply spec_bind (mul_internal_spec a b a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 ha hb
      ⟨hA0, hA1, hA2, hA3, hA4, hB0, hB1, hB2, hB3, hB4⟩)
  rintro zz ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, hzl,
    hz0e, hz1e, hz2e, hz3e, hz4e, hz5e, hz6e, hz7e, hz8e⟩
  show backend.serial.u64.scalar.Scalar52.montgomery_reduce zz
    ⦃ r => (∃ s0 s1 s2 s3 s4 : U64, (↑r : List U64) = [s0, s1, s2, s3, s4] ∧
            s0.val < 2^52 ∧ s1.val < 2^52 ∧ s2.val < 2^52 ∧ s3.val < 2^52 ∧
            s4.val < 2^52) ∧
          scVal r < Ell ∧
          scDenote r * 2^260 = scDenote a * scDenote b ⦄
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
  apply spec_mono (montgomery_reduce_spec zz z0 z1 z2 z3 z4 z5 z6 z7 z8 hzl
      ⟨hzb0, hzb1, hzb2, hzb3, hzb4, hzb5, hzb6, hzb7, hzb8⟩ hZlt)
  intro r hr
  refine ⟨hr.1, hr.2.1, ?_⟩
  have hc := congrArg (Nat.cast (R := ZMod Ell)) hZval
  push_cast at hc
  have hr2 := hr.2.2
  push_cast at hr2
  rw [hr2]
  simp only [scDenote]
  push_cast
  linear_combination hc

end ScalarProofs
