/- ──────────────────────────────────────────────────────────────────────────────
   Proofs/ToBytesMath.lean — the pure ℕ mathematics of `FieldElement51::to_bytes`
   (phase 2 of the signature apex: compress semantics, brick "to_bytes canonicity").

   `to_bytes` canonicalizes a weakly-reduced field element (limbs < 2⁵¹+19·2¹³,
   hence value h < 2p) to r = h mod p and serializes r little-endian:

   1. THE q-TRICK: q := carry of h + 19 out of bit 255 = (h+19)/2²⁵⁵, computed
      limb-wise as a 5-rung carry telescope; q ∈ {0,1}, and q = 1 ↔ h ≥ p
      (h ≥ p ↔ h + 19 ≥ 2²⁵⁵).                          (q_telescope, q_facts)
   2. r = (h + 19q) mod 2²⁵⁵ = h mod p — adding 19q and discarding bit 255
      subtracts exactly pq.                                        (q_mod_p)
   3. The carry chain computing (h + 19q) mod 2²⁵⁵ limb-wise.    (carry_pack)
   4. The 32-byte little-endian packing: each limb splits into byte chunks
      (byte_split_*); their weighted sum reassembles the value. (bytes_pack)

   Everything here is context-free ℕ arithmetic (METHOD 4: heavy identities in
   isolation, applied once). The symbolic execution of the transpiled code
   lives in Proofs/ToBytesSpec.lean, which consumes exactly these lemmas.
   ────────────────────────────────────────────────────────────────────────────── -/
import Proofs.Denote
import Mathlib.Tactic.LinearCombination
open Aeneas Aeneas.Std Result

set_option maxHeartbeats 4000000

namespace CurveFieldProofs

/-- `>>>` on ℕ is division (generic-exponent companion of ReduceSpec's
    `nat_shift_div`, which is specialized to 51). -/
theorem nat_shr (n k : ℕ) : n >>> k = n / 2^k :=
  Nat.shiftRight_eq_div_pow n k

/-- One rung of a carry telescope: absorbing a floor-quotient into the next
    limb and re-dividing is one division at the combined weight. -/
theorem div_rung (a b j k : ℕ) : (a + b / 2^j) / 2^k = (a * 2^j + b) / 2^(j+k) := by
  have h1 : (a * 2^j + b) / 2^j = a + b / 2^j := by
    rw [Nat.add_comm (a * 2^j) b, Nat.add_mul_div_right _ _ (Nat.two_pow_pos j)]
    omega
  rw [← h1, Nat.div_div_eq_div_mul, ← pow_add]

/-- THE q-TELESCOPE: the limb-wise 5-rung carry computation equals one
    division of the assembled value by 2²⁵⁵. `x` is the (already offset)
    limb-0 summand — in `to_bytes`, x = m0 + 19 for the q pass and
    x = m0 + 19q for the final carry pass. -/
theorem q_telescope (x m1 m2 m3 m4 : ℕ) :
    (m4 + (m3 + (m2 + (m1 + x / 2^51) / 2^51) / 2^51) / 2^51) / 2^51
      = (x + m1 * 2^51 + m2 * 2^102 + m3 * 2^153 + m4 * 2^204) / 2^255 := by
  have h1 : (m1 + x / 2^51) / 2^51 = (m1 * 2^51 + x) / 2^102 := by
    have h := div_rung m1 x 51 51; norm_num at h; exact h
  have h2 : (m2 + (m1 * 2^51 + x) / 2^102) / 2^51
      = (m2 * 2^102 + (m1 * 2^51 + x)) / 2^153 := by
    have h := div_rung m2 (m1 * 2^51 + x) 102 51; norm_num at h; exact h
  have h3 : (m3 + (m2 * 2^102 + (m1 * 2^51 + x)) / 2^153) / 2^51
      = (m3 * 2^153 + (m2 * 2^102 + (m1 * 2^51 + x))) / 2^204 := by
    have h := div_rung m3 (m2 * 2^102 + (m1 * 2^51 + x)) 153 51; norm_num at h; exact h
  have h4 : (m4 + (m3 * 2^153 + (m2 * 2^102 + (m1 * 2^51 + x))) / 2^204) / 2^51
      = (m4 * 2^204 + (m3 * 2^153 + (m2 * 2^102 + (m1 * 2^51 + x)))) / 2^255 := by
    have h := div_rung m4 (m3 * 2^153 + (m2 * 2^102 + (m1 * 2^51 + x))) 204 51
    norm_num at h; exact h
  rw [h1, h2, h3, h4]
  congr 1
  ring

/-- The q facts: for h < 2p (p = 2²⁵⁵ − 19), the carry q = (h+19)/2²⁵⁵ is a
    bit, and it fires exactly when h is not yet canonical. -/
theorem q_facts (h : ℕ) (hh : h < 2 * P) :
    (h + 19) / 2^255 ≤ 1 ∧ ((h + 19) / 2^255 = 1 ↔ P ≤ h) := by
  unfold P at *
  constructor
  · omega
  · omega

/-- Adding 19q and discarding bit 255 computes h mod p exactly. -/
theorem q_mod_p (h : ℕ) (hh : h < 2 * P) :
    (h + 19 * ((h + 19) / 2^255)) % 2^255 = h % P := by
  have h1 : (h + 19) / 2^255 ≤ 1 := (q_facts h hh).1
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h1 with hq | hq <;>
    · rw [hq]
      unfold P at *
      omega

/-- THE CARRY-PACK ACCOUNTING: the masked limbs of the final carry pass
    assemble to the value mod 2²⁵⁵. Stated over the *quotient/remainder
    forms* the symbolic execution produces:
      t₀ = x,  t_{i+1} = m_{i+1} + t_i / 2⁵¹,  f_i = t_i mod 2⁵¹. -/
theorem carry_pack (x m1 m2 m3 m4 : ℕ) :
    (x % 2^51)
      + ((m1 + x / 2^51) % 2^51) * 2^51
      + ((m2 + (m1 + x / 2^51) / 2^51) % 2^51) * 2^102
      + ((m3 + (m2 + (m1 + x / 2^51) / 2^51) / 2^51) % 2^51) * 2^153
      + ((m4 + (m3 + (m2 + (m1 + x / 2^51) / 2^51) / 2^51) / 2^51) % 2^51) * 2^204
      = (x + m1 * 2^51 + m2 * 2^102 + m3 * 2^153 + m4 * 2^204) % 2^255 := by
  -- name the telescope stages
  set t0 := x with ht0
  set t1 := m1 + t0 / 2^51 with ht1
  set t2 := m2 + t1 / 2^51 with ht2
  set t3 := m3 + t2 / 2^51 with ht3
  set t4 := m4 + t3 / 2^51 with ht4
  -- the top carry-out equals the global quotient (the same telescope as q)
  have htop : t4 / 2^51
      = (x + m1 * 2^51 + m2 * 2^102 + m3 * 2^153 + m4 * 2^204) / 2^255 := by
    simpa [ht1, ht2, ht3, ht4] using q_telescope x m1 m2 m3 m4
  -- flat div/mod facts for each stage
  have d0 := Nat.div_add_mod t0 (2^51)
  have d1 := Nat.div_add_mod t1 (2^51)
  have d2 := Nat.div_add_mod t2 (2^51)
  have d3 := Nat.div_add_mod t3 (2^51)
  have d4 := Nat.div_add_mod t4 (2^51)
  have dT := Nat.div_add_mod
    (x + m1 * 2^51 + m2 * 2^102 + m3 * 2^153 + m4 * 2^204) (2^255)
  -- linear assembly: Σ fᵢ·2⁵¹ⁱ + 2²⁵⁵·(t4/2⁵¹) = T, then subtract via dT
  omega

/-! ### Byte-chunk splits: one per limb, offsets follow 51·j mod 8. -/

/-- Limb 0 (bit offset 0): bytes 0–5 whole, low 3 bits of byte 6. -/
theorem byte_split_0 (f : ℕ) :
    f % 2^8 + (f / 2^8 % 2^8) * 2^8 + (f / 2^16 % 2^8) * 2^16
      + (f / 2^24 % 2^8) * 2^24 + (f / 2^32 % 2^8) * 2^32
      + (f / 2^40 % 2^8) * 2^40 + (f / 2^48) * 2^48 = f := by
  have e1 : f / 2^8 / 2^8 = f / 2^16 := by rw [Nat.div_div_eq_div_mul]; norm_num
  have e2 : f / 2^16 / 2^8 = f / 2^24 := by rw [Nat.div_div_eq_div_mul]; norm_num
  have e3 : f / 2^24 / 2^8 = f / 2^32 := by rw [Nat.div_div_eq_div_mul]; norm_num
  have e4 : f / 2^32 / 2^8 = f / 2^40 := by rw [Nat.div_div_eq_div_mul]; norm_num
  have e5 : f / 2^40 / 2^8 = f / 2^48 := by rw [Nat.div_div_eq_div_mul]; norm_num
  have d0 := Nat.div_add_mod f (2^8)
  have d1 := Nat.div_add_mod (f / 2^8) (2^8)
  have d2 := Nat.div_add_mod (f / 2^16) (2^8)
  have d3 := Nat.div_add_mod (f / 2^24) (2^8)
  have d4 := Nat.div_add_mod (f / 2^32) (2^8)
  have d5 := Nat.div_add_mod (f / 2^40) (2^8)
  omega

/-- Limb 1 (bit offset 3): low 5 bits close byte 6, bytes 7–11 whole,
    low 6 bits of byte 12 take the top (f < 2⁵¹ ⇒ f/2⁴⁵ < 2⁶). -/
theorem byte_split_1 (f : ℕ) :
    f % 2^5 + (f / 2^5 % 2^8) * 2^5 + (f / 2^13 % 2^8) * 2^13
      + (f / 2^21 % 2^8) * 2^21 + (f / 2^29 % 2^8) * 2^29
      + (f / 2^37 % 2^8) * 2^37 + (f / 2^45) * 2^45 = f := by
  have e1 : f / 2^5 / 2^8 = f / 2^13 := by rw [Nat.div_div_eq_div_mul]; norm_num
  have e2 : f / 2^13 / 2^8 = f / 2^21 := by rw [Nat.div_div_eq_div_mul]; norm_num
  have e3 : f / 2^21 / 2^8 = f / 2^29 := by rw [Nat.div_div_eq_div_mul]; norm_num
  have e4 : f / 2^29 / 2^8 = f / 2^37 := by rw [Nat.div_div_eq_div_mul]; norm_num
  have e5 : f / 2^37 / 2^8 = f / 2^45 := by rw [Nat.div_div_eq_div_mul]; norm_num
  have d0 := Nat.div_add_mod f (2^5)
  have d1 := Nat.div_add_mod (f / 2^5) (2^8)
  have d2 := Nat.div_add_mod (f / 2^13) (2^8)
  have d3 := Nat.div_add_mod (f / 2^21) (2^8)
  have d4 := Nat.div_add_mod (f / 2^29) (2^8)
  have d5 := Nat.div_add_mod (f / 2^37) (2^8)
  omega

/-- Limb 2 (bit offset 6): low 2 bits close byte 12, bytes 13–18 whole,
    the single top bit lands in byte 19 (f/2⁵⁰ < 2). -/
theorem byte_split_2 (f : ℕ) :
    f % 2^2 + (f / 2^2 % 2^8) * 2^2 + (f / 2^10 % 2^8) * 2^10
      + (f / 2^18 % 2^8) * 2^18 + (f / 2^26 % 2^8) * 2^26
      + (f / 2^34 % 2^8) * 2^34 + (f / 2^42 % 2^8) * 2^42
      + (f / 2^50) * 2^50 = f := by
  have e1 : f / 2^2 / 2^8 = f / 2^10 := by rw [Nat.div_div_eq_div_mul]; norm_num
  have e2 : f / 2^10 / 2^8 = f / 2^18 := by rw [Nat.div_div_eq_div_mul]; norm_num
  have e3 : f / 2^18 / 2^8 = f / 2^26 := by rw [Nat.div_div_eq_div_mul]; norm_num
  have e4 : f / 2^26 / 2^8 = f / 2^34 := by rw [Nat.div_div_eq_div_mul]; norm_num
  have e5 : f / 2^34 / 2^8 = f / 2^42 := by rw [Nat.div_div_eq_div_mul]; norm_num
  have e6 : f / 2^42 / 2^8 = f / 2^50 := by rw [Nat.div_div_eq_div_mul]; norm_num
  have d0 := Nat.div_add_mod f (2^2)
  have d1 := Nat.div_add_mod (f / 2^2) (2^8)
  have d2 := Nat.div_add_mod (f / 2^10) (2^8)
  have d3 := Nat.div_add_mod (f / 2^18) (2^8)
  have d4 := Nat.div_add_mod (f / 2^26) (2^8)
  have d5 := Nat.div_add_mod (f / 2^34) (2^8)
  have d6 := Nat.div_add_mod (f / 2^42) (2^8)
  omega

/-- Limb 3 (bit offset 1): low 7 bits close byte 19, bytes 20–24 whole,
    low 4 bits of byte 25 take the top (f/2⁴⁷ < 2⁴). -/
theorem byte_split_3 (f : ℕ) :
    f % 2^7 + (f / 2^7 % 2^8) * 2^7 + (f / 2^15 % 2^8) * 2^15
      + (f / 2^23 % 2^8) * 2^23 + (f / 2^31 % 2^8) * 2^31
      + (f / 2^39 % 2^8) * 2^39 + (f / 2^47) * 2^47 = f := by
  have e1 : f / 2^7 / 2^8 = f / 2^15 := by rw [Nat.div_div_eq_div_mul]; norm_num
  have e2 : f / 2^15 / 2^8 = f / 2^23 := by rw [Nat.div_div_eq_div_mul]; norm_num
  have e3 : f / 2^23 / 2^8 = f / 2^31 := by rw [Nat.div_div_eq_div_mul]; norm_num
  have e4 : f / 2^31 / 2^8 = f / 2^39 := by rw [Nat.div_div_eq_div_mul]; norm_num
  have e5 : f / 2^39 / 2^8 = f / 2^47 := by rw [Nat.div_div_eq_div_mul]; norm_num
  have d0 := Nat.div_add_mod f (2^7)
  have d1 := Nat.div_add_mod (f / 2^7) (2^8)
  have d2 := Nat.div_add_mod (f / 2^15) (2^8)
  have d3 := Nat.div_add_mod (f / 2^23) (2^8)
  have d4 := Nat.div_add_mod (f / 2^31) (2^8)
  have d5 := Nat.div_add_mod (f / 2^39) (2^8)
  omega

/-- Limb 4 (bit offset 4): high 4 bits of byte 25 take the low 4 bits,
    bytes 26–31 whole (f/2⁴⁴ < 2⁷ — the canonical top byte < 2⁷). -/
theorem byte_split_4 (f : ℕ) :
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

/-- THE PACKING IDENTITY: the 32 little-endian bytes that `to_bytes` emits —
    27 plain shift-extracts plus 4 boundary bytes (each an OR of the high
    bits of one limb with the low bits of the next, already normalized to
    its additive form by the walk) — assemble to the limb value. -/
theorem bytes_pack (f0 f1 f2 f3 f4 : ℕ)
    (h0 : f0 < 2^51) (h1 : f1 < 2^51) (h2 : f2 < 2^51)
    (h3 : f3 < 2^51) (h4 : f4 < 2^51) :
    (f0 % 2^8)
      + (f0 / 2^8 % 2^8) * 2^8
      + (f0 / 2^16 % 2^8) * 2^16
      + (f0 / 2^24 % 2^8) * 2^24
      + (f0 / 2^32 % 2^8) * 2^32
      + (f0 / 2^40 % 2^8) * 2^40
      + (f0 / 2^48 + (f1 % 2^5) * 2^3) * 2^48
      + (f1 / 2^5 % 2^8) * 2^56
      + (f1 / 2^13 % 2^8) * 2^64
      + (f1 / 2^21 % 2^8) * 2^72
      + (f1 / 2^29 % 2^8) * 2^80
      + (f1 / 2^37 % 2^8) * 2^88
      + (f1 / 2^45 + (f2 % 2^2) * 2^6) * 2^96
      + (f2 / 2^2 % 2^8) * 2^104
      + (f2 / 2^10 % 2^8) * 2^112
      + (f2 / 2^18 % 2^8) * 2^120
      + (f2 / 2^26 % 2^8) * 2^128
      + (f2 / 2^34 % 2^8) * 2^136
      + (f2 / 2^42 % 2^8) * 2^144
      + (f2 / 2^50 + (f3 % 2^7) * 2^1) * 2^152
      + (f3 / 2^7 % 2^8) * 2^160
      + (f3 / 2^15 % 2^8) * 2^168
      + (f3 / 2^23 % 2^8) * 2^176
      + (f3 / 2^31 % 2^8) * 2^184
      + (f3 / 2^39 % 2^8) * 2^192
      + (f3 / 2^47 + (f4 % 2^4) * 2^4) * 2^200
      + (f4 / 2^4 % 2^8) * 2^208
      + (f4 / 2^12 % 2^8) * 2^216
      + (f4 / 2^20 % 2^8) * 2^224
      + (f4 / 2^28 % 2^8) * 2^232
      + (f4 / 2^36 % 2^8) * 2^240
      + (f4 / 2^44) * 2^248
      = f0 + f1 * 2^51 + f2 * 2^102 + f3 * 2^153 + f4 * 2^204 := by
  have s0 := byte_split_0 f0
  have s1 := byte_split_1 f1
  have s2 := byte_split_2 f2
  have s3 := byte_split_3 f3
  have s4 := byte_split_4 f4
  -- Each limb's split, scaled by its radix weight, accounts for exactly the
  -- terms above that mention it (boundary bytes contribute to two limbs).
  -- Cast to ℤ and take the weighted linear combination of the five splits.
  zify at s0 s1 s2 s3 s4 ⊢
  linear_combination s0 + 2^51 * s1 + 2^102 * s2 + 2^153 * s3 + 2^204 * s4

/-- Setting a clear top bit by XOR is addition (compress's sign-bit write). -/
theorem xor_top_bit (a : ℕ) (h : a < 2^7) : a ^^^ 2^7 = a + 2^7 := by
  have hdiv : (a ^^^ 2^7) / 2^7 = 1 := by
    rw [Nat.xor_div_two_pow]
    rw [Nat.div_eq_of_lt h]
    norm_num
  have hand := Nat.and_two_pow_sub_one_eq_mod (a ^^^ 2^7) 7
  have hdistrib := Nat.and_xor_distrib_right (a := a) (b := 2^7) (c := 2^7 - 1)
  have ha : a &&& (2^7 - 1) = a := by
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt h]
  have h2 : 2^7 &&& (2^7 - 1) = 0 := by decide
  have hmod : (a ^^^ 2^7) % 2^7 = a := by
    rw [← hand, hdistrib, ha, h2, Nat.xor_zero]
  have hdm := Nat.div_add_mod (a ^^^ 2^7) (2^7)
  omega

end CurveFieldProofs
