/- ──────────────────────────────────────────────────────────────────────────────
   Proofs/ScalarReduceSpec.lean — Scalar52 Montgomery reduction, the main walk.

   Rounds 0–4 of `montgomery_reduce` (the five exact-division `part1` rounds),
   composed with `mont_tail_spec` (rounds 5–8 + the `sub _ L`
   canonicalization) from ScalarMontSpec. Split across two files because the
   74-step monolith exceeds a single declaration's elaboration budget
   (METHOD 4); each half is a `mul_internal`-sized walk.
   ────────────────────────────────────────────────────────────────────────────── -/
import Proofs.ScalarMontSpec
open Aeneas Aeneas.Std Result
open curve25519

set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 600

namespace ScalarProofs

open Aeneas.Std.WP

/-- The nonce value N = Σ n_k·2^52k of five 52-bit digits stays below R.
    Standalone so its `omega` sees exactly five hypotheses — inside the
    walk, the same goal drags ~110 hypotheses (five round equations with
    2^102-scale coefficients included) into one Presburger instance and
    never returns (measured: the single spiralling line of the file). -/
theorem nonce_sum_bound {n0 n1 n2 n3 n4 : ℕ} (h0 : n0 < 2^52) (h1 : n1 < 2^52)
    (h2 : n2 < 2^52) (h3 : n3 < 2^52) (h4 : n4 < 2^52) :
    n0 + 2^52 * n1 + 2^104 * n2 + 2^156 * n3 + 2^208 * n4 < 2^260 := by
  omega

/-- **Montgomery reduction is exact division by R = 2^260 mod ℓ.** For a
    9-limb double-width input Z = Σ z_k·2^52k with column-bounded limbs
    (z_k < 2^107, what `mul_internal` produces) and the standard
    Montgomery hypothesis Z < 2^260·ℓ, the transpiled `montgomery_reduce`
    returns a 52-bit-bounded scalar r with  ⟦r⟧·2^260 = Z  in ZMod ℓ.
    Rounds 0–4 walk `part1_spec` here; rounds 5–8 and the `sub _ L`
    canonicalization are `mont_tail_spec`; the value accounting is
    `mont_head_telescope` + `mont_bound`. -/
theorem montgomery_reduce_spec (limbs : Std.Array Std.U128 9#usize)
    (z0 z1 z2 z3 z4 z5 z6 z7 z8 : Std.U128)
    (hl : (↑limbs : List Std.U128) = [z0, z1, z2, z3, z4, z5, z6, z7, z8])
    (hzb : z0.val < 2^107 ∧ z1.val < 2^107 ∧ z2.val < 2^107 ∧ z3.val < 2^107 ∧
           z4.val < 2^107 ∧ z5.val < 2^107 ∧ z6.val < 2^107 ∧ z7.val < 2^107 ∧
           z8.val < 2^107)
    (hZ : z0.val + 2^52 * z1.val + 2^104 * z2.val + 2^156 * z3.val + 2^208 * z4.val + 2^260 * z5.val + 2^312 * z6.val + 2^364 * z7.val + 2^416 * z8.val < 2^260 * Ell) :
    backend.serial.u64.scalar.Scalar52.montgomery_reduce limbs
      ⦃ r => (∃ s0 s1 s2 s3 s4 : U64, (↑r : List U64) = [s0, s1, s2, s3, s4] ∧
              s0.val < 2^52 ∧ s1.val < 2^52 ∧ s2.val < 2^52 ∧ s3.val < 2^52 ∧
              s4.val < 2^52) ∧
            scVal r < Ell ∧
            scDenote r * 2^260 = ((z0.val + 2^52 * z1.val + 2^104 * z2.val + 2^156 * z3.val + 2^208 * z4.val + 2^260 * z5.val + 2^312 * z6.val + 2^364 * z7.val + 2^416 * z8.val : ℕ) : ZMod Ell) ⦄ := by
  obtain ⟨hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8⟩ := hzb
  -- Hide the Montgomery bound behind an existential for the duration of
  -- the walk: a bare 2^416-coefficient inequality in the local context
  -- sends every step's side-condition automation into the huge literals
  -- (measured: the walk never finishes). It re-enters only for mont_bound.
  replace hZ : ∃ B : ℕ,
      (z0.val + 2^52 * z1.val + 2^104 * z2.val + 2^156 * z3.val
        + 2^208 * z4.val + 2^260 * z5.val + 2^312 * z6.val + 2^364 * z7.val
        + 2^416 * z8.val < B) ∧ B = 2^260 * Ell := ⟨_, hZ, rfl⟩
  unfold backend.serial.u64.scalar.Scalar52.montgomery_reduce
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexUsizeU64.index
  step as ⟨i, hi⟩
  simp [hl] at hi
  have hvi : i.val = z0.val := by rw [hi]
  have hbi : i.val < 2^124 := by clear hZ; omega
  step with (part1_spec i hbi) as ⟨carry, n0, hn0b, hE0⟩
  rw [hvi] at hE0
  have hcb0 : carry.val < 2^60 := by clear hZ; omega
  step as ⟨i1, hi1⟩
  simp [hl] at hi1
  have hvi1 : i1.val = z1.val := by rw [hi1]
  have hsi2 : carry.val + i1.val < 2^128 := by clear hZ; omega
  step as ⟨i2, hi2⟩
  have hvi2 : i2.val = carry.val + i1.val := by rw [hi2]
  have hbi2 : i2.val < 2^110 := by clear hZ; omega
  step as ⟨i3, hi3⟩
  try simp [L_limbs] at hi3
  have hvi3 : i3.val = 3916664325105025 := by rw [hi3]; rfl
  step with m_spec as ⟨i4, hi4⟩
  have hvi4 : i4.val = n0.val * 3916664325105025 := by rw [hi4, hvi3]
  have hbi4 : i4.val < 2^104 := by clear hZ; rw [hvi4]; omega
  have hsi5 : i2.val + i4.val < 2^128 := by clear hZ; omega
  step as ⟨i5, hi5⟩
  have hvi5 : i5.val = i2.val + i4.val := by rw [hi5]
  have hbi5 : i5.val < 2^112 := by clear hZ; omega
  have hbp1 : i5.val < 2^124 := by clear hZ; omega
  step with (part1_spec i5 hbp1) as ⟨carry1, n1, hn1b, hE1⟩
  rw [hvi5, hvi2, hvi1, hvi4] at hE1
  have hcb1 : carry1.val < 2^60 := by clear hZ; omega
  step as ⟨i6, hi6⟩
  simp [hl] at hi6
  have hvi6 : i6.val = z2.val := by rw [hi6]
  have hsi7 : carry1.val + i6.val < 2^128 := by clear hZ; omega
  step as ⟨i7, hi7⟩
  have hvi7 : i7.val = carry1.val + i6.val := by rw [hi7]
  have hbi7 : i7.val < 2^110 := by clear hZ; omega
  step as ⟨i8, hi8⟩
  try simp [L_limbs] at hi8
  have hvi8 : i8.val = 1367801 := by rw [hi8]; rfl
  step with m_spec as ⟨i9, hi9⟩
  have hvi9 : i9.val = n0.val * 1367801 := by rw [hi9, hvi8]
  have hbi9 : i9.val < 2^104 := by clear hZ; rw [hvi9]; omega
  have hsi10 : i7.val + i9.val < 2^128 := by clear hZ; omega
  step as ⟨i10, hi10⟩
  have hvi10 : i10.val = i7.val + i9.val := by rw [hi10]
  have hbi10 : i10.val < 2^112 := by clear hZ; omega
  step with m_spec as ⟨i11, hi11⟩
  have hvi11 : i11.val = n1.val * 3916664325105025 := by rw [hi11, hvi3]
  have hbi11 : i11.val < 2^104 := by clear hZ; rw [hvi11]; omega
  have hsi12 : i10.val + i11.val < 2^128 := by clear hZ; omega
  step as ⟨i12, hi12⟩
  have hvi12 : i12.val = i10.val + i11.val := by rw [hi12]
  have hbi12 : i12.val < 2^113 := by clear hZ; omega
  have hbp2 : i12.val < 2^124 := by clear hZ; omega
  step with (part1_spec i12 hbp2) as ⟨carry2, n2, hn2b, hE2⟩
  rw [hvi12, hvi10, hvi7, hvi6, hvi9, hvi11] at hE2
  have hcb2 : carry2.val < 2^62 := by clear hZ; omega
  step as ⟨i13, hi13⟩
  simp [hl] at hi13
  have hvi13 : i13.val = z3.val := by rw [hi13]
  have hsi14 : carry2.val + i13.val < 2^128 := by clear hZ; omega
  step as ⟨i14, hi14⟩
  have hvi14 : i14.val = carry2.val + i13.val := by rw [hi14]
  have hbi14 : i14.val < 2^110 := by clear hZ; omega
  step with m_spec as ⟨i15, hi15⟩
  have hvi15 : i15.val = n1.val * 1367801 := by rw [hi15, hvi8]
  have hbi15 : i15.val < 2^104 := by clear hZ; rw [hvi15]; omega
  have hsi16 : i14.val + i15.val < 2^128 := by clear hZ; omega
  step as ⟨i16, hi16⟩
  have hvi16 : i16.val = i14.val + i15.val := by rw [hi16]
  have hbi16 : i16.val < 2^112 := by clear hZ; omega
  step with m_spec as ⟨i17, hi17⟩
  have hvi17 : i17.val = n2.val * 3916664325105025 := by rw [hi17, hvi3]
  have hbi17 : i17.val < 2^104 := by clear hZ; rw [hvi17]; omega
  have hsi18 : i16.val + i17.val < 2^128 := by clear hZ; omega
  step as ⟨i18, hi18⟩
  have hvi18 : i18.val = i16.val + i17.val := by rw [hi18]
  have hbi18 : i18.val < 2^113 := by clear hZ; omega
  have hbp3 : i18.val < 2^124 := by clear hZ; omega
  step with (part1_spec i18 hbp3) as ⟨carry3, n3, hn3b, hE3⟩
  rw [hvi18, hvi16, hvi14, hvi13, hvi15, hvi17] at hE3
  have hcb3 : carry3.val < 2^62 := by clear hZ; omega
  step as ⟨i19, hi19⟩
  simp [hl] at hi19
  have hvi19 : i19.val = z4.val := by rw [hi19]
  have hsi20 : carry3.val + i19.val < 2^128 := by clear hZ; omega
  step as ⟨i20, hi20⟩
  have hvi20 : i20.val = carry3.val + i19.val := by rw [hi20]
  have hbi20 : i20.val < 2^110 := by clear hZ; omega
  step as ⟨i21, hi21⟩
  try simp [L_limbs] at hi21
  have hvi21 : i21.val = 17592186044416 := by rw [hi21]; rfl
  step with m_spec as ⟨i22, hi22⟩
  have hvi22 : i22.val = n0.val * 17592186044416 := by rw [hi22, hvi21]
  have hbi22 : i22.val < 2^104 := by clear hZ; rw [hvi22]; omega
  have hsi23 : i20.val + i22.val < 2^128 := by clear hZ; omega
  step as ⟨i23, hi23⟩
  have hvi23 : i23.val = i20.val + i22.val := by rw [hi23]
  have hbi23 : i23.val < 2^112 := by clear hZ; omega
  step with m_spec as ⟨i24, hi24⟩
  have hvi24 : i24.val = n2.val * 1367801 := by rw [hi24, hvi8]
  have hbi24 : i24.val < 2^104 := by clear hZ; rw [hvi24]; omega
  have hsi25 : i23.val + i24.val < 2^128 := by clear hZ; omega
  step as ⟨i25, hi25⟩
  have hvi25 : i25.val = i23.val + i24.val := by rw [hi25]
  have hbi25 : i25.val < 2^113 := by clear hZ; omega
  step with m_spec as ⟨i26, hi26⟩
  have hvi26 : i26.val = n3.val * 3916664325105025 := by rw [hi26, hvi3]
  have hbi26 : i26.val < 2^104 := by clear hZ; rw [hvi26]; omega
  have hsi27 : i25.val + i26.val < 2^128 := by clear hZ; omega
  step as ⟨i27, hi27⟩
  have hvi27 : i27.val = i25.val + i26.val := by rw [hi27]
  have hbi27 : i27.val < 2^114 := by clear hZ; omega
  have hbp4 : i27.val < 2^124 := by clear hZ; omega
  step with (part1_spec i27 hbp4) as ⟨carry4, n4, hn4b, hE4⟩
  rw [hvi27, hvi25, hvi23, hvi20, hvi19, hvi22, hvi24, hvi26] at hE4
  have hcb4 : carry4.val < 2^62 := by clear hZ; omega

  -- the head telescope gives X′·2^260 = Z + N·ℓ; mont_bound gives X′ < 2ℓ
  have hHT := mont_head_telescope z0.val z1.val z2.val z3.val z4.val z5.val
    z6.val z7.val z8.val n0.val n1.val n2.val n3.val n4.val
    carry.val carry1.val carry2.val carry3.val carry4.val
    hE0 hE1 hE2 hE3 hE4
  have hNb := nonce_sum_bound hn0b hn1b hn2b hn3b hn4b
  obtain ⟨B, hZlt, hBeq⟩ := hZ
  subst hBeq
  have hXb := mont_bound _ _ _ hHT hZlt hNb

  -- rounds 5–8 + canonicalization
  apply spec_mono (mont_tail_spec limbs z0 z1 z2 z3 z4 z5 z6 z7 z8 carry4
      n1 n2 n3 n4 i3 i8 i21 hl hvi3 hvi8 hvi21 hcb4
      ⟨hn1b, hn2b, hn3b, hn4b⟩ ⟨hz5, hz6, hz7, hz8⟩ hXb)
  intro r hr
  refine ⟨hr.1, hr.2.1, ?_⟩
  rw [hr.2.2]
  have hEz : (Ell : ZMod Ell) = 0 := ZMod.natCast_self Ell
  have hc := congrArg (Nat.cast (R := ZMod Ell)) hHT
  push_cast at hc
  rw [hEz] at hc
  push_cast
  linear_combination hc

end ScalarProofs
