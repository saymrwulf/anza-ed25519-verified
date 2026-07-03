/- ──────────────────────────────────────────────────────────────────────────────
   Proofs/ScalarAddSpec.lean — Scalar52 addition mod ℓ (value + bounds)

   WHAT THIS FILE CONTAINS
   The value spec for the transpiled `Scalar52::add`: for limb-bounded,
   canonical inputs (scVal < ℓ), `add a b` denotes ⟦a⟧ + ⟦b⟧ in ZMod ℓ.

   RUST ANALOG (curve25519-dalek v5, scalar.rs:161-174)
     let mut sum = Scalar52::ZERO; let mask = (1u64 << 52) - 1;
     let mut carry: u64 = 0;
     for i in 0..5 { carry = a[i] + b[i] + (carry >> 52); sum[i] = carry & mask; }
     sum.sub(&constants::L)      // conditional -ℓ canonicalization
   Transpiled: `add` → `add_loop` (5 iterations) → `Scalar52.sub sum L`.

   PROOF ARCHITECTURE
   `add_loop_spec` mirrors ScalarSubSpec's cond_add_l unrolls (the carry
   loop is the same shape with b's limbs in place of L's constants);
   `add_telescope` (ScalarSubSpec) lifts the five carry equations to
     scLimbs sum + 2^260·γ5 = scVal a + scVal b,
   canonical inputs force γ5 = 0, and `sub_val_spec` with subtrahend L
   (scVal L = ℓ ≤ ℓ — the ≤ hypothesis exists precisely for this call)
   finishes:  ⟦sub sum L⟧ = ⟦sum⟧ − ⟦L⟧ = ⟦a⟧ + ⟦b⟧ − 0.

   ROLE IN THE PYRAMID
   With sub (ScalarSubSpec), gives ℤ/ℓ its verified + and −.
   ────────────────────────────────────────────────────────────────────────────── -/
import Proofs.ScalarSubSpec
open Aeneas Aeneas.Std Result
open curve25519

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 300

namespace ScalarProofs

open Aeneas.Std.WP

/-- The addition carry loop, unrolled: five limbs of masked sums with the
    carry chain, per-limb equations r_i + 2^52·γ_(i+1) = a_i + b_i + γ_i. -/
theorem add_loop_spec (a b : Sc) (mask : U64)
    (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : U64)
    (ha : (↑a : List U64) = [a0, a1, a2, a3, a4])
    (hb : (↑b : List U64) = [b0, b1, b2, b3, b4])
    (hmask : mask.val = 2^52 - 1)
    (hbnd : a0.val < 2^52 ∧ a1.val < 2^52 ∧ a2.val < 2^52 ∧ a3.val < 2^52 ∧ a4.val < 2^52 ∧
            b0.val < 2^52 ∧ b1.val < 2^52 ∧ b2.val < 2^52 ∧ b3.val < 2^52 ∧ b4.val < 2^52) :
    backend.serial.u64.scalar.Scalar52.add_loop
        { start := 0#usize, «end» := 5#usize } a b
        backend.serial.u64.scalar.Scalar52.ZERO mask 0#u64
      ⦃ (s : Sc) => ∃ r0 r1 r2 r3 r4 : U64, ∃ γ1 γ2 γ3 γ4 γ5 : ℕ,
          (↑s : List U64) = [r0, r1, r2, r3, r4] ∧
          γ1 ≤ 1 ∧ γ2 ≤ 1 ∧ γ3 ≤ 1 ∧ γ4 ≤ 1 ∧ γ5 ≤ 1 ∧
          r0.val < 2^52 ∧ r1.val < 2^52 ∧ r2.val < 2^52 ∧ r3.val < 2^52 ∧ r4.val < 2^52 ∧
          r0.val + 2^52 * γ1 = a0.val + b0.val ∧
          r1.val + 2^52 * γ2 = a1.val + b1.val + γ1 ∧
          r2.val + 2^52 * γ3 = a2.val + b2.val + γ2 ∧
          r3.val + 2^52 * γ4 = a3.val + b3.val + γ3 ∧
          r4.val + 2^52 * γ5 = a4.val + b4.val + γ4 ⦄ := by
  obtain ⟨hA0, hA1, hA2, hA3, hA4, hB0, hB1, hB2, hB3, hB4⟩ := hbnd
  have hmaskv : mask.val = 2^52 - 1 := hmask
  unfold backend.serial.u64.scalar.Scalar52.add_loop
  -- Iteration 1 (i = 0)
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.add_loop.body,
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexUsizeU64.index,
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexMutUsizeU64.index_mut,
    bind_tc_ok]
  step with range_next_lt_spec as ⟨o1, iter1, ho1, hs1, he1⟩
  simp only [ho1]
  step as ⟨x1, hx1⟩
  step as ⟨y1, hy1⟩
  simp [ha] at hx1
  simp [hb] at hy1
  have hxb1 : x1.val < 2^52 := by rw [hx1]; exact hA0
  have hyb1 : y1.val < 2^52 := by rw [hy1]; exact hB0
  step as ⟨v1, hv1⟩
  step as ⟨g1, hg1⟩
  have hgb1 : g1.val = 0 := by rw [hg1]; rfl
  step as ⟨cy1, hcy1⟩
  step as ⟨q1, bk1, hq1, hbk1⟩
  step as ⟨r1, hr1⟩
  try simp only [spec_ok]
  have hcyv1 : cy1.val = a0.val + b0.val := by
    rw [hcy1, hv1, hx1, hy1, hgb1]; omega
  have hcyb1 : cy1.val < 2^53 := by rw [hcyv1]; omega
  have hrv1 : r1.val = cy1.val % 2^52 := by
    rw [hr1, UScalar.val_and, hmaskv, nat_and_mask52]
  -- Iteration 2 (i = 1)
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.add_loop.body,
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexUsizeU64.index,
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexMutUsizeU64.index_mut,
    bind_tc_ok]
  step with range_next_lt_spec as ⟨o2, iter2, ho2, hs2, he2⟩
  simp only [ho2]
  step as ⟨x2, hx2⟩
  step as ⟨y2, hy2⟩
  simp [ha, hs1, he1] at hx2
  simp [hb, hs1, he1] at hy2
  have hxb2 : x2.val < 2^52 := by rw [hx2]; exact hA1
  have hyb2 : y2.val < 2^52 := by rw [hy2]; exact hB1
  step as ⟨v2, hv2⟩
  step as ⟨g2, hg2⟩
  have hgeq2 : g2.val = cy1.val / 2^52 := by rw [hg2, nat_shift52]
  have hgb2 : g2.val ≤ 1 := by rw [hgeq2]; omega
  step as ⟨cy2, hcy2⟩
  step as ⟨q2, bk2, hq2, hbk2⟩
  step as ⟨r2, hr2⟩
  try simp only [spec_ok]
  have hcyv2 : cy2.val = a1.val + b1.val + g2.val := by
    rw [hcy2, hv2, hx2, hy2]
  have hcyb2 : cy2.val < 2^53 := by rw [hcyv2]; omega
  have hrv2 : r2.val = cy2.val % 2^52 := by
    rw [hr2, UScalar.val_and, hmaskv, nat_and_mask52]
  -- Iteration 3 (i = 2)
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.add_loop.body,
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexUsizeU64.index,
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexMutUsizeU64.index_mut,
    bind_tc_ok]
  step with range_next_lt_spec as ⟨o3, iter3, ho3, hs3, he3⟩
  simp only [ho3]
  step as ⟨x3, hx3⟩
  step as ⟨y3, hy3⟩
  simp [ha, hs1, he1, hs2, he2] at hx3
  simp [hb, hs1, he1, hs2, he2] at hy3
  have hxb3 : x3.val < 2^52 := by rw [hx3]; exact hA2
  have hyb3 : y3.val < 2^52 := by rw [hy3]; exact hB2
  step as ⟨v3, hv3⟩
  step as ⟨g3, hg3⟩
  have hgeq3 : g3.val = cy2.val / 2^52 := by rw [hg3, nat_shift52]
  have hgb3 : g3.val ≤ 1 := by rw [hgeq3]; omega
  step as ⟨cy3, hcy3⟩
  step as ⟨q3, bk3, hq3, hbk3⟩
  step as ⟨r3, hr3⟩
  try simp only [spec_ok]
  have hcyv3 : cy3.val = a2.val + b2.val + g3.val := by
    rw [hcy3, hv3, hx3, hy3]
  have hcyb3 : cy3.val < 2^53 := by rw [hcyv3]; omega
  have hrv3 : r3.val = cy3.val % 2^52 := by
    rw [hr3, UScalar.val_and, hmaskv, nat_and_mask52]
  -- Iteration 4 (i = 3)
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.add_loop.body,
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexUsizeU64.index,
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexMutUsizeU64.index_mut,
    bind_tc_ok]
  step with range_next_lt_spec as ⟨o4, iter4, ho4, hs4, he4⟩
  simp only [ho4]
  step as ⟨x4, hx4⟩
  step as ⟨y4, hy4⟩
  simp [ha, hs1, he1, hs2, he2, hs3, he3] at hx4
  simp [hb, hs1, he1, hs2, he2, hs3, he3] at hy4
  have hxb4 : x4.val < 2^52 := by rw [hx4]; exact hA3
  have hyb4 : y4.val < 2^52 := by rw [hy4]; exact hB3
  step as ⟨v4, hv4⟩
  step as ⟨g4, hg4⟩
  have hgeq4 : g4.val = cy3.val / 2^52 := by rw [hg4, nat_shift52]
  have hgb4 : g4.val ≤ 1 := by rw [hgeq4]; omega
  step as ⟨cy4, hcy4⟩
  step as ⟨q4, bk4, hq4, hbk4⟩
  step as ⟨r4, hr4⟩
  try simp only [spec_ok]
  have hcyv4 : cy4.val = a3.val + b3.val + g4.val := by
    rw [hcy4, hv4, hx4, hy4]
  have hcyb4 : cy4.val < 2^53 := by rw [hcyv4]; omega
  have hrv4 : r4.val = cy4.val % 2^52 := by
    rw [hr4, UScalar.val_and, hmaskv, nat_and_mask52]
  -- Iteration 5 (i = 4)
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.add_loop.body,
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexUsizeU64.index,
    backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexMutUsizeU64.index_mut,
    bind_tc_ok]
  step with range_next_lt_spec as ⟨o5, iter5, ho5, hs5, he5⟩
  simp only [ho5]
  step as ⟨x5, hx5⟩
  step as ⟨y5, hy5⟩
  simp [ha, hs1, he1, hs2, he2, hs3, he3, hs4, he4] at hx5
  simp [hb, hs1, he1, hs2, he2, hs3, he3, hs4, he4] at hy5
  have hxb5 : x5.val < 2^52 := by rw [hx5]; exact hA4
  have hyb5 : y5.val < 2^52 := by rw [hy5]; exact hB4
  step as ⟨v5, hv5⟩
  step as ⟨g5, hg5⟩
  have hgeq5 : g5.val = cy4.val / 2^52 := by rw [hg5, nat_shift52]
  have hgb5 : g5.val ≤ 1 := by rw [hgeq5]; omega
  step as ⟨cy5, hcy5⟩
  step as ⟨q5, bk5, hq5, hbk5⟩
  step as ⟨r5, hr5⟩
  try simp only [spec_ok]
  have hcyv5 : cy5.val = a4.val + b4.val + g5.val := by
    rw [hcy5, hv5, hx5, hy5]
  have hcyb5 : cy5.val < 2^53 := by rw [hcyv5]; omega
  have hrv5 : r5.val = cy5.val % 2^52 := by
    rw [hr5, UScalar.val_and, hmaskv, nat_and_mask52]
  -- Iteration 6: exhausted
  apply loop_step
  simp only [backend.serial.u64.scalar.Scalar52.add_loop.body]
  step with range_next_ge_spec as ⟨o6, iter6, ho6, hr6⟩
  simp only [ho6]
  try simp only [spec_ok]
  refine ⟨r1, r2, r3, r4, r5,
          cy1.val / 2^52, cy2.val / 2^52, cy3.val / 2^52, cy4.val / 2^52, cy5.val / 2^52,
          ?_, by omega, by omega, by omega, by omega, by omega,
          by rw [hrv1]; omega, by rw [hrv2]; omega, by rw [hrv3]; omega,
          by rw [hrv4]; omega, by rw [hrv5]; omega,
          ?_, ?_, ?_, ?_, ?_⟩
  · simp [hbk1, hbk2, hbk3, hbk4, hbk5, Array.set_val_eq, ZERO_limbs, hs1, hs2, hs3, hs4]
  · rw [hrv1, hcyv1]; omega
  · rw [hrv2, hcyv2, hgeq2]; omega
  · rw [hrv3, hcyv3, hgeq3]; omega
  · rw [hrv4, hcyv4, hgeq4]; omega
  · rw [hrv5, hcyv5, hgeq5]; omega

/-- **Scalar addition is correct mod ℓ.** For limb-bounded, canonical
    inputs (scVal < ℓ), the transpiled `Scalar52::add` denotes ⟦a⟧ + ⟦b⟧
    in `ZMod ℓ`: the carry loop computes the exact sum (canonical inputs
    force the top carry to 0), and the trailing `sub sum L` subtracts
    ⟦L⟧ = 0 in ZMod ℓ while canonicalizing. -/
theorem add_val_spec (a b : Sc)
    (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : U64)
    (ha : (↑a : List U64) = [a0, a1, a2, a3, a4])
    (hb : (↑b : List U64) = [b0, b1, b2, b3, b4])
    (hab : a0.val < 2^52 ∧ a1.val < 2^52 ∧ a2.val < 2^52 ∧ a3.val < 2^52 ∧ a4.val < 2^52)
    (hbb : b0.val < 2^52 ∧ b1.val < 2^52 ∧ b2.val < 2^52 ∧ b3.val < 2^52 ∧ b4.val < 2^52)
    (hca : scVal a < Ell) (hcb : scVal b < Ell) :
    backend.serial.u64.scalar.Scalar52.add a b
      ⦃ r => (∃ s0 s1 s2 s3 s4 : U64, (↑r : List U64) = [s0, s1, s2, s3, s4] ∧
              s0.val < 2^52 ∧ s1.val < 2^52 ∧ s2.val < 2^52 ∧ s3.val < 2^52 ∧ s4.val < 2^52) ∧
            scVal r < Ell ∧
            scDenote r = scDenote a + scDenote b ⦄ := by
  obtain ⟨hA0, hA1, hA2, hA3, hA4⟩ := hab
  obtain ⟨hB0, hB1, hB2, hB3, hB4⟩ := hbb
  unfold backend.serial.u64.scalar.Scalar52.add
  step as ⟨sh, hsh⟩
  step as ⟨mask, hmask⟩
  have hmaskv : mask.val = 2^52 - 1 := by
    simp [hmask, hsh, U64.size_def, U64.numBits]
  apply spec_bind (add_loop_spec a b mask a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 ha hb hmaskv
      ⟨hA0, hA1, hA2, hA3, hA4, hB0, hB1, hB2, hB3, hB4⟩)
  rintro sum ⟨r0, r1, r2, r3, r4, γ1, γ2, γ3, γ4, γ5, hrl,
    hg1, hg2, hg3, hg4, hg5, hr0, hr1, hr2, hr3, hr4,
    hf0, hf1, hf2, hf3, hf4⟩
  try simp only at hrl
  show backend.serial.u64.scalar.Scalar52.sub sum backend.serial.u64.constants.L
    ⦃ r => (∃ s0 s1 s2 s3 s4 : U64, (↑r : List U64) = [s0, s1, s2, s3, s4] ∧
            s0.val < 2^52 ∧ s1.val < 2^52 ∧ s2.val < 2^52 ∧ s3.val < 2^52 ∧ s4.val < 2^52) ∧
          scVal r < Ell ∧
          scDenote r = scDenote a + scDenote b ⦄
  -- telescope: scLimbs sum + 2^260·γ5 = scVal a + scVal b; canonicity kills γ5
  have hsva : scVal a = scLimbs a0 a1 a2 a3 a4 := scVal_eq a a0 a1 a2 a3 a4 ha
  have hsvb : scVal b = scLimbs b0 b1 b2 b3 b4 := scVal_eq b b0 b1 b2 b3 b4 hb
  have hT : scLimbs r0 r1 r2 r3 r4 + 2^260 * γ5
      = scLimbs a0 a1 a2 a3 a4 + scLimbs b0 b1 b2 b3 b4 := by
    unfold scLimbs
    exact add_telescope _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hf0 hf1 hf2 hf3 hf4
  have hEllbig : Ell < 2^253 := by unfold Ell; norm_num
  have hγ0 : γ5 = 0 := by
    have hlt : scLimbs a0 a1 a2 a3 a4 + scLimbs b0 b1 b2 b3 b4 < 2^254 := by
      rw [← hsva, ← hsvb]; omega
    omega
  have hsum : scVal sum = scVal a + scVal b := by
    rw [scVal_eq sum r0 r1 r2 r3 r4 hrl, hsva, hsvb]
    rw [hγ0] at hT; simpa using hT
  -- L's limbs and their bounds (literals)
  have hLb : (671914833335277:ℕ) < 2^52 ∧ (3916664325105025:ℕ) < 2^52 ∧
      (1367801:ℕ) < 2^52 ∧ (0:ℕ) < 2^52 ∧ (17592186044416:ℕ) < 2^52 := by norm_num
  have hLlist := L_limbs
  have hLv0 : (671914833335277#u64).val = 671914833335277 := by rfl
  -- apply the subtraction spec with subtrahend L (scVal L = ℓ ≤ ℓ)
  apply spec_mono (sub_val_spec sum backend.serial.u64.constants.L
      r0 r1 r2 r3 r4 _ _ _ _ _ hrl hLlist
      ⟨hr0, hr1, hr2, hr3, hr4⟩
      (by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num)
      (by rw [L_val]))
  intro r hr
  obtain ⟨hbnds, ⟨β, hβle, heq, hguard⟩, hden⟩ := hr
  rw [L_val] at heq
  refine ⟨hbnds, ?_, ?_⟩
  · -- canonicity: the trailing sub L leaves a value below ℓ
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hβle with h0 | h1
    · subst h0; omega
    · subst h1
      have hlt := hguard rfl
      rw [L_val] at hlt
      omega
  · rw [hden]
    have hL0 : scDenote backend.serial.u64.constants.L = 0 := by
      simp only [scDenote, L_val]; exact ZMod.natCast_self Ell
    have hsd : scDenote sum = scDenote a + scDenote b := by
      simp only [scDenote, hsum]; push_cast; ring
    rw [hL0, hsd]; ring

end ScalarProofs
