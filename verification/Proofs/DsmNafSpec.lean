/- ──────────────────────────────────────────────────────────────────────────────
   Proofs/DsmNafSpec.lean — NAF campaign, stage 4: the public spec of
   `Scalar::non_adjacent_form(5)`.

   Composes the proven stages: both entry masserts DISCHARGED (w = 5 is in
   [2,8]), the LE byte→word load (DsmNafLoadSpec), width = 1<<<5 = 32 and
   window_mask = 31 computed, and the digit loop (DsmNafLoopSpec) seeded
   with the all-zeros state whose invariant is trivial.

   POST: the 256 digits satisfy the NAF conditions (odd-or-zero, |d| < 16 —
   exactly `NafDigits`, what dsm_loop_spec consumes) and their signed sum
   reconstructs the scalar's little-endian byte value EXACTLY:
       nafSum res 256 = V   (as integers, no modular slack).
   Requires V < 2^253 — canonical scalars, which the mul call sites provide.
   ────────────────────────────────────────────────────────────────────────────── -/
import Proofs.DsmNafLoadSpec
import Proofs.DsmNafLoopSpec
open Aeneas Aeneas.Std Result ControlFlow
open curve25519

set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000

namespace CurveFieldProofs

open Aeneas.Std.WP

/-- **Scalar::non_adjacent_form(5)**: for a scalar whose 32-byte LE value V
    is below 2^253, the result is a 256-entry NAF digit array — every digit
    odd or zero with |d| < 16, and Σ naf[k]·2^k = V exactly. Both entry
    masserts are discharged. -/
theorem non_adjacent_form_spec (self : scalar.Scalar)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 : Std.U8)
    (hb : (↑self.bytes : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31])
    (V : ℕ)
    (hVbytes : V = b0.val + b1.val * 2^8 + b2.val * 2^16 + b3.val * 2^24 + b4.val * 2^32 + b5.val * 2^40 + b6.val * 2^48 + b7.val * 2^56 + b8.val * 2^64 + b9.val * 2^72 + b10.val * 2^80 + b11.val * 2^88 + b12.val * 2^96 + b13.val * 2^104 + b14.val * 2^112 + b15.val * 2^120 + b16.val * 2^128 + b17.val * 2^136 + b18.val * 2^144 + b19.val * 2^152 + b20.val * 2^160 + b21.val * 2^168 + b22.val * 2^176 + b23.val * 2^184 + b24.val * 2^192 + b25.val * 2^200 + b26.val * 2^208 + b27.val * 2^216 + b28.val * 2^224 + b29.val * 2^232 + b30.val * 2^240 + b31.val * 2^248)
    (hV : V < 2^253) :
    scalar.Scalar.non_adjacent_form self 5#usize ⦃ res =>
      NafDigits res ∧ nafSum res 256 = (V : ℤ) ⦄ := by
  unfold scalar.Scalar.non_adjacent_form
  step with (massert_spec (5#usize ≥ 2#usize) (by scalar_tac)) as ⟨h2⟩
  step with (massert_spec (5#usize ≤ 8#usize) (by scalar_tac)) as ⟨h8⟩
  -- the LE load fills x_u64[0..3]; word 4 stays 0
  step with (naf_load_spec self (Array.repeat 5#usize 0#u64)
    b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31
    hb (by simp [List.replicate])) as ⟨v0, v1, v2, v3, ws, hws, hv0, hv1, hv2, hv3⟩
  -- width ← 1 <<< 5 (= 32), window_mask ← width − 1 (= 31)
  step as ⟨wd, hwd⟩
  have hwdv : wd = 32#u64 := by clear * - hwd; scalar_tac
  rw [hwdv]
  step as ⟨mk, hmk⟩
  have hmkv : mk = 31#u64 := by clear * - hmk; scalar_tac
  rw [hmkv]
  -- the initial all-zeros digit state
  have hz : ∀ k, k < 256 → nafDigit (Array.repeat 256#usize 0#i8) k = 0 := by
    intro k hk
    unfold nafDigit
    rw [getElem!_pos (↑(Array.repeat 256#usize 0#i8) : List Std.I8) k
        (by simp; omega)]
    simp only [Array.repeat_val, List.getElem_replicate]
    simp
  have hsum0 : nafSum (Array.repeat 256#usize 0#i8) 256 = 0 := by
    unfold nafSum
    apply Finset.sum_eq_zero
    intro k hk
    rw [hz k (Finset.mem_range.mp hk)]
    ring
  -- the word-form value
  have hVw : V = v0.val + 2^64 * (v1.val + 2^64 * (v2.val + 2^64 * (v3.val + 2^64 * 0))) := by
    rw [hVbytes, hv0, hv1, hv2, hv3]
    ring
  -- the digit loop from the trivial invariant
  apply naf_digit_loop_spec ws v0 v1 v2 v3 V hws hVw hV 256
    (Array.repeat 256#usize 0#i8) 0#usize 0#u64
    (by scalar_tac)
    (by scalar_tac)
    (by intro h; simp at h)
    (fun k _ hk => hz k hk)
    (fun k hk => ⟨Or.inl (hz k hk), by rw [hz k hk]; norm_num,
                  by rw [hz k hk]; norm_num⟩)
    (by simp [hsum0])

end CurveFieldProofs
