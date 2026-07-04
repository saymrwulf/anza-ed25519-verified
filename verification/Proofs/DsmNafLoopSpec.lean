/- ──────────────────────────────────────────────────────────────────────────────
   Proofs/DsmNafLoopSpec.lean — NAF campaign, stage 3: the w=5 digit loop,
   by induction on the remaining-bits measure (no unrolling).

   State (naf, pos, carry); exact ℤ invariant (DsmNafMath):
       carry ≤ 1 ∧ (carry = 1 → pos ≤ 254) ∧ digits ≥ pos all zero ∧
       digit conditions ∧ nafSum naf 256 + carry·2^pos = V mod 2^pos.
   One symbolic body-walk per induction step:
   · `naf_bitbuf_spec`  — the (single|cross)-word 64-bit read at bit pos,
     4-way split on the word index, closed by naf_window_single/cross.
   · `naf_update_spec`  — the odd-digit write: hcast / wrapping_sub digit,
     new carry ∈ {0,1}, exact digit value window − 32·carry′, oddness and
     |d| < 16 (the strict lower bound needs the window's oddness).
   · even step: pos+1 via naf_even_step / naf_carry_even;
     odd step: pos+5 via nafSum_set / naf_odd_step / naf_carry_odd.
   Exit (pos ≥ 256): naf_exit — the carry is provably dead and
       nafSum naf 256 = V  exactly (V < 2^253: canonical scalars, which is
   what the mul call sites provide).
   ────────────────────────────────────────────────────────────────────────────── -/
import Proofs.DsmNafMath
open Aeneas Aeneas.Std Result ControlFlow
open curve25519

set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000

namespace CurveFieldProofs

open Aeneas.Std.WP

/-! ### Digit-array set plumbing -/

/-- Entries away from the written index are unchanged. -/
theorem nafDigit_set_ne (naf naf' : Std.Array Std.I8 256#usize) (pos : ℕ)
    (d : Std.I8) (hset : (↑naf' : List Std.I8) = (↑naf : List Std.I8).set pos d)
    (k : ℕ) (hk : k < 256) (hne : k ≠ pos) :
    nafDigit naf' k = nafDigit naf k := by
  have hlen : (↑naf : List Std.I8).length = 256 := by scalar_tac
  unfold nafDigit
  rw [hset, getElem!_pos ((↑naf : List Std.I8).set pos d) k
        (by rw [List.length_set]; omega),
      List.getElem_set_ne (by omega),
      ← getElem!_pos (↑naf : List Std.I8) k (by omega)]

/-- The written entry holds the new digit. -/
theorem nafDigit_set_eq (naf naf' : Std.Array Std.I8 256#usize) (pos : ℕ)
    (d : Std.I8) (hpos : pos < 256)
    (hset : (↑naf' : List Std.I8) = (↑naf : List Std.I8).set pos d) :
    nafDigit naf' pos = d.val := by
  have hlen : (↑naf : List Std.I8).length = 256 := by scalar_tac
  unfold nafDigit
  rw [hset, getElem!_pos ((↑naf : List Std.I8).set pos d) pos
        (by rw [List.length_set]; omega),
      List.getElem_set_self]

/-! ### The 64-bit window read and the digit write -/

/-- The 64-bit buffer read of the digit loop at bit position pos: its masked
    value is the 5-bit window of V at pos. Four word cases (the fifth word is
    the zero pad), each closed by naf_window_single (bit_idx < 59) or
    naf_window_cross. -/
theorem naf_bitbuf_spec
    (x_u64 : Std.Array Std.U64 5#usize) (v0 v1 v2 v3 : Std.U64) (V : ℕ)
    (hx : (↑x_u64 : List Std.U64) = [v0, v1, v2, v3, 0#u64])
    (hVdef : V = v0.val + 2^64 * (v1.val + 2^64 * (v2.val + 2^64 * (v3.val + 2^64 * 0))))
    (u bidx : Usize) (pos : ℕ) (hposv : pos < 256)
    (hu : u.val = pos / 64) (hbidx : bidx.val = pos % 64) :
    (if bidx < 59#usize
     then do
          let i1 ← Array.index_usize x_u64 u
          i1 >>> bidx
     else
       do
       let i1 ← Array.index_usize x_u64 u
       let i2 ← i1 >>> bidx
       let i3 ← 1#usize + u
       let i4 ← Array.index_usize x_u64 i3
       let i5 ← 64#usize - bidx
       let i6 ← i4 <<< i5
       ok (i2 ||| i6))
    ⦃ buf => buf.val % 32 = (V / 2^pos) % 32 ⦄ := by
  have hb0 : v0.val < 2^64 := by scalar_tac
  have hb1 : v1.val < 2^64 := by scalar_tac
  have hb2 : v2.val < 2^64 := by scalar_tac
  have hb3 : v3.val < 2^64 := by scalar_tac
  have hulen : u.val < 4 := by clear * - hu hposv; omega
  have hsz : (U64.size : ℕ) = 2^64 := by scalar_tac
  split
  · -- single-word read
    rename_i hblt
    have hbv : pos % 64 < 59 := by
      have h := hbidx ▸ (show bidx.val < 59 by clear * - hblt; scalar_tac)
      omega
    step as ⟨w, hw⟩
    step as ⟨buf, hbuf⟩
    rcases (show pos / 64 = 0 ∨ pos / 64 = 1 ∨ pos / 64 = 2 ∨ pos / 64 = 3 by omega)
      with hc | hc | hc | hc
    · have huv : u.val = 0 := by omega
      simp only [hx, huv] at hw
      simp at hw
      rw [hbuf, hw, hbidx, Nat.shiftRight_eq_div_pow]
      have hd : V = 0 + 2^0 * (v0.val + 2^64 * (v1.val + 2^64 * (v2.val + 2^64 * (v3.val + 2^64 * 0)))) := by
        rw [hVdef]; try ring
      have h := naf_window_single V (0) v0.val (v1.val + 2^64 * (v2.val + 2^64 * (v3.val + 2^64 * 0))) 0 (pos % 64)
        hd (by norm_num) (by omega)
      rw [show (0 : ℕ) + pos % 64 = pos from by omega] at h
      exact h
    · have huv : u.val = 1 := by omega
      simp only [hx, huv] at hw
      simp at hw
      rw [hbuf, hw, hbidx, Nat.shiftRight_eq_div_pow]
      have hd : V = v0.val + 2^64 * (v1.val + 2^64 * (v2.val + 2^64 * (v3.val + 2^64 * 0))) := by
        rw [hVdef]; try ring
      have h := naf_window_single V (v0.val) v1.val (v2.val + 2^64 * (v3.val + 2^64 * 0)) 64 (pos % 64)
        hd (by omega) (by omega)
      rw [show (64 : ℕ) + pos % 64 = pos from by omega] at h
      exact h
    · have huv : u.val = 2 := by omega
      simp only [hx, huv] at hw
      simp at hw
      rw [hbuf, hw, hbidx, Nat.shiftRight_eq_div_pow]
      have hd : V = v0.val + 2^64 * v1.val + 2^128 * (v2.val + 2^64 * (v3.val + 2^64 * 0)) := by
        rw [hVdef]; try ring
      have h := naf_window_single V (v0.val + 2^64 * v1.val) v2.val (v3.val + 2^64 * 0) 128 (pos % 64)
        hd (by omega) (by omega)
      rw [show (128 : ℕ) + pos % 64 = pos from by omega] at h
      exact h
    · have huv : u.val = 3 := by omega
      simp only [hx, huv] at hw
      simp at hw
      rw [hbuf, hw, hbidx, Nat.shiftRight_eq_div_pow]
      have hd : V = v0.val + 2^64 * v1.val + 2^128 * v2.val + 2^192 * (v3.val + 2^64 * (0)) := by
        rw [hVdef]; try ring
      have h := naf_window_single V (v0.val + 2^64 * v1.val + 2^128 * v2.val) v3.val (0) 192 (pos % 64)
        hd (by omega) (by omega)
      rw [show (192 : ℕ) + pos % 64 = pos from by omega] at h
      exact h
  · -- cross-word read
    rename_i hbge
    have hbv : 59 ≤ pos % 64 := by
      have h : ¬ (bidx.val < 59) := by clear * - hbge; scalar_tac
      omega
    step as ⟨w, hw⟩
    step as ⟨i2, hi2⟩
    step as ⟨i3, hi3⟩
    step as ⟨w', hw'⟩
    step as ⟨i5, hi5⟩
    step as ⟨i6, hi6⟩
    try simp only [spec_ok]
    rcases (show pos / 64 = 0 ∨ pos / 64 = 1 ∨ pos / 64 = 2 ∨ pos / 64 = 3 by omega)
      with hc | hc | hc | hc
    · have huv : u.val = 0 := by omega
      have hi3v : i3.val = 1 := by clear * - hi3 huv; omega
      simp only [hx, huv] at hw
      simp at hw
      simp only [hx, hi3v] at hw'
      simp at hw'
      rw [UScalar.val_or, hi2, hi6, hi5, hbidx, hw, hw', hsz,
          Nat.shiftRight_eq_div_pow]
      have hd : V = 0 + 2^0 * (v0.val + 2^64 * (v1.val + 2^64 * (v2.val + 2^64 * (v3.val + 2^64 * 0)))) := by
        rw [hVdef]; try simp; try ring
      have h := naf_window_cross V (0) v0.val (v1.val) (v2.val + 2^64 * (v3.val + 2^64 * 0)) 0 (pos % 64)
        hd (by norm_num) (by omega) (by omega)
      rw [show (0 : ℕ) + pos % 64 = pos from by omega] at h
      exact h
    · have huv : u.val = 1 := by omega
      have hi3v : i3.val = 2 := by clear * - hi3 huv; omega
      simp only [hx, huv] at hw
      simp at hw
      simp only [hx, hi3v] at hw'
      simp at hw'
      rw [UScalar.val_or, hi2, hi6, hi5, hbidx, hw, hw', hsz,
          Nat.shiftRight_eq_div_pow]
      have hd : V = v0.val + 2^64 * (v1.val + 2^64 * (v2.val + 2^64 * (v3.val + 2^64 * 0))) := by
        rw [hVdef]; try simp; try ring
      have h := naf_window_cross V (v0.val) v1.val (v2.val) (v3.val + 2^64 * 0) 64 (pos % 64)
        hd (by omega) (by omega) (by omega)
      rw [show (64 : ℕ) + pos % 64 = pos from by omega] at h
      exact h
    · have huv : u.val = 2 := by omega
      have hi3v : i3.val = 3 := by clear * - hi3 huv; omega
      simp only [hx, huv] at hw
      simp at hw
      simp only [hx, hi3v] at hw'
      simp at hw'
      rw [UScalar.val_or, hi2, hi6, hi5, hbidx, hw, hw', hsz,
          Nat.shiftRight_eq_div_pow]
      have hd : V = v0.val + 2^64 * v1.val + 2^128 * (v2.val + 2^64 * (v3.val + 2^64 * (0))) := by
        rw [hVdef]; try simp; try ring
      have h := naf_window_cross V (v0.val + 2^64 * v1.val) v2.val (v3.val) (0) 128 (pos % 64)
        hd (by omega) (by omega) (by omega)
      rw [show (128 : ℕ) + pos % 64 = pos from by omega] at h
      exact h
    · have huv : u.val = 3 := by omega
      have hi3v : i3.val = 4 := by clear * - hi3 huv; omega
      simp only [hx, huv] at hw
      simp at hw
      simp only [hx, hi3v] at hw'
      simp at hw'
      rw [UScalar.val_or, hi2, hi6, hi5, hbidx, hw, hw', hsz,
          Nat.shiftRight_eq_div_pow]
      have hd : V = v0.val + 2^64 * v1.val + 2^128 * v2.val + 2^192 * (v3.val + 2^64 * ((0#u64).val + 2^64 * (0))) := by
        rw [hVdef]; try simp; try ring
      have h := naf_window_cross V (v0.val + 2^64 * v1.val + 2^128 * v2.val) v3.val ((0#u64).val) (0) 192 (pos % 64)
        hd (by omega) (by omega) (by omega)
      rw [show (192 : ℕ) + pos % 64 = pos from by omega] at h
      exact h

/-- The odd-digit write: hcast (or hcast + wrapping_sub) produces the digit
    window − 32·carry′ with carry′ the ≥16 indicator; the digit is odd with
    |d| < 16, and the entry is written at pos. -/
theorem naf_update_spec (naf : Std.Array Std.I8 256#usize) (pos : Usize) (window : Std.U64)
    (hpos : pos.val < 256) (hwle : window.val ≤ 32) (hwodd : window.val % 2 = 1) :
    (if window < 16#u64
     then do
          let i4 ← lift (UScalar.hcast .I8 window)
          let a ← Array.update naf pos i4
          ok (a, 0#u64)
     else
       do
       let i4 ← lift (UScalar.hcast .I8 window)
       let i5 ← lift (UScalar.hcast .I8 32#u64)
       let i6 ← lift (core.num.I8.wrapping_sub i4 i5)
       let a ← Array.update naf pos i6
       ok (a, 1#u64))
    ⦃ p => ∃ d : Std.I8, (↑p.1 : List Std.I8) = (↑naf : List Std.I8).set pos.val d ∧
        p.2.val ≤ 1 ∧
        (d.val : ℤ) = (window.val : ℤ) - 32 * (p.2.val : ℤ) ∧
        d.val % 2 = 1 ∧ -16 < d.val ∧ d.val < 16 ∧
        ((window.val < 16 ∧ p.2.val = 0) ∨ (16 ≤ window.val ∧ p.2.val = 1)) ⦄ := by
  split
  · rename_i hlt
    have hltv : window.val < 16 := by clear * - hlt; scalar_tac
    step with (UScalar.hcast_inBounds_spec .I8 window
      (by clear * - hltv; scalar_tac)) as ⟨d, hd⟩
    step as ⟨a, ha⟩
    try simp only [spec_ok]
    refine ⟨d, by rw [ha, Array.set_val_eq], by simp, by simp [hd], ?_, ?_, ?_,
      Or.inl ⟨hltv, by simp⟩⟩
    · rw [hd]; clear * - hwodd; omega
    · rw [hd]; push_cast; omega
    · rw [hd]; clear * - hltv; omega
  · rename_i hge
    have hgev : 16 ≤ window.val := by clear * - hge; scalar_tac
    step with (UScalar.hcast_inBounds_spec .I8 window
      (by clear * - hwle; scalar_tac)) as ⟨d0, hd0⟩
    step with (UScalar.hcast_inBounds_spec .I8 32#u64
      (by scalar_tac)) as ⟨t32, ht32⟩
    step as ⟨d, hd⟩
    step as ⟨a, ha⟩
    try simp only [spec_ok]
    have hdv : (d.val : ℤ) = (window.val : ℤ) - 32 := by
      rw [hd]
      simp only [core.num.I8.wrapping_sub_val_eq, hd0, ht32]
      have hb := Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 8 ((window.val : ℤ) - 32)
        (by norm_num) (by clear * - ; push_cast; omega)
        (by clear * - hwle; push_cast; omega)
      push_cast at hb ⊢
      convert hb using 2 <;> norm_num
    refine ⟨d, by rw [ha, Array.set_val_eq], by simp, by simp [hdv], ?_, ?_, ?_,
      Or.inr ⟨hgev, by simp⟩⟩
    · rw [hdv]; clear * - hwodd hgev; omega
    · rw [hdv]; clear * - hgev hwodd; push_cast; omega
    · rw [hdv]; clear * - hwle; omega


/-! ### The digit loop -/

/-- **The w=5 NAF digit loop**, by induction on the remaining-bits measure.
    From any state satisfying the invariant, the loop returns a digit array
    with the NAF digit conditions and exact value V. -/
theorem naf_digit_loop_spec
    (x_u64 : Std.Array Std.U64 5#usize) (v0 v1 v2 v3 : Std.U64) (V : ℕ)
    (hx : (↑x_u64 : List Std.U64) = [v0, v1, v2, v3, 0#u64])
    (hVdef : V = v0.val + 2^64 * (v1.val + 2^64 * (v2.val + 2^64 * (v3.val + 2^64 * 0))))
    (hV : V < 2^253) (m : ℕ) :
    ∀ (naf : Std.Array Std.I8 256#usize) (pos : Usize) (carry : Std.U64),
    256 - pos.val ≤ m →
    carry.val ≤ 1 →
    (carry.val = 1 → pos.val ≤ 254) →
    (∀ k, pos.val ≤ k → k < 256 → nafDigit naf k = 0) →
    (∀ k, k < 256 → (nafDigit naf k = 0 ∨ nafDigit naf k % 2 = 1) ∧
        -16 < nafDigit naf k ∧ nafDigit naf k < 16) →
    nafSum naf 256 + carry.val * 2^pos.val = ((V % 2^pos.val : ℕ) : ℤ) →
    scalar.Scalar.non_adjacent_form_loop1 5#usize naf x_u64 32#u64 31#u64 pos carry
      ⦃ res => NafDigits res ∧ nafSum res 256 = (V : ℤ) ⦄ := by
  induction m with
  | zero =>
    intro naf pos carry hm hc hcp hzero hdig hinv
    unfold scalar.Scalar.non_adjacent_form_loop1
    apply loop_step
    simp only [scalar.Scalar.non_adjacent_form_loop1.body]
    have hguard : ¬ (pos < 256#usize) := by clear * - hm; scalar_tac
    rw [if_neg hguard]
    try simp only [spec_ok]
    exact ⟨hdig, naf_exit V pos.val carry.val _ hV (by clear * - hm; omega) hc hcp hinv⟩
  | succ m ih =>
    intro naf pos carry hm hc hcp hzero hdig hinv
    unfold scalar.Scalar.non_adjacent_form_loop1
    apply loop_step
    simp only [scalar.Scalar.non_adjacent_form_loop1.body]
    by_cases hguard : pos < 256#usize
    swap
    · -- exit branch (measure slack)
      rw [if_neg hguard]
      try simp only [spec_ok]
      have hge : 256 ≤ pos.val := by clear * - hguard; scalar_tac
      exact ⟨hdig, naf_exit V pos.val carry.val _ hV hge hc hcp hinv⟩
    · rw [if_pos hguard]
      have hposv : pos.val < 256 := by clear * - hguard; scalar_tac
      -- u64_idx ← pos / 64 ; bit_idx ← pos % 64 ; i ← 64 − 5
      step as ⟨u, hu⟩
      step as ⟨bidx, hbidx⟩
      step as ⟨i59, hi59⟩
      have hi59v : i59 = 59#usize := by clear * - hi59; scalar_tac
      rw [hi59v]
      -- bit_buf: the 5-bit window of V at pos
      step with (naf_bitbuf_spec x_u64 v0 v1 v2 v3 V hx hVdef u bidx pos.val
        hposv hu hbidx) as ⟨buf, hbuf⟩
      -- i1 ← buf &&& 31 : the masked window
      step as ⟨msk, hmsk⟩
      have hmskv : msk.val = (V / 2^pos.val) % 32 := by
        rw [hmsk, UScalar.val_and]
        rw [show (31#u64).val = 2^5 - 1 by scalar_tac,
            Nat.and_two_pow_sub_one_eq_mod]
        rw [show (2:ℕ)^5 = 32 from by norm_num]
        exact hbuf
      -- window ← carry + msk
      step as ⟨win, hwin⟩
      have hwinv : win.val = carry.val + (V / 2^pos.val) % 32 := by
        rw [hwin, hmskv]
      have hwle : win.val ≤ 32 := by clear * - hwinv hc; omega
      -- i2 ← win &&& 1 : the parity bit
      step as ⟨par, hpar⟩
      have hparv : par.val = win.val % 2 := by
        rw [hpar, UScalar.val_and]
        rw [show (1#u64).val = 2^1 - 1 by scalar_tac,
            Nat.and_two_pow_sub_one_eq_mod]
        try norm_num
      split
      · -- EVEN window: digit 0, pos+1, carry unchanged
        rename_i hz
        have heven : (carry.val + (V / 2^pos.val) % 32) % 2 = 0 := by
          have h : par.val = 0 := by rw [hz]; simp
          rw [← hwinv, ← hparv]
          exact h
        step as ⟨pos1, hpos1⟩
        have hpos1v : pos1.val = pos.val + 1 := by clear * - hpos1; omega
        try simp only [spec_ok]
        apply ih naf pos1 carry (by clear * - hm hpos1v; omega) hc
          (fun h1 => by have := naf_carry_even V pos.val carry.val hV hc heven h1
                        clear * - this hpos1v; omega)
          (fun k hk1 hk2 => hzero k (by clear * - hk1 hpos1v; omega) hk2)
          hdig
          (by rw [hpos1v]
              exact naf_even_step V pos.val carry.val _ hc hinv heven)
      · -- ODD window: write digit, pos+5, carry from the ≥16 test
        rename_i hnz
        have hwodd : win.val % 2 = 1 := by
          have h : par.val ≠ 0 := by
            clear * - hnz
            intro h
            exact hnz (by scalar_tac)
          clear * - h hparv
          omega
        -- i3 ← 32 / 2 (= 16)
        step as ⟨h16, hh16⟩
        have hh16v : h16 = 16#u64 := by clear * - hh16; scalar_tac
        rw [hh16v]
        -- the digit write (both branches of the < 16 test)
        step with (naf_update_spec naf pos win hposv hwle hwodd) as
          ⟨d, naf1, carry1, hset, hc1, hdval, hdodd, hdlo, hdhi, hcase⟩
        -- pos1 ← pos + 5
        step as ⟨pos1, hpos1⟩
        have hpos1v : pos1.val = pos.val + 5 := by clear * - hpos1; scalar_tac
        try simp only [spec_ok]
        -- the digit facts at the written index and away from it
        have holdz : nafDigit naf pos.val = 0 :=
          hzero pos.val (le_refl _) hposv
        have hsum1 : nafSum naf1 256 = nafSum naf 256 + d.val * 2^pos.val :=
          nafSum_set naf naf1 pos.val d hposv holdz hset
        have hdig1 : ∀ k, k < 256 → nafDigit naf1 k =
            if k = pos.val then d.val else nafDigit naf k := by
          intro k hk
          by_cases h : k = pos.val
          · subst h
            rw [nafDigit_set_eq naf naf1 pos.val d hk hset, if_pos rfl]
          · rw [nafDigit_set_ne naf naf1 pos.val d hset k hk h, if_neg h]
        -- the window as a ℕ fact for the step lemmas
        have hwcase : (carry.val + (V / 2^pos.val) % 32 < 16 ∧ carry1.val = 0) ∨
            (16 ≤ carry.val + (V / 2^pos.val) % 32 ∧ carry1.val = 1) := by
          rw [← hwinv]
          exact hcase
        apply ih naf1 pos1 carry1 (by clear * - hm hpos1v; omega) hc1
          (fun h1 => by
            have := naf_carry_odd V pos.val carry.val carry1.val hV hc hwcase h1
            clear * - this hpos1v; omega)
          (fun k hk1 hk2 => by
            rw [hdig1 k hk2, if_neg (by clear * - hk1 hpos1v hposv; omega)]
            exact hzero k (by clear * - hk1 hpos1v; omega) hk2)
          (fun k hk => by
            rw [hdig1 k hk]
            by_cases h : k = pos.val
            · rw [if_pos h]
              exact ⟨Or.inr hdodd, hdlo, hdhi⟩
            · rw [if_neg h]
              exact hdig k hk)
          (by rw [hpos1v, hsum1]
              have hd' : (d.val : ℤ) = (carry.val : ℤ) +
                  ((V / 2^pos.val) % 32 : ℕ) - 32 * carry1.val := by
                rw [hdval, hwinv]
                push_cast
                ring
              exact naf_odd_step V pos.val carry.val carry1.val _ d.val hinv hd')


end CurveFieldProofs
