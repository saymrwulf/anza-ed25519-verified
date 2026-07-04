/- ──────────────────────────────────────────────────────────────────────────────
   Proofs/DsmNafMath.lean — NAF campaign, stage 2: the pure arithmetic core
   of the w=5 NAF digit loop (no extraction dependence beyond `nafDigit`).

   The digit loop's state is (naf, pos, carry) with the exact ℤ invariant
       nafSum naf 256 + carry·2^pos = V mod 2^pos
   (digits at k ≥ pos all zero, carry ≤ 1, and carry = 1 → pos ≤ 254 given
   V < 2^253 — the component that kills the carry at exit).

   Step theorems the monadic walk plugs in:
   · `nafSum_set`          — writing a fresh digit adds d·2^pos to the sum.
   · `div_pow_shift` / `mod32_absorb` / `naf_window_single` / `naf_window_cross`
     — the 64-bit buffer read at bit position p+b sees (V >> (p+b)) mod 32
     (single word when b + 5 ≤ 64; cross-word via disjoint-OR otherwise).
   · `naf_even_step`       — even window ⇒ pos+1, carry preserved (the parity
     of V >> pos matches carry, so both sides absorb carry·2^(pos+1)).
   · `naf_odd_step`        — odd window ⇒ digit (window − 32·carry'), pos+5:
     the digit plus the new carry reconstruct the 5 consumed bits
     (Nat.mod_mul telescoping).
   · `naf_carry_even` / `naf_carry_odd` — carry = 1 → pos ≤ 254 propagation
     from V < 2^253.
   · `naf_exit`            — pos ≥ 256 kills the carry: nafSum = V exactly.
   ────────────────────────────────────────────────────────────────────────────── -/
import Proofs.DsmLoopSpec
open Aeneas Aeneas.Std
open curve25519

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000

namespace CurveFieldProofs

/-! ### The signed digit sum -/

/-- Σ_{k<m} naf[k]·2^k over ℤ — the value a digit array denotes. -/
def nafSum (naf : Std.Array Std.I8 256#usize) (m : ℕ) : ℤ :=
  ∑ k ∈ Finset.range m, nafDigit naf k * 2^k

/-- Setting entry `pos` (previously 0) adds d·2^pos to the full sum. -/
theorem nafSum_set (naf naf' : Std.Array Std.I8 256#usize) (pos : ℕ) (d : Std.I8)
    (hpos : pos < 256) (hold : nafDigit naf pos = 0)
    (hset : (↑naf' : List Std.I8) = (↑naf : List Std.I8).set pos d) :
    nafSum naf' 256 = nafSum naf 256 + d.val * 2^pos := by
  have hlen : (↑naf : List Std.I8).length = 256 := by scalar_tac
  have hlen' : ((↑naf : List Std.I8).set pos d).length = 256 := by
    rw [List.length_set]; exact hlen
  have hdig : ∀ k, k < 256 → nafDigit naf' k =
      if k = pos then d.val else nafDigit naf k := by
    intro k hk
    unfold nafDigit
    rw [hset]
    by_cases h : k = pos
    · subst h
      rw [getElem!_pos ((↑naf : List Std.I8).set k d) k (by omega),
          List.getElem_set_self]
      simp
    · rw [getElem!_pos ((↑naf : List Std.I8).set pos d) k (by omega),
          List.getElem_set_ne (by omega),
          ← getElem!_pos (↑naf : List Std.I8) k (by omega)]
      rw [if_neg h]
  unfold nafSum
  have hmem : pos ∈ Finset.range 256 := Finset.mem_range.mpr hpos
  rw [← Finset.sum_erase_add _ _ hmem, ← Finset.sum_erase_add _ _ hmem]
  have hcongr : ∑ k ∈ (Finset.range 256).erase pos, nafDigit naf' k * 2^k
      = ∑ k ∈ (Finset.range 256).erase pos, nafDigit naf k * 2^k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hdig k (Finset.mem_range.mp (Finset.mem_of_mem_erase hk)),
        if_neg (Finset.ne_of_mem_erase hk)]
  rw [hcongr, hdig pos hpos, if_pos rfl, hold]
  ring

/-! ### Window-read arithmetic -/

/-- Dividing the three-part value lo + 2^p·(w + 2^64·rest) by 2^(p+b)
    (b ≤ 64, lo < 2^p) yields w >> b plus the rest shifted down. -/
theorem div_pow_shift (lo w rest p b : ℕ) (hlo : lo < 2^p) (hb : b ≤ 64) :
    (lo + 2^p * (w + 2^64 * rest)) / 2^(p+b) = w / 2^b + 2^(64-b) * rest := by
  have hp : (0:ℕ) < 2^p := Nat.two_pow_pos p
  have hbp : (0:ℕ) < 2^b := Nat.two_pow_pos b
  rw [pow_add, ← Nat.div_div_eq_div_mul]
  have h1 : (lo + 2^p * (w + 2^64 * rest)) / 2^p = w + 2^64 * rest := by
    rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hlo, Nat.zero_add]
  rw [h1]
  have h2 : (2:ℕ)^64 = 2^b * 2^(64-b) := by
    rw [← pow_add]; congr 1; omega
  rw [h2, Nat.mul_assoc, Nat.add_mul_div_left _ _ hbp]

/-- Multiples of 2^m (m ≥ 5) vanish mod 32. -/
theorem mod32_absorb (x y m : ℕ) (hm : 5 ≤ m) :
    (x + 2^m * y) % 32 = x % 32 := by
  have h : (2:ℕ)^m = 32 * 2^(m-5) := by
    rw [show (32:ℕ) = 2^5 by norm_num, ← pow_add]; congr 1; omega
  rw [h, Nat.mul_assoc, Nat.add_mul_mod_self_left]

/-- Single-word window read: when the 5-bit window at bit b fits inside
    word w (b + 5 ≤ 64), (w >> b) mod 32 is the value's window at p+b. -/
theorem naf_window_single (V lo w rest p b : ℕ)
    (hV : V = lo + 2^p * (w + 2^64 * rest)) (hlo : lo < 2^p) (hb : b + 5 ≤ 64) :
    (w / 2^b) % 32 = (V / 2^(p+b)) % 32 := by
  rw [hV, div_pow_shift lo w rest p b hlo (by omega)]
  exact (mod32_absorb _ _ _ (by omega)).symm

/-- Cross-word window read: when the window at bit b straddles into the next
    word w' (b ≥ 60), the extracted read (w >> b) ||| ((w' << (64−b)) mod 2^64)
    still sees the value's window at p+b, mod 32. -/
theorem naf_window_cross (V lo w w' rest p b : ℕ)
    (hV : V = lo + 2^p * (w + 2^64 * (w' + 2^64 * rest)))
    (hlo : lo < 2^p) (hw : w < 2^64) (hb : b < 64) :
    ((w / 2^b) ||| (w' <<< (64 - b)) % 2^64) % 32 = (V / 2^(p+b)) % 32 := by
  have hp64 : (2:ℕ)^(64-b) * 2^b = 2^64 := by
    rw [← pow_add]; congr 1; omega
  have hp128 : (2:ℕ)^(64-b) * 2^64 = 2^(128-b) := by
    rw [← pow_add]; congr 1; omega
  -- the truncated shift: (w' << (64−b)) mod 2^64 = 2^(64−b)·(w' mod 2^b)
  have hsh : (w' <<< (64 - b)) % 2^64 = 2^(64-b) * (w' % 2^b) := by
    rw [Nat.shiftLeft_eq, Nat.mul_comm w' _, ← hp64, Nat.mul_mod_mul_left]
  -- the OR is disjoint: w >> b < 2^(64−b)
  have hdl : w / 2^b < 2^(64-b) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos b)]
    calc w < 2^64 := hw
      _ = 2^(64-b) * 2^b := hp64.symm
  have hor := Nat.two_pow_add_eq_or_of_lt (b := w / 2^b) (i := 64-b) hdl (w' % 2^b)
  rw [hsh, Nat.lor_comm, ← hor]
  -- the value side
  rw [hV, div_pow_shift lo w _ p b hlo (by omega)]
  -- both sides are (w/2^b + 2^(64−b)·(w' mod 2^b)) mod 32 after absorbing
  -- the 2^64-multiples: w' = w' mod 2^b + 2^b·(w'/2^b)
  have hw' : w' = w' % 2^b + 2^b * (w' / 2^b) := (Nat.mod_add_div _ _).symm
  have e1 : w / 2^b + 2^(64-b) * (w' + 2^64 * rest)
      = (2^(64-b) * (w' % 2^b) + w / 2^b)
        + 2^64 * (w' / 2^b + 2^(64-b) * rest) := by
    conv_lhs => rw [hw']
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, ← Nat.mul_assoc, hp64,
        ← Nat.mul_assoc, hp128]
    have hp128' : (2:ℕ)^(128-b) = 2^64 * 2^(64-b) := by
      rw [← pow_add]; congr 1; omega
    rw [hp128']
    ring
  rw [e1]
  have := mod32_absorb (2^(64-b) * (w' % 2^b) + w / 2^b)
    (w' / 2^b + 2^(64-b) * rest) 64 (by omega)
  rw [this]

/-! ### Invariant step theorems -/

/-- Even window: digit 0, position advances by 1, carry preserved.
    The parity of V >> pos equals the carry, so the invariant extends. -/
theorem naf_even_step (V pos : ℕ) (carry : ℕ) (S : ℤ)
    (hc : carry ≤ 1)
    (hinv : S + carry * 2^pos = ((V % 2^pos : ℕ) : ℤ))
    (heven : (carry + (V / 2^pos) % 32) % 2 = 0) :
    S + carry * 2^(pos+1) = ((V % 2^(pos+1) : ℕ) : ℤ) := by
  have hmm : V % 2^(pos+1) = V % 2^pos + 2^pos * ((V / 2^pos) % 2) := by
    rw [pow_succ, Nat.mod_mul]
  have hpar : (V / 2^pos) % 2 = carry := by omega
  rw [hmm, hpar]
  push_cast at hinv ⊢
  linear_combination hinv

/-- Odd window: digit window − 32·carry', position advances by 5.
    The digit plus the promoted carry reconstruct the 5 consumed bits. -/
theorem naf_odd_step (V pos : ℕ) (carry carry' : ℕ) (S d : ℤ)
    (hinv : S + carry * 2^pos = ((V % 2^pos : ℕ) : ℤ))
    (hd : d = (carry : ℤ) + ((V / 2^pos) % 32 : ℕ) - 32 * carry') :
    (S + d * 2^pos) + carry' * 2^(pos+5) = ((V % 2^(pos+5) : ℕ) : ℤ) := by
  have hmm : V % 2^(pos+5) = V % 2^pos + 2^pos * ((V / 2^pos) % 32) := by
    have h : (2:ℕ)^(pos+5) = 2^pos * 32 := by rw [pow_add]; norm_num
    rw [h, Nat.mod_mul]
  rw [hmm, hd]
  push_cast at hinv ⊢
  linear_combination hinv

/-- Carry propagation, even step: with V < 2^253, an even step that keeps
    carry = 1 must be reading a set bit, so pos ≤ 252 and pos+1 ≤ 254. -/
theorem naf_carry_even (V pos : ℕ) (carry : ℕ) (hV : V < 2^253)
    (hc : carry ≤ 1)
    (heven : (carry + (V / 2^pos) % 32) % 2 = 0) :
    carry = 1 → pos + 1 ≤ 254 := by
  intro h1
  subst h1
  have h3 : 1 ≤ (V / 2^pos) % 32 := by
    generalize (V / 2^pos) % 32 = r at heven ⊢
    omega
  have hge : 1 ≤ V / 2^pos := le_trans h3 (Nat.mod_le _ _)
  have hle : 2^pos ≤ V := by
    have h5 := (Nat.le_div_iff_mul_le (Nat.two_pow_pos pos)).mp hge
    simpa using h5
  have hpb : pos ≤ 252 := by
    by_contra h
    have h253 : (2:ℕ)^253 ≤ 2^pos := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact absurd (lt_of_le_of_lt (le_trans h253 hle) hV) (lt_irrefl _)
  omega

/-- Carry propagation, odd step: producing carry' = 1 needs window ≥ 16, so
    V >> pos ≥ 15, forcing pos ≤ 249 (V < 2^253) and pos+5 ≤ 254. -/
theorem naf_carry_odd (V pos : ℕ) (carry carry' : ℕ) (hV : V < 2^253)
    (hc : carry ≤ 1)
    (hcw : (carry + (V / 2^pos) % 32 < 16 ∧ carry' = 0) ∨
           (16 ≤ carry + (V / 2^pos) % 32 ∧ carry' = 1)) :
    carry' = 1 → pos + 5 ≤ 254 := by
  intro h1
  rcases hcw with ⟨-, h0⟩ | ⟨hge, -⟩
  · omega
  · have h15 : 15 ≤ (V / 2^pos) % 32 := by
      generalize (V / 2^pos) % 32 = r at hge ⊢
      omega
    have hge15 : 15 ≤ V / 2^pos := le_trans h15 (Nat.mod_le _ _)
    have hmul : 15 * 2^pos ≤ V :=
      (Nat.le_div_iff_mul_le (Nat.two_pow_pos pos)).mp hge15
    have hpb : pos ≤ 249 := by
      by_contra h
      have h250 : (2:ℕ)^250 ≤ 2^pos := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hbig : (2:ℕ)^253 < 15 * 2^250 := by norm_num
      have hmono : 15 * 2^250 ≤ 15 * 2^pos := Nat.mul_le_mul_left 15 h250
      exact absurd (lt_of_le_of_lt (le_trans hmono hmul) hV) (not_lt.mpr hbig.le)
    omega

/-- Exit: at pos ≥ 256 the carry must be dead (carry = 1 forces pos ≤ 254),
    and V mod 2^pos = V, so the digit sum equals V exactly. -/
theorem naf_exit (V pos : ℕ) (carry : ℕ) (S : ℤ) (hV : V < 2^253)
    (hpos : 256 ≤ pos) (hc : carry ≤ 1) (hcp : carry = 1 → pos ≤ 254)
    (hinv : S + carry * 2^pos = ((V % 2^pos : ℕ) : ℤ)) : S = V := by
  have hc0 : carry = 0 := by
    by_contra h
    have h1 : carry = 1 := by omega
    have := hcp h1
    omega
  subst hc0
  have hmod : V % 2^pos = V := by
    apply Nat.mod_eq_of_lt
    calc V < 2^253 := hV
      _ ≤ 2^pos := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [hmod] at hinv
  push_cast at hinv
  linarith

end CurveFieldProofs
