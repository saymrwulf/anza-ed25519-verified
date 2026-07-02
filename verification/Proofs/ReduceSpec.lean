/- ──────────────────────────────────────────────────────────────────────────────
   Proofs/ReduceSpec.lean — total-correctness spec of the "weak reduction"

   WHAT THIS FILE CONTAINS
   Spec for the transpiled `FieldElement51::reduce`:
   it never panics, its output limbs are < 2⁵¹ + 19·2¹³ (⊂ 2⁵²), and it
   preserves the value modulo p (exact Nat relation: it subtracts (l4 ≫ 51)·p).
   It also proves two tiny ℕ-level rewrite lemmas (`nat_and_mask`, `nat_shift_div`)
   that turn the hardware bit operations `&&&`/`>>>` into `%`/`/`, the form the
   `omega` decision procedure understands.

   RUST ANALOG
   `FieldElement51::reduce`, curve25519/solana-ed25519/src/backend/serial/u64/field.rs:290-323
   (its local constant `LOW_51_BIT_MASK`, field.rs:291). The transpiled bodies live in
   gen/CurveField/Funs.lean as `backend.serial.u64.field.FieldElement51.reduce` and
   `...reduce.LOW_51_BIT_MASK`.

   THE ALGORITHM (what the Rust does)
   A field element is 5 limbs l0..l4 in radix 2⁵¹:
       feVal l = l0 + l1·2⁵¹ + l2·2¹⁰² + l3·2¹⁵³ + l4·2²⁰⁴.
   `reduce` performs one parallel carry pass ("weak reduction" — it shrinks limbs back
   under ~2⁵¹ but does NOT canonicalize below p):
       c_i := l_i >> 51          (the carry-out of limb i; c_i < 2¹³ since l_i < 2⁶⁴)
       m_i := l_i & (2⁵¹ − 1)    (the low 51 bits, i.e. l_i mod 2⁵¹)
       r0  := m0 + 19·c4,   r_{i+1} := m_{i+1} + c_i   (i = 0..3).
   Each carry c_i moves from weight 2^(51·i)·2⁵¹ = 2^(51·(i+1)) to limb i+1 — except c4,
   whose weight 2²⁵⁵ does not exist in the representation; since 2²⁵⁵ ≡ 19 (mod p) it is
   folded back into limb 0 as 19·c4. The value therefore drops by exactly
   c4·(2²⁵⁵ − 19) = p·(l4 div 2⁵¹), giving the EXACT ℕ accounting proved below:
       feVal r + p·(l4 div 2⁵¹) = feVal l.
   No u64 addition can overflow: m_i < 2⁵¹ and 19·c4 < 19·2¹³, so every output limb is
   < 2⁵¹ + 19·2¹³ < 2⁵² ≪ 2⁶⁴ — this is simultaneously the panic-freedom argument and
   the restored limb-bound invariant `Bnd r (2⁵¹ + 19·2¹³)`.

   ROLE IN THE MAIN THEOREM (Proofs/FieldMain.lean: fieldImplementation)
   `sub` and `negate` (Proofs/SubNegSpec.lean) end with a call to `reduce`; their specs
   compose `reduce_spec` (via the packaged `reduce_make_spec`) with their own limb
   arithmetic. The exact (not merely mod-p) value equation is what lets those callers
   finish their accounting purely over ℕ with `omega` and cast to 𝔽_p only once.
   The `nat_and_mask`/`nat_shift_div` simp lemmas are reused by every carry-chain proof
   (MulSpec, SquareSpec) since `mul`/`pow2k` inline the same mask/shift idiom.

   FILE RELATIONS
   Imports Proofs/Denote.lean (Fe, feVal, limbsVal, Bnd, P). Imported by
   Proofs/SubNegSpec.lean and Proofs/AddSpec.lean, hence (transitively) by everything
   up to Proofs/FieldMain.lean.
   ────────────────────────────────────────────────────────────────────────────── -/
import Proofs.Denote
open Aeneas Aeneas.Std Result
open curve25519

set_option maxHeartbeats 4000000

namespace CurveFieldProofs

/-- The mask constant evaluates to 2⁵¹ − 1.

    Rust: `const LOW_51_BIT_MASK: u64 = (1u64 << 51) - 1;` inside `FieldElement51::reduce`,
    curve25519/solana-ed25519/src/backend/serial/u64/field.rs:291.

    MATH:  reduce.LOW_51_BIT_MASK = ok m  with  m = 2^51 - 1  (= 2251799813685247).

    WHY NEEDED: in the Aeneas model even this constant is a *fallible* computation
    (`1#u64 <<< 51` then `- 1#u64` — each could in principle overflow), so proving the
    field theorem requires proving it succeeds and pinning its value. The `@[step]`
    attribute registers it with the `step` tactic, so the symbolic execution of
    `reduce`'s body picks it up automatically when it reaches the mask read. -/
@[step]
theorem reduce_mask_spec :
    backend.serial.u64.field.FieldElement51.reduce.LOW_51_BIT_MASK
      ⦃ m => m.val = 2^51 - 1 ⦄ := by
  unfold backend.serial.u64.field.FieldElement51.reduce.LOW_51_BIT_MASK
  -- symbolically execute the two machine ops (shift, subtract); no side conditions remain
  step*

/-- Convert `&&& (2^51-1)` and `>>> 51` on `ℕ` to `%`/`/` so `omega` can reason.
    Stated with the *literal* (2251799813685247 = 2⁵¹−1) since simp normalizes
    `2^51 - 1` to it before these lemmas get a chance to fire.

    Rust analog: the expression `x & LOW_51_BIT_MASK` (field.rs:310-314 and the same
    idiom in `mul`/`square`); at the `.val : ℕ` level the U64 bitwise-and becomes ℕ's
    `&&&` (`Nat.land`).

    MATH:  n AND (2^51 - 1) = n mod 2^51   — masking the low 51 bits IS reduction
    mod 2^51 (standard two-power identity `Nat.and_two_pow_sub_one_eq_mod`).

    WHY NEEDED: `omega` (the linear-arithmetic closer of every carry proof) knows
    `/` and `%` but not bitwise ops. Tagging with `@[simp, scalar_tac_simps]` makes
    both `simp_all` and `scalar_tac` eliminate `&&&` on sight, here and in
    MulSpec/SquareSpec. -/
@[simp, scalar_tac_simps]
theorem nat_and_mask (n : ℕ) : n &&& 2251799813685247 = n % 2251799813685248 := by
  have := Nat.and_two_pow_sub_one_eq_mod n 51
  norm_num at this
  simpa using this

/-- Companion to `nat_and_mask` for the right shift.

    Rust analog: the carry extraction `limbs[i] >> 51` (field.rs:304-308 and the same
    idiom in `mul`/`square`).

    MATH:  n >> 51 = n div 2^51   (2251799813685248 = 2⁵¹; `Nat.shiftRight_eq_div_pow`).

    WHY NEEDED: same as `nat_and_mask` — rewrites the hardware shift into the division
    that `omega` can reason about linearly. -/
@[simp, scalar_tac_simps]
theorem nat_shift_div (n : ℕ) : n >>> 51 = n / 2251799813685248 := by
  simp [Nat.shiftRight_eq_div_pow]

/-- `reduce` spec: total (no panic), output bounded, value preserved mod p.

    Rust: `FieldElement51::reduce`,
    curve25519/solana-ed25519/src/backend/serial/u64/field.rs:290-323.

    MATH (note: NO precondition — `reduce` is total on arbitrary u64 limbs):
    ASCII:  forall l : Fe with limbs [l0..l4],
            reduce l = ok r  with  Bnd(r, 2^51 + 19*2^13)
            and  feVal r + p * (l4 div 2^51) = feVal l.
    LaTeX:  $\forall l,\ \exists r,\ \mathrm{reduce}(l) = \mathrm{ok}\ r \wedge
            \mathrm{Bnd}(r, 2^{51} + 19\cdot 2^{13}) \wedge
            \llbracket r\rrbracket_{\mathbb N} + p\lfloor l_4/2^{51}\rfloor
            = \llbracket l\rrbracket_{\mathbb N}$.

    The value clause is EXACT ℕ arithmetic, not a congruence mod p: the only multiple
    of p that `reduce` removes is c4·p where c4 = l4 div 2⁵¹ (the carry out of the top
    limb, folded back as 19·c4 because 2²⁵⁵ ≡ 19 mod p — see the file header). Crucially
    it is stated WITHOUT subtraction (`feVal r + P·c4 = feVal l`, not
    `feVal r = feVal l − P·c4`): ℕ-subtraction truncates at 0 and breaks linear
    reasoning, whereas this purely additive form is a linear Diophantine equation in
    the `%`/`/` terms of the input limbs — exactly the fragment `omega` decides.

    The bound 2⁵¹ + 19·2¹³ is sharp for limb 0 (mask < 2⁵¹ plus 19·c4 with c4 < 2¹³);
    limbs 1–4 satisfy the stronger < 2⁵¹ + 2¹³. Callers weaken it to `Bnd r (2^52)`
    via `Bnd.mono`.

    WHY NEEDED: `sub_spec`/`neg_spec` (SubNegSpec.lean) run `reduce` on their raw
    "a + 16p − b" limbs; this spec provides both their panic-freedom (one conjunct of
    the main theorem's totality claim) and the value bookkeeping that turns into
    ⟪r⟫ = ⟪a⟫ − ⟪b⟫ after the single cast to 𝔽_p. -/
theorem reduce_spec (l : Fe) (l0 l1 l2 l3 l4 : U64)
    (hl : (↑l : List U64) = [l0, l1, l2, l3, l4]) :
    fe_reduce l ⦃ r =>
      Bnd r (2^51 + 19 * 2^13) ∧
      feVal r + P * (l4.val / 2^51) = feVal l ⦄ := by
  -- expose the transpiled monadic body (gen/CurveField/Funs.lean)
  unfold fe_reduce backend.serial.u64.field.FieldElement51.reduce
  -- step*: symbolically execute the whole program, one machine op per step (5 shifts,
  -- 5 masks, the ×19, 5 carry adds, plus the interleaved array reads/writes — ~45 ops).
  -- For each op it applies the registered @[step] spec (U64.add_spec, reduce_mask_spec,
  -- Array.index_usize_spec, ...), names the result, and discharges every overflow /
  -- index-in-bounds side condition with the supplied `by` block:
  --   subst_vars  — substitute the equations of earlier steps,
  --   simp [...]  — evaluate array get-after-set chains,
  --   scalar_tac  — close the remaining linear bound (e.g. mask + 19·carry < 2⁶⁴).
  step* by (subst_vars
            try simp [Array.set_val_eq, *]
            try scalar_tac)
  -- Final postcondition: normalize the set-chain + all value equations to
  -- %/÷ arithmetic over the input limbs (simp_all also uses the inaccessible
  -- step*-generated hypotheses), then close with omega.
  -- After simp_all (which fires nat_and_mask/nat_shift_div) the goal is the pure
  -- linear identity over ℕ:
  --   Σᵢ (lᵢ % 2⁵¹)·2^(51i) + 19·(l4/2⁵¹) + Σᵢ₌₀..₃ (lᵢ/2⁵¹)·2^(51(i+1))
  --     + (2²⁵⁵−19)·(l4/2⁵¹) = Σᵢ lᵢ·2^(51i)
  -- which follows from lᵢ = (lᵢ % 2⁵¹) + 2⁵¹·(lᵢ/2⁵¹); scalar_tac ends in omega.
  simp_all [Array.set_val_eq, P, limbsVal, Bnd, feVal]
  scalar_tac

end CurveFieldProofs
