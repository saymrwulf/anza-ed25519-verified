/- ─────────────────────────────────────────────────────────────────────────────
   Proofs/MulSpec.lean — total correctness of field MULTIPLICATION

   WHAT THIS FILE PROVES (one big theorem, `mul_spec`)

     ASCII:  forall a b : Fe,  Bnd(a, 2^54) and Bnd(b, 2^54)  ==>
             fe_mul a b = ok r   with   Bnd(r, 2^51 + 2^13)
             and  [[r]] = [[a]] * [[b]]   in F_p,  p = 2^255 - 19
     LaTeX:  $\forall a\,b,\ \mathrm{Bnd}(a,2^{54})\wedge\mathrm{Bnd}(b,2^{54})
             \Rightarrow \exists r,\ \mathrm{fe\_mul}\,a\,b = \mathrm{ok}\,r \wedge
             \llbracket r\rrbracket=\llbracket a\rrbracket\cdot\llbracket b\rrbracket$

   Here `Bnd x c` = "all 5 limbs of x are < c" and [[x]] = ⟪x⟫ =
   (x0 + x1·2^51 + x2·2^102 + x3·2^153 + x4·2^204) mod p — both defined in
   Proofs/Denote.lean. "fe_mul a b = ok r" (written `fe_mul a b ⦃ post ⦄`)
   means TOTAL correctness: the Rust code never panics/overflows on such
   inputs, *including* its ten `debug_assert!`s, which Charon keeps as
   `massert` obligations that we must PROVE (they are theorems, not
   assumptions).

   RUST ANALOG
   `impl Mul<&'a FieldElement51> for &FieldElement51 { fn mul }`,
   curve25519/solana-ed25519/src/backend/serial/u64/field.rs:115-213, with its
   nested helper `m` (widening 64×64→128 multiply, field.rs:119), the local
   constant `LOW_51_BIT_MASK = (1u64 << 51) - 1` (field.rs:172) and the ten
   `debug_assert!(limb < 1 << 54)` checks (field.rs:162-166). The mechanical
   Lean model of that code is the generated function
   `Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51.mul`
   in gen/CurveField/Funs.lean, aliased `fe_mul` in Proofs/Denote.lean.

   THE ALGORITHM BEING VERIFIED (radix-2^51 schoolbook multiply, 19-folded)
   Writing A = Sum_i x_i 2^(51 i) and B = Sum_j y_j 2^(51 j), the full product
   is Sum_{i,j} x_i y_j 2^(51(i+j)) — ten powers 2^0 .. 2^(51·8). Because
   2^255 = p + 19, i.e. 2^255 ≡ 19 (mod p), every high term with i+j ≥ 5 is
   folded down: x_i y_j 2^(51(i+j)) ≡ 19 · x_i y_j 2^(51(i+j-5)). The code
   therefore precomputes b1_19 = 19·y1, …, b4_19 = 19·y4 (u64; fits since
   19·2^54 < 2^64) and accumulates five u128 columns (field.rs:144-148):

     c0 = x0·y0 + 19·(x4·y1 + x3·y2 + x2·y3 + x1·y4)
     c1 = x1·y0 + x0·y1 + 19·(x4·y2 + x3·y3 + x2·y4)
     c2 = x2·y0 + x1·y1 + x0·y2 + 19·(x4·y3 + x3·y4)
     c3 = x3·y0 + x2·y1 + x1·y2 + x0·y3 + 19·(x4·y4)
     c4 = x4·y0 + x3·y1 + x2·y2 + x1·y3 + x0·y4

   With limbs < 2^54 each column is < (1+i + 19·(4-i))·2^108 ≤ 77·2^108 < 2^115,
   far below the u128 limit 2^128. Then a single carry pass (field.rs:175-188)
   normalizes: c_{k+1} += c_k >> 51, out[k] = c_k & mask; the final carry
   (multiples of 2^255) re-enters as out[0] += 19·carry (field.rs:205), and one
   mini-carry out[1] += out[0] >> 51; out[0] &= mask (field.rs:208-209) leaves
   all limbs < 2^51 + 2^13.

   PROOF ARCHITECTURE — a fully NAMED machine-checked symbolic execution
   The generated body is a chain of ~95 fallible machine operations in the
   `Result` monad. The script mirrors it step by step:

     let* ⟨ x, x_post ⟩ ← spec_lemma by tac

   is the Aeneas "progress" step: it consumes the next monadic operation,
   applies the registered spec lemma for it (`m_spec`, `U128.add_spec`,
   `Array.index_usize_spec`, …), names the result `x` and its postcondition
   `x_post`, and discharges the lemma's precondition — i.e. the u64/u128
   overflow side condition of that very operation — with the `by tac` block.
   After each step an explicit bound fact `hv_… : ….val < n·2^108` (or an
   identification `he_… : i = x3` of which limb a read returned) is recorded,
   so that every later side condition is LINEAR arithmetic over already-named
   quantities and `omega`/`scalar_tac` close it without nonlinear reasoning.

   The final assembly has three layers:
     (1) hkey  — exact ℕ carry accounting:
                 feVal r + p·carry = c0 + 2^51·c1 + 2^102·c2 + 2^153·c3 + 2^204·c4
                 (pure div/mod bookkeeping of the carry pass; `omega`).
     (2) hnc0–hnc4 — each column c_k as a polynomial in the input limbs
                 (substitute all step postconditions, then `ring`).
     (3) hAB   — the F_p identity A·B = Sum_k c_k·2^(51 k), via
                 `linear_combination D * h255` where h255 : (2:F_p)^255 = 19
                 and D is the explicit wrap-around polynomial
                   D =        (x1·y4 + x2·y3 + x3·y2 + x4·y1)
                     + 2^51 ·(x2·y4 + x3·y3 + x4·y2)
                     + 2^102·(x3·y4 + x4·y3)
                     + 2^153·(x4·y4)
                     = Sum_{i+j ≥ 5} x_i·y_j·2^(51(i+j-5)),
                 because over ℤ:  A·B = Sum_k c_k·2^(51 k) + (2^255 - 19)·D.
   Casting (1) into F_p kills the p·carry term ((p : F_p) = 0) and chaining it
   with (3) yields ⟪r⟫ = ⟪a⟫·⟪b⟫.

   ROLE IN THE MAIN THEOREM (Proofs/FieldMain.lean)
   `mul_spec` is the multiplicative half of `fieldImplementation`: the
   corollaries impl_mul_comm/assoc, impl_one_mul, impl_mul_inv_cancel and
   impl_left_distrib all run `fe_mul` and rest on this theorem.
   Imports: Proofs/SubNegSpec (transitively Denote/ReduceSpec: ⟪·⟫, Bnd,
   two_pow_255_eq) and mathlib's `linear_combination` tactic.
   Dependents: Proofs/SquareSpec.lean (same architecture, reuses the `dis`
   macro), Proofs/InvertSpec.lean (mul steps of the pow22501 chain),
   Proofs/Field.lean and Proofs/FieldMain.lean.

   PROVENANCE: the script was generated by /tmp/gen_mul_proof.py to mirror the
   generated body, then hand-tuned.
   ───────────────────────────────────────────────────────────────────────── -/
import Proofs.SubNegSpec
import Mathlib.Tactic.LinearCombination
open Aeneas Aeneas.Std Result
open curve25519

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace CurveFieldProofs

/-- Discharge tactic shared by most steps: substitute the equations introduced
    so far, simplify array reads/writes (`Array.set_val_eq`) with all
    hypotheses, then run `scalar_tac` (Aeneas's linear-arithmetic decision
    procedure over machine integers). This is what closes each overflow side
    condition once the `hv_*` bound facts have made it linear.
    WHY NEEDED: keeps the ~95 `let*` steps below one-liners. -/
macro "dis" : tactic =>
  `(tactic| (subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac))

/-- The u128 widening product `m(x, y) = (x as u128) * (y as u128)`.

    Rust: nested `fn m(x: u64, y: u64) -> u128`,
    curve25519/solana-ed25519/src/backend/serial/u64/field.rs:119.
    MATH: forall x y : u64, m x y = ok z with z.val = x.val * y.val — the
    product of two u64 is < 2^64 · 2^64 = 2^128, so the u128 multiply that the
    transpiler emits after the two casts can NEVER overflow; this lemma proves
    that once and for all.
    WHY NEEDED: every one of the 25 partial products in `mul` goes through
    `m`; tagging the lemma `@[step]` registers it with the `let*` machinery.  -/
@[step]
theorem m_spec (x y : U64) :
    backend.serial.u64.field.MulShared0FieldElement51SharedAFieldElement51FieldElement51.mul.m
      x y ⦃ z => z.val = x.val * y.val ⦄ := by
  unfold
    backend.serial.u64.field.MulShared0FieldElement51SharedAFieldElement51FieldElement51.mul.m
  -- the two u64 inputs are < 2^64 by construction …
  have hx : x.val < 2^64 := x.hBounds
  have hy : y.val < 2^64 := y.hBounds
  -- … hence the product fits in a u128: the only side condition of the body
  have hxy : x.val * y.val < 2^128 := by
    calc x.val * y.val < 2^64 * 2^64 := Nat.mul_lt_mul'' hx hy
      _ = 2^128 := by norm_num
  -- run the 3 ops (cast, cast, mul); `dis` discharges each side condition
  step* by dis

/-- The mask constant in `mul` evaluates to 2⁵¹ − 1.

    Rust: `const LOW_51_BIT_MASK: u64 = (1u64 << 51) - 1;`,
    curve25519/solana-ed25519/src/backend/serial/u64/field.rs:172.
    MATH: the constant's generated body (shift then subtract) succeeds and
    returns 2251799813685247 = 2^51 - 1. `x & LOW_51_BIT_MASK` is therefore
    `x mod 2^51` — the "keep the low limb" half of every carry step.
    WHY NEEDED: the carry pass reads this constant once; its value must be
    known exactly for the div/mod accounting in `hkey`.                      -/
@[step]
theorem mul_mask_spec :
    backend.serial.u64.field.MulShared0FieldElement51SharedAFieldElement51FieldElement51.mul.LOW_51_BIT_MASK
      ⦃ m => m.val = 2251799813685247 ⦄ := by
  unfold
    backend.serial.u64.field.MulShared0FieldElement51SharedAFieldElement51FieldElement51.mul.LOW_51_BIT_MASK
  step*

/-- Main multiplication theorem (see the file header for the full story).

    Rust: `impl Mul<&FieldElement51> for &FieldElement51 { fn mul }`,
    curve25519/solana-ed25519/src/backend/serial/u64/field.rs:115-213.
    MATH (ASCII):
      Bnd(a,2^54) and Bnd(b,2^54)  ==>  fe_mul a b = ok r
      with Bnd(r, 2^51 + 2^13) and [[r]] = [[a]]·[[b]] in F_p.
    The limb lists [x0..x4] / [y0..y4] are taken as explicit arguments so that
    every intermediate bound can be stated about a NAMED limb.
    WHY NEEDED: sole support of the impl_mul_* field axioms in FieldMain;
    also the workhorse inside InvertSpec's exponentiation chain.            -/
theorem mul_spec (a b : Fe) (x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 : U64)
    (ha : (↑a : List U64) = [x0, x1, x2, x3, x4])
    (hb : (↑b : List U64) = [y0, y1, y2, y3, y4])
    (hba : Bnd a (2^54)) (hbb : Bnd b (2^54)) :
    fe_mul a b ⦃ r => Bnd r (2^51 + 2^13) ∧ ⟪r⟫ = ⟪a⟫ * ⟪b⟫ ⦄ := by
  -- turn the abstract invariants into 5+5 named limb bounds x_i < 2^54, y_i < 2^54
  rw [Bnd_eq a x0 x1 x2 x3 x4 _ ha] at hba
  rw [Bnd_eq b y0 y1 y2 y3 y4 _ hb] at hbb
  -- expose the generated body (fe_mul is a definitional alias)
  unfold fe_mul
    Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51.mul
  -- ── b*_19 precomputations + limb loads (field.rs:138-141) ────────────────
  -- each read `i… = y_j` is identified (he_*) and bounded (hv_*); each
  -- 19·y_j u64 multiply needs 19·2^54 < 2^64 — discharged inside `dis`
  let* ⟨ i, i_post ⟩ ← Array.index_usize_spec by dis
  have he_i : i = y1 := by simp [i_post, hb]
  have hv_i : i.val < 2^54 := by rw [he_i]; omega
  let* ⟨ b1_19, b1_19_post ⟩ ← U64.mul_spec by dis
  have hv_b1_19 : b1_19.val < 19 * 2^54 := by rw [b1_19_post]; omega
  let* ⟨ i1, i1_post ⟩ ← Array.index_usize_spec by dis
  have he_i1 : i1 = y2 := by simp [i1_post, hb]
  have hv_i1 : i1.val < 2^54 := by rw [he_i1]; omega
  let* ⟨ b2_19, b2_19_post ⟩ ← U64.mul_spec by dis
  have hv_b2_19 : b2_19.val < 19 * 2^54 := by rw [b2_19_post]; omega
  let* ⟨ i2, i2_post ⟩ ← Array.index_usize_spec by dis
  have he_i2 : i2 = y3 := by simp [i2_post, hb]
  have hv_i2 : i2.val < 2^54 := by rw [he_i2]; omega
  let* ⟨ b3_19, b3_19_post ⟩ ← U64.mul_spec by dis
  have hv_b3_19 : b3_19.val < 19 * 2^54 := by rw [b3_19_post]; omega
  let* ⟨ i3, i3_post ⟩ ← Array.index_usize_spec by dis
  have he_i3 : i3 = y4 := by simp [i3_post, hb]
  have hv_i3 : i3.val < 2^54 := by rw [he_i3]; omega
  let* ⟨ b4_19, b4_19_post ⟩ ← U64.mul_spec by dis
  have hv_b4_19 : b4_19.val < 19 * 2^54 := by rw [b4_19_post]; omega
  let* ⟨ i4, i4_post ⟩ ← Array.index_usize_spec by dis
  have he_i4 : i4 = x0 := by simp [i4_post, ha]
  have hv_i4 : i4.val < 2^54 := by rw [he_i4]; omega
  let* ⟨ i5, i5_post ⟩ ← Array.index_usize_spec by dis
  have he_i5 : i5 = y0 := by simp [i5_post, hb]
  have hv_i5 : i5.val < 2^54 := by rw [he_i5]; omega
  -- ── column c0 = a0*b0 + 19*(a4*b1 + a3*b2 + a2*b3 + a1*b4) (field.rs:144) ─
  -- each `m` product is < 2^108 (or < 19·2^108 when one factor is a b*_19);
  -- the running u128 sums stay < 77·2^108 < 2^128, so each add is in range
  let* ⟨ i6, i6_post ⟩ ← m_spec by dis
  have hv_i6 : i6.val < 2^108 := by
    rw [i6_post]; have := Nat.mul_lt_mul'' hv_i4 hv_i5; omega
  let* ⟨ i7, i7_post ⟩ ← Array.index_usize_spec by dis
  have he_i7 : i7 = x4 := by simp [i7_post, ha]
  have hv_i7 : i7.val < 2^54 := by rw [he_i7]; omega
  let* ⟨ i8, i8_post ⟩ ← m_spec by dis
  have hv_i8 : i8.val < 2^54 * (19 * 2^54) := by
    rw [i8_post]; have := Nat.mul_lt_mul'' hv_i7 hv_b1_19; omega
  let* ⟨ i9, i9_post ⟩ ← U128.add_spec by scalar_tac
  have hv_i9 : i9.val < 20 * 2^108 := by rw [i9_post]; omega
  let* ⟨ i10, i10_post ⟩ ← Array.index_usize_spec by dis
  have he_i10 : i10 = x3 := by simp [i10_post, ha]
  have hv_i10 : i10.val < 2^54 := by rw [he_i10]; omega
  let* ⟨ i11, i11_post ⟩ ← m_spec by dis
  have hv_i11 : i11.val < 2^54 * (19 * 2^54) := by
    rw [i11_post]; have := Nat.mul_lt_mul'' hv_i10 hv_b2_19; omega
  let* ⟨ i12, i12_post ⟩ ← U128.add_spec by scalar_tac
  have hv_i12 : i12.val < 39 * 2^108 := by rw [i12_post]; omega
  let* ⟨ i13, i13_post ⟩ ← Array.index_usize_spec by dis
  have he_i13 : i13 = x2 := by simp [i13_post, ha]
  have hv_i13 : i13.val < 2^54 := by rw [he_i13]; omega
  let* ⟨ i14, i14_post ⟩ ← m_spec by dis
  have hv_i14 : i14.val < 2^54 * (19 * 2^54) := by
    rw [i14_post]; have := Nat.mul_lt_mul'' hv_i13 hv_b3_19; omega
  let* ⟨ i15, i15_post ⟩ ← U128.add_spec by scalar_tac
  have hv_i15 : i15.val < 58 * 2^108 := by rw [i15_post]; omega
  let* ⟨ i16, i16_post ⟩ ← Array.index_usize_spec by dis
  have he_i16 : i16 = x1 := by simp [i16_post, ha]
  have hv_i16 : i16.val < 2^54 := by rw [he_i16]; omega
  let* ⟨ i17, i17_post ⟩ ← m_spec by dis
  have hv_i17 : i17.val < 2^54 * (19 * 2^54) := by
    rw [i17_post]; have := Nat.mul_lt_mul'' hv_i16 hv_b4_19; omega
  let* ⟨ c0, c0_post ⟩ ← U128.add_spec by scalar_tac
  have hv_c0 : c0.val < 77 * 2^108 := by rw [c0_post]; omega
  -- ── column c1 = a1*b0 + a0*b1 + 19*(a4*b2 + a3*b3 + a2*b4) (field.rs:145) ─
  let* ⟨ i18, i18_post ⟩ ← m_spec by dis
  have hv_i18 : i18.val < 2^108 := by
    rw [i18_post]; have := Nat.mul_lt_mul'' hv_i16 hv_i5; omega
  let* ⟨ i19, i19_post ⟩ ← m_spec by dis
  have hv_i19 : i19.val < 2^108 := by
    rw [i19_post]; have := Nat.mul_lt_mul'' hv_i4 hv_i; omega
  let* ⟨ i20, i20_post ⟩ ← U128.add_spec by scalar_tac
  have hv_i20 : i20.val < 2 * 2^108 := by rw [i20_post]; omega
  let* ⟨ i21, i21_post ⟩ ← m_spec by dis
  have hv_i21 : i21.val < 2^54 * (19 * 2^54) := by
    rw [i21_post]; have := Nat.mul_lt_mul'' hv_i7 hv_b2_19; omega
  let* ⟨ i22, i22_post ⟩ ← U128.add_spec by scalar_tac
  have hv_i22 : i22.val < 21 * 2^108 := by rw [i22_post]; omega
  let* ⟨ i23, i23_post ⟩ ← m_spec by dis
  have hv_i23 : i23.val < 2^54 * (19 * 2^54) := by
    rw [i23_post]; have := Nat.mul_lt_mul'' hv_i10 hv_b3_19; omega
  let* ⟨ i24, i24_post ⟩ ← U128.add_spec by scalar_tac
  have hv_i24 : i24.val < 40 * 2^108 := by rw [i24_post]; omega
  let* ⟨ i25, i25_post ⟩ ← m_spec by dis
  have hv_i25 : i25.val < 2^54 * (19 * 2^54) := by
    rw [i25_post]; have := Nat.mul_lt_mul'' hv_i13 hv_b4_19; omega
  let* ⟨ c1, c1_post ⟩ ← U128.add_spec by scalar_tac
  have hv_c1 : c1.val < 59 * 2^108 := by rw [c1_post]; omega
  -- ── column c2 = a2*b0 + a1*b1 + a0*b2 + 19*(a4*b3 + a3*b4) (field.rs:146) ─
  let* ⟨ i26, i26_post ⟩ ← m_spec by dis
  have hv_i26 : i26.val < 2^108 := by
    rw [i26_post]; have := Nat.mul_lt_mul'' hv_i13 hv_i5; omega
  let* ⟨ i27, i27_post ⟩ ← m_spec by dis
  have hv_i27 : i27.val < 2^108 := by
    rw [i27_post]; have := Nat.mul_lt_mul'' hv_i16 hv_i; omega
  let* ⟨ i28, i28_post ⟩ ← U128.add_spec by scalar_tac
  have hv_i28 : i28.val < 2 * 2^108 := by rw [i28_post]; omega
  let* ⟨ i29, i29_post ⟩ ← m_spec by dis
  have hv_i29 : i29.val < 2^108 := by
    rw [i29_post]; have := Nat.mul_lt_mul'' hv_i4 hv_i1; omega
  let* ⟨ i30, i30_post ⟩ ← U128.add_spec by scalar_tac
  have hv_i30 : i30.val < 3 * 2^108 := by rw [i30_post]; omega
  let* ⟨ i31, i31_post ⟩ ← m_spec by dis
  have hv_i31 : i31.val < 2^54 * (19 * 2^54) := by
    rw [i31_post]; have := Nat.mul_lt_mul'' hv_i7 hv_b3_19; omega
  let* ⟨ i32, i32_post ⟩ ← U128.add_spec by scalar_tac
  have hv_i32 : i32.val < 22 * 2^108 := by rw [i32_post]; omega
  let* ⟨ i33, i33_post ⟩ ← m_spec by dis
  have hv_i33 : i33.val < 2^54 * (19 * 2^54) := by
    rw [i33_post]; have := Nat.mul_lt_mul'' hv_i10 hv_b4_19; omega
  let* ⟨ c2, c2_post ⟩ ← U128.add_spec by scalar_tac
  have hv_c2 : c2.val < 41 * 2^108 := by rw [c2_post]; omega
  -- ── column c3 = a3*b0 + a2*b1 + a1*b2 + a0*b3 + 19*a4*b4 (field.rs:147) ──
  let* ⟨ i34, i34_post ⟩ ← m_spec by dis
  have hv_i34 : i34.val < 2^108 := by
    rw [i34_post]; have := Nat.mul_lt_mul'' hv_i10 hv_i5; omega
  let* ⟨ i35, i35_post ⟩ ← m_spec by dis
  have hv_i35 : i35.val < 2^108 := by
    rw [i35_post]; have := Nat.mul_lt_mul'' hv_i13 hv_i; omega
  let* ⟨ i36, i36_post ⟩ ← U128.add_spec by scalar_tac
  have hv_i36 : i36.val < 2 * 2^108 := by rw [i36_post]; omega
  let* ⟨ i37, i37_post ⟩ ← m_spec by dis
  have hv_i37 : i37.val < 2^108 := by
    rw [i37_post]; have := Nat.mul_lt_mul'' hv_i16 hv_i1; omega
  let* ⟨ i38, i38_post ⟩ ← U128.add_spec by scalar_tac
  have hv_i38 : i38.val < 3 * 2^108 := by rw [i38_post]; omega
  let* ⟨ i39, i39_post ⟩ ← m_spec by dis
  have hv_i39 : i39.val < 2^108 := by
    rw [i39_post]; have := Nat.mul_lt_mul'' hv_i4 hv_i2; omega
  let* ⟨ i40, i40_post ⟩ ← U128.add_spec by scalar_tac
  have hv_i40 : i40.val < 4 * 2^108 := by rw [i40_post]; omega
  let* ⟨ i41, i41_post ⟩ ← m_spec by dis
  have hv_i41 : i41.val < 2^54 * (19 * 2^54) := by
    rw [i41_post]; have := Nat.mul_lt_mul'' hv_i7 hv_b4_19; omega
  let* ⟨ c3, c3_post ⟩ ← U128.add_spec by scalar_tac
  have hv_c3 : c3.val < 23 * 2^108 := by rw [c3_post]; omega
  -- ── column c4 = a4*b0 + a3*b1 + a2*b2 + a1*b3 + a0*b4 (field.rs:148) ─────
  -- no 19-folding here: i+j = 4 never wraps past 2^255
  let* ⟨ i42, i42_post ⟩ ← m_spec by dis
  have hv_i42 : i42.val < 2^108 := by
    rw [i42_post]; have := Nat.mul_lt_mul'' hv_i7 hv_i5; omega
  let* ⟨ i43, i43_post ⟩ ← m_spec by dis
  have hv_i43 : i43.val < 2^108 := by
    rw [i43_post]; have := Nat.mul_lt_mul'' hv_i10 hv_i; omega
  let* ⟨ i44, i44_post ⟩ ← U128.add_spec by scalar_tac
  have hv_i44 : i44.val < 2 * 2^108 := by rw [i44_post]; omega
  let* ⟨ i45, i45_post ⟩ ← m_spec by dis
  have hv_i45 : i45.val < 2^108 := by
    rw [i45_post]; have := Nat.mul_lt_mul'' hv_i13 hv_i1; omega
  let* ⟨ i46, i46_post ⟩ ← U128.add_spec by scalar_tac
  have hv_i46 : i46.val < 3 * 2^108 := by rw [i46_post]; omega
  let* ⟨ i47, i47_post ⟩ ← m_spec by dis
  have hv_i47 : i47.val < 2^108 := by
    rw [i47_post]; have := Nat.mul_lt_mul'' hv_i16 hv_i2; omega
  let* ⟨ i48, i48_post ⟩ ← U128.add_spec by scalar_tac
  have hv_i48 : i48.val < 4 * 2^108 := by rw [i48_post]; omega
  let* ⟨ i49, i49_post ⟩ ← m_spec by dis
  have hv_i49 : i49.val < 2^108 := by
    rw [i49_post]; have := Nat.mul_lt_mul'' hv_i4 hv_i3; omega
  let* ⟨ c4, c4_post ⟩ ← U128.add_spec by scalar_tac
  have hv_c4 : c4.val < 5 * 2^108 := by rw [c4_post]; omega
  -- ── the ten debug_assert!(limb < 2^54) (field.rs:162-166) ────────────────
  -- Rust debug_assert! survives translation as `massert`; `massert_spec`
  -- requires us to PROVE each asserted bound (from hba/hbb via scalar_tac) —
  -- the asserts are verified, not assumed. i50 evaluates `1 << 54` = 2^54.
  let* ⟨ i50, i50_post1, i50_post2 ⟩ ← U64.ShiftLeft_IScalar_spec by dis
  have hv_i50 : i50.val = 2^54 := by
    rw [i50_post1]; simp [Nat.shiftLeft_eq, U64.size, U64.numBits]
  let* ⟨ _ ⟩ ← massert_spec by scalar_tac
  let* ⟨ _ ⟩ ← massert_spec by scalar_tac
  let* ⟨ _ ⟩ ← massert_spec by scalar_tac
  let* ⟨ _ ⟩ ← massert_spec by scalar_tac
  let* ⟨ _ ⟩ ← massert_spec by scalar_tac
  let* ⟨ _ ⟩ ← massert_spec by scalar_tac
  let* ⟨ _ ⟩ ← massert_spec by scalar_tac
  let* ⟨ _ ⟩ ← massert_spec by scalar_tac
  let* ⟨ _ ⟩ ← massert_spec by scalar_tac
  let* ⟨ _ ⟩ ← massert_spec by scalar_tac
  -- ── carry pass (field.rs:175-188). Pattern per limb k:
  --    c_{k+1} += (c_k >> 51) as u64 as u128;  out[k] = (c_k as u64) & mask.
  -- The u128→u64→u128 cast round-trip is lossless exactly because
  -- c_k/2^51 < 77·2^57 < 2^64 — that is what each hv_* div fact certifies. ──
  -- carry c0 -> c11; limb 0
  let* ⟨ i51, i51_post1, i51_post2 ⟩ ← U128.ShiftRight_IScalar_spec by dis
  let* ⟨ i52, i52_post ⟩ ← UScalar.cast.step_spec by scalar_tac
  let* ⟨ i53, i53_post ⟩ ← UScalar.cast.step_spec by scalar_tac
  have hv_i53 : i53.val = c0.val / 2^51 := by
    simp [i53_post, i52_post, i51_post1, UScalar.cast_val_eq, U64.size, U128.size]; omega
  let* ⟨ c11, c11_post ⟩ ← U128.add_spec by scalar_tac
  have hv_c11 : c11.val < 60 * 2^108 := by
    rw [c11_post]; omega
  let* ⟨ i54, i54_post ⟩ ← UScalar.cast.step_spec by scalar_tac
  let* ⟨ i55, i55_post ⟩ ← mul_mask_spec by dis
  let* ⟨ i56, i56_post1, i56_post2 ⟩ ← UScalar.and_spec by scalar_tac
  have hv_i56 : i56.val = c0.val % 2^51 := by
    simp [i56_post1, i54_post, i55_post, UScalar.cast_val_eq, U64.size, U128.size]
  let* ⟨ out1, out1_post ⟩ ← Array.update_spec by scalar_tac
  -- carry c11 -> c21; limb 1
  let* ⟨ i57, i57_post1, i57_post2 ⟩ ← U128.ShiftRight_IScalar_spec by dis
  let* ⟨ i58, i58_post ⟩ ← UScalar.cast.step_spec by scalar_tac
  let* ⟨ i59, i59_post ⟩ ← UScalar.cast.step_spec by scalar_tac
  have hv_i59 : i59.val = c11.val / 2^51 := by
    simp [i59_post, i58_post, i57_post1, UScalar.cast_val_eq, U64.size, U128.size]; omega
  let* ⟨ c21, c21_post ⟩ ← U128.add_spec by scalar_tac
  have hv_c21 : c21.val < 42 * 2^108 := by
    rw [c21_post]; omega
  let* ⟨ i60, i60_post ⟩ ← UScalar.cast.step_spec by scalar_tac
  let* ⟨ i61, i61_post1, i61_post2 ⟩ ← UScalar.and_spec by scalar_tac
  have hv_i61 : i61.val = c11.val % 2^51 := by
    simp [i61_post1, i60_post, i55_post, UScalar.cast_val_eq, U64.size, U128.size]
  let* ⟨ out2, out2_post ⟩ ← Array.update_spec by scalar_tac
  -- carry c21 -> c31; limb 2
  let* ⟨ i62, i62_post1, i62_post2 ⟩ ← U128.ShiftRight_IScalar_spec by dis
  let* ⟨ i63, i63_post ⟩ ← UScalar.cast.step_spec by scalar_tac
  let* ⟨ i64, i64_post ⟩ ← UScalar.cast.step_spec by scalar_tac
  have hv_i64 : i64.val = c21.val / 2^51 := by
    simp [i64_post, i63_post, i62_post1, UScalar.cast_val_eq, U64.size, U128.size]; omega
  let* ⟨ c31, c31_post ⟩ ← U128.add_spec by scalar_tac
  have hv_c31 : c31.val < 24 * 2^108 := by
    rw [c31_post]; omega
  let* ⟨ i65, i65_post ⟩ ← UScalar.cast.step_spec by scalar_tac
  let* ⟨ i66, i66_post1, i66_post2 ⟩ ← UScalar.and_spec by scalar_tac
  have hv_i66 : i66.val = c21.val % 2^51 := by
    simp [i66_post1, i65_post, i55_post, UScalar.cast_val_eq, U64.size, U128.size]
  let* ⟨ out3, out3_post ⟩ ← Array.update_spec by scalar_tac
  -- carry c31 -> c41; limb 3
  let* ⟨ i67, i67_post1, i67_post2 ⟩ ← U128.ShiftRight_IScalar_spec by dis
  let* ⟨ i68, i68_post ⟩ ← UScalar.cast.step_spec by scalar_tac
  let* ⟨ i69, i69_post ⟩ ← UScalar.cast.step_spec by scalar_tac
  have hv_i69 : i69.val = c31.val / 2^51 := by
    simp [i69_post, i68_post, i67_post1, UScalar.cast_val_eq, U64.size, U128.size]; omega
  let* ⟨ c41, c41_post ⟩ ← U128.add_spec by scalar_tac
  have hv_c41 : c41.val < 6 * 2^108 := by
    rw [c41_post]; omega
  let* ⟨ i70, i70_post ⟩ ← UScalar.cast.step_spec by scalar_tac
  let* ⟨ i71, i71_post1, i71_post2 ⟩ ← UScalar.and_spec by scalar_tac
  have hv_i71 : i71.val = c31.val % 2^51 := by
    simp [i71_post1, i70_post, i55_post, UScalar.cast_val_eq, U64.size, U128.size]
  let* ⟨ out4, out4_post ⟩ ← Array.update_spec by scalar_tac
  -- last limb: carry out of c41 (field.rs:187-188); carry counts 2^255-units
  let* ⟨ i72, i72_post1, i72_post2 ⟩ ← U128.ShiftRight_IScalar_spec by dis
  let* ⟨ carry, carry_post ⟩ ← UScalar.cast.step_spec by scalar_tac
  have hv_carry : carry.val = c41.val / 2^51 := by
    simp [carry_post, i72_post1, UScalar.cast_val_eq, U64.size, U128.size]; omega
  let* ⟨ i73, i73_post ⟩ ← UScalar.cast.step_spec by scalar_tac
  let* ⟨ i74, i74_post1, i74_post2 ⟩ ← UScalar.and_spec by scalar_tac
  have hv_i74 : i74.val = c41.val % 2^51 := by
    simp [i74_post1, i73_post, i55_post, UScalar.cast_val_eq, U64.size, U128.size]
  let* ⟨ out5, out5_post ⟩ ← Array.update_spec by scalar_tac
  -- ── fold the final carry * 19 into limb 0 (field.rs:205, since 2^255 ≡ 19),
  --    then the mini-carry into limb 1 (field.rs:208-209).
  --    No overflow: carry < 6·2^57, so 19·carry < 2^62 and
  --    out[0] + 19·carry < 2^51 + 2^62 < 2^64. ─────────────────────────────
  let* ⟨ i75, i75_post ⟩ ← U64.mul_spec by scalar_tac
  let* ⟨ i76, i76_post ⟩ ← Array.index_usize_spec by scalar_tac
  have hv_i76 : i76.val = c0.val % 2^51 := by
    simp [i76_post, out5_post, out4_post, out3_post, out2_post, out1_post,
          Array.set_val_eq, hv_i56]
  let* ⟨ i77, i77_post ⟩ ← U64.add_spec by scalar_tac
  let* ⟨ out6, out6_post ⟩ ← Array.update_spec by scalar_tac
  let* ⟨ i78, i78_post ⟩ ← Array.index_usize_spec by scalar_tac
  have hv_i78 : i78.val = i77.val := by
    simp [i78_post, out6_post, out5_post, out4_post, out3_post, out2_post,
          out1_post, Array.set_val_eq]
  let* ⟨ i79, i79_post1, i79_post2 ⟩ ← U64.ShiftRight_IScalar_spec by scalar_tac
  let* ⟨ i80, i80_post ⟩ ← Array.index_usize_spec by scalar_tac
  have hv_i80 : i80.val = c11.val % 2^51 := by
    simp [i80_post, out6_post, out5_post, out4_post, out3_post, out2_post,
          out1_post, Array.set_val_eq, hv_i61]
  let* ⟨ i81, i81_post ⟩ ← U64.add_spec by scalar_tac
  let* ⟨ out7, out7_post ⟩ ← Array.update_spec by scalar_tac
  let* ⟨ i82, i82_post ⟩ ← Array.index_usize_spec by scalar_tac
  have hv_i82 : i82.val = i77.val := by
    simp [i82_post, out7_post, out6_post, out5_post, out4_post, out3_post,
          out2_post, out1_post, Array.set_val_eq]
  let* ⟨ i83, i83_post1, i83_post2 ⟩ ← UScalar.and_spec by scalar_tac
  have hv_i83 : i83.val = i77.val % 2^51 := by
    simp [i83_post1, hv_i82, i55_post, UScalar.cast_val_eq, U64.size, U128.size]
  let* ⟨ out8, out8_post ⟩ ← Array.update_spec by scalar_tac
  -- ── symbolic execution done; assemble the postcondition ──────────────────
  -- the result limb list: r = [i77 mod 2^51, (c11 mod 2^51) + i77/2^51,
  --                            c21 mod 2^51, c31 mod 2^51, c41 mod 2^51]
  have hout : (↑out8 : List U64) = [i83, i81, i66, i71, i74] := by
    simp [out8_post, out7_post, out6_post, out5_post, out4_post, out3_post,
          out2_post, out1_post, Array.set_val_eq, Array.repeat_val,
          List.replicate_succ]
  have hv_i79 : i79.val = i77.val / 2^51 := by
    simp [i79_post1, hv_i78]
  -- output bound Bnd r (2^51 + 2^13): four limbs are `mod 2^51` < 2^51, and
  -- limb 1 = (c11 mod 2^51) + i77/2^51 < 2^51 + 2^13 since i77 < 2^51 + 19·6·2^57
  refine ⟨(Bnd_eq _ _ _ _ _ _ _ hout).mpr
    ⟨by omega, by omega, by omega, by omega, by omega⟩, ?_⟩
  -- ── layer (1): exact ℕ accounting of the carry pass ──────────────────────
  -- feVal r + p·carry = Σ_k c_k·2^(51k): the chain shifted out carry·2^255
  -- and re-injected 19·carry, a net difference of exactly (2^255-19)·carry = p·carry.
  -- Pure div/mod arithmetic on the named facts — omega closes it.
  have hkey : feVal out8 + P * carry.val
      = c0.val + 2^51*c1.val + 2^102*c2.val + 2^153*c3.val + 2^204*c4.val := by
    rw [feVal_eq _ _ _ _ _ _ hout]; simp only [limbsVal, P]; omega
  -- ── layer (2): ℕ product expansions of the five columns ──────────────────
  -- substitute every step postcondition, then `ring` rearranges to the
  -- schoolbook column polynomial in the input limbs x_i, y_j
  have hnc0 : c0.val = x0.val*y0.val + 19*(x4.val*y1.val + x3.val*y2.val + x2.val*y3.val + x1.val*y4.val) := by
    simp only [c0_post, i15_post, i12_post, i9_post, i6_post, i8_post, i11_post, i14_post, i17_post, b1_19_post, b2_19_post, b3_19_post, b4_19_post,
              he_i, he_i1, he_i2, he_i3, he_i4, he_i5, he_i7, he_i10,
              he_i13, he_i16]
    ring
  have hnc1 : c1.val = x1.val*y0.val + x0.val*y1.val + 19*(x4.val*y2.val + x3.val*y3.val + x2.val*y4.val) := by
    simp only [c1_post, i24_post, i22_post, i20_post, i18_post, i19_post, i21_post, i23_post, i25_post, b2_19_post, b3_19_post, b4_19_post,
              he_i, he_i1, he_i2, he_i3, he_i4, he_i5, he_i7, he_i10,
              he_i13, he_i16]
    ring
  have hnc2 : c2.val = x2.val*y0.val + x1.val*y1.val + x0.val*y2.val + 19*(x4.val*y3.val + x3.val*y4.val) := by
    simp only [c2_post, i32_post, i30_post, i28_post, i26_post, i27_post, i29_post, i31_post, i33_post, b3_19_post, b4_19_post,
              he_i, he_i1, he_i2, he_i3, he_i4, he_i5, he_i7, he_i10,
              he_i13, he_i16]
    ring
  have hnc3 : c3.val = x3.val*y0.val + x2.val*y1.val + x1.val*y2.val + x0.val*y3.val + 19*(x4.val*y4.val) := by
    simp only [c3_post, i40_post, i38_post, i36_post, i34_post, i35_post, i37_post, i39_post, i41_post, b4_19_post,
              he_i, he_i1, he_i2, he_i3, he_i4, he_i5, he_i7, he_i10,
              he_i13, he_i16]
    ring
  have hnc4 : c4.val = x4.val*y0.val + x3.val*y1.val + x2.val*y2.val + x1.val*y3.val + x0.val*y4.val := by
    simp only [c4_post, i48_post, i46_post, i44_post, i42_post, i43_post, i45_post, i47_post, i49_post,
              he_i, he_i1, he_i2, he_i3, he_i4, he_i5, he_i7, he_i10,
              he_i13, he_i16]
    -- c4 needs no 19-rearrangement; `try ring` closes (or no-ops) the goal
    try ring
  -- ── layer (3): 𝔽_p bridge: A·B = Σ cᵢ·2⁵¹ⁱ using 2²⁵⁵ = 19 ───────────────
  -- h255 : (2 : F_p)^255 = 19, cast from two_pow_255_eq (Proofs/Denote.lean)
  have h255 : (2:Fp)^255 = 19 := by
    have h := two_pow_255_eq; push_cast at h; simpa using h
  -- over ℤ: A·B − Σ c_k·2^(51k) = (2^255 − 19)·D with the wrap-around poly
  --   D = Σ_{i+j≥5} x_i·y_j·2^(51(i+j−5))  (spelled out literally below);
  -- `linear_combination D * h255` asks `ring` to certify exactly that identity
  have hAB : ((feVal a : ℕ) : Fp) * ((feVal b : ℕ) : Fp)
      = ((c0.val : ℕ) : Fp) + 2^51*(c1.val : ℕ) + 2^102*(c2.val : ℕ)
        + 2^153*(c3.val : ℕ) + 2^204*(c4.val : ℕ) := by
    rw [feVal_eq a x0 x1 x2 x3 x4 ha, feVal_eq b y0 y1 y2 y3 y4 hb]
    simp only [limbsVal, hnc0, hnc1, hnc2, hnc3, hnc4]
    push_cast
    linear_combination ((x1.val:Fp)*(y4.val:Fp) + (x2.val:Fp)*(y3.val:Fp)
      + (x3.val:Fp)*(y2.val:Fp) + (x4.val:Fp)*(y1.val:Fp)
      + 2^51*((x2.val:Fp)*(y4.val:Fp) + (x3.val:Fp)*(y3.val:Fp) + (x4.val:Fp)*(y2.val:Fp))
      + 2^102*((x3.val:Fp)*(y4.val:Fp) + (x4.val:Fp)*(y3.val:Fp))
      + 2^153*((x4.val:Fp)*(y4.val:Fp))) * h255
  -- ── conclude: cast layer (1) into F_p, where (p : F_p) = 0 kills p·carry,
  --    then chain with layer (3): ⟪r⟫ = Σ c_k·2^(51k) = ⟪a⟫·⟪b⟫ ─────────────
  have hc := congrArg (Nat.cast : ℕ → Fp) hkey
  push_cast at hc
  have hp0 : ((P : ℕ) : Fp) = 0 := ZMod.natCast_self P
  rw [hp0] at hc
  simp only [zero_mul, add_zero] at hc
  simp only [denote]
  linear_combination hc - hAB

end CurveFieldProofs
