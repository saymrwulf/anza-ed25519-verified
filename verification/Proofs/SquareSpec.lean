/- ─────────────────────────────────────────────────────────────────────────────
   Proofs/SquareSpec.lean — total correctness of SQUARING: `pow2k` and `square`

   WHAT THIS FILE PROVES
     `pow2k_spec`  (k ≥ 1):
       ASCII:  Bnd(a, 2^54)  ==>  fe_pow2k a k = ok r  with
               Bnd(r, 2^51 + 2^13)  and  [[r]] = [[a]] ^ (2^k)  in F_p
       LaTeX:  $\mathrm{Bnd}(a,2^{54}) \wedge k\ge 1 \Rightarrow
               \llbracket \mathrm{pow2k}(a,k)\rrbracket
               = \llbracket a\rrbracket^{2^k}$
     `square_spec`:
       ASCII:  Bnd(a, 2^54)  ==>  fe_square a = ok r  with
               Bnd(r, 2^51 + 2^13)  and  [[r]] = [[a]] * [[a]]
   where Bnd/[[·]] = ⟪·⟫ are the invariant and denotation of Proofs/Denote.lean
   and p = 2^255 - 19. As everywhere, `f x ⦃ post ⦄` is TOTAL correctness:
   no panic/overflow, including the Rust `debug_assert!`s, which Charon keeps
   as `massert` obligations that we must PROVE.

   RUST ANALOG
   `FieldElement51::pow2k`, curve25519/solana-ed25519/src/backend/serial/u64/
   field.rs:454-559 (helper `m`: 460-462; `LOW_51_BIT_MASK`: 511;
   `debug_assert!(k > 0)`: 456; the five `debug_assert!(a[i] < 1 << 54)`:
   505-509), and `FieldElement51::square` = `self.pow2k(1)`, field.rs:562-564.
   Charon splits the Rust `loop { … }` (field.rs:466-556) into two generated
   items in gen/CurveField/Funs.lean:
     * `…FieldElement51.pow2k_loop.body (k, a)` — ONE iteration, returning a
       `ControlFlow` value: `.done r` models `break` (the `if k == 0 { break }`
       after `k -= 1`), `.cont (k1, r)` models falling through to the next
       iteration with the decremented counter k1 and the squared limbs r;
     * `…FieldElement51.pow2k_loop` — `Aeneas.Std.loop` applied to that body.
   `fe_pow2k` / `fe_square` are the aliases from Proofs/Denote.lean.

   THE ALGORITHM (one loop iteration = one radix-2^51 squaring, 19-folded)
   Squaring specializes the schoolbook multiply of Proofs/MulSpec.lean: by the
   symmetry x_i·x_j = x_j·x_i, cross products are computed once and doubled,
   and the wrap-around 2^255 ≡ 19 (mod p) folds high columns down. With
   a3_19 = 19·x3 and a4_19 = 19·x4 precomputed in u64 (field.rs:480-481), the
   five u128 columns (field.rs:488-492) are
     c0 = x0·x0 + 2·(x1·a4_19 + x2·a3_19)  = x0² + 38·x1·x4 + 38·x2·x3
     c1 = x3·a3_19 + 2·(x0·x1 + x2·a4_19)  = 19·x3² + 2·x0·x1 + 38·x2·x4
     c2 = x1·x1 + 2·(x0·x2 + x4·a3_19)     = x1² + 2·x0·x2 + 38·x3·x4
     c3 = x4·a4_19 + 2·(x0·x3 + x1·x2)     = 19·x4² + 2·x0·x3 + 2·x1·x2
     c4 = x2·x2 + 2·(x0·x4 + x1·x3)        = x2² + 2·x0·x4 + 2·x1·x3
   followed by exactly the same carry pass as `mul` (field.rs:515-548):
   c_{k+1} += c_k >> 51, a[k] = c_k & mask, the final carry re-enters as
   a[0] += 19·carry, one mini-carry into a[1], leaving all limbs < 2^51 + 2^13.

   PROOF ARCHITECTURE
   `pow2k_body_spec` mirrors Proofs/MulSpec.lean line by line: a fully NAMED
   symbolic execution (`let* ⟨ x, x_post ⟩ ← spec_lemma by tac` consumes one
   machine op, names its result and postcondition, and discharges its overflow
   side condition), interleaved with explicit bound facts `hv_*` so every side
   condition is LINEAR for `omega`/`scalar_tac`. The same three-layer final
   assembly applies:
     (1) hkey  — exact ℕ carry accounting:
                 feVal r + p·carry = Σ_k c_k·2^(51 k);
     (2) hnc0–hnc4 — each column c_k as a polynomial in x0..x4 (`ring`);
     (3) hAA   — the F_p identity A·A = Σ_k c_k·2^(51 k) via
                 `linear_combination D * h255`, h255 : (2:F_p)^255 = 19, with
                 the squaring wrap-around polynomial
                   D =        2·x1·x4 + 2·x2·x3
                     + 2^51 ·(2·x2·x4 + x3·x3)
                     + 2^102·(2·x3·x4)
                     + 2^153·(x4·x4)
                     = Sum_{i+j ≥ 5} x_i·x_j·2^(51(i+j-5)),
                 because over ℤ:  A·A = Sum_k c_k·2^(51 k) + (2^255 - 19)·D.

   On top of the body spec, the LOOP is handled by fuel induction
   (`pow2k_loop_spec_aux`): `Aeneas.Std.loop` carries no termination measure,
   so we induct on an external bound n ≥ k, peeling one iteration per step
   with `loop_step` (Proofs/AddSpec.lean). Each iteration squares the value
   and decrements k, so k iterations compute ((a²)²…)² = a^(2^k); the output
   bound 2^51 + 2^13 ≤ 2^54 (Bnd.mono) re-establishes the input invariant for
   the next round. Finally `square = pow2k(·, 1)` gives
   ⟪square a⟫ = ⟪a⟫^(2^1) = ⟪a⟫·⟪a⟫.

   ROLE IN THE MAIN THEOREM (Proofs/FieldMain.lean)
   `pow2k_spec`/`square_spec` drive Proofs/InvertSpec.lean: the pow22501
   addition chain computing x^(p-2) is 14 pow2k/mul steps, each verified with
   these lemmas; via Fermat this yields impl_mul_inv_cancel, one of the field
   axioms of `fieldImplementation`.
   Imports: Proofs/MulSpec (architecture + the `dis` macro), Proofs/AddSpec
   (`loop_step`). Dependents: Proofs/InvertSpec.lean.
   ───────────────────────────────────────────────────────────────────────── -/
import Proofs.MulSpec
import Proofs.AddSpec
open Aeneas Aeneas.Std Result
open curve25519

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedSimpArgs false

namespace CurveFieldProofs

-- the weakest-precondition layer: spec_mono / spec_bind / spec_ok used below
open Aeneas.Std.WP

/-- The u128 widening product `pow2k.m(x, y) = (x as u128) * (y as u128)`.

    Rust: nested `fn m(x: u64, y: u64) -> u128` inside `pow2k`,
    curve25519/solana-ed25519/src/backend/serial/u64/field.rs:460-462
    (a separate copy of the identical helper in `mul`, so it gets its own
    generated definition and its own spec lemma — cf. m_spec in MulSpec.lean).
    MATH: pow2k.m x y = ok z with z.val = x.val * y.val; never overflows
    since x·y < 2^64·2^64 = 2^128.
    WHY NEEDED: all 13 partial products of the squaring go through it;
    `@[step]` registers it with the `let*` machinery.                        -/
@[step]
theorem pow2k_m_spec (x y : U64) :
    backend.serial.u64.field.FieldElement51.pow2k.m x y
      ⦃ z => z.val = x.val * y.val ⦄ := by
  unfold backend.serial.u64.field.FieldElement51.pow2k.m
  -- u64 inputs are < 2^64, so the u128 product cannot overflow
  have hx : x.val < 2^64 := x.hBounds
  have hy : y.val < 2^64 := y.hBounds
  have hxy : x.val * y.val < 2^128 := by
    calc x.val * y.val < 2^64 * 2^64 := Nat.mul_lt_mul'' hx hy
      _ = 2^128 := by norm_num
  -- run the 3 ops (cast, cast, mul); `dis` discharges each side condition
  step* by dis

/-- The mask constant in `pow2k` evaluates to 2⁵¹ − 1.

    Rust: `const LOW_51_BIT_MASK: u64 = (1u64 << 51) - 1;`,
    curve25519/solana-ed25519/src/backend/serial/u64/field.rs:511.
    MATH: the constant body returns 2251799813685247 = 2^51 - 1, so
    `x & LOW_51_BIT_MASK = x mod 2^51` — the "keep the low limb" half of each
    carry step. WHY NEEDED: exact value feeds the div/mod accounting (hkey). -/
@[step]
theorem pow2k_mask_spec :
    backend.serial.u64.field.FieldElement51.pow2k.LOW_51_BIT_MASK
      ⦃ m => m.val = 2251799813685247 ⦄ := by
  unfold backend.serial.u64.field.FieldElement51.pow2k.LOW_51_BIT_MASK
  step*

/-- One iteration of the `pow2k` loop body: it squares the field element
    (limbs < 2⁵¹ + 2¹³ afterwards) and decrements `k`, breaking iff `k = 1`.

    Rust: the body of `loop { … }` in `FieldElement51::pow2k`,
    curve25519/solana-ed25519/src/backend/serial/u64/field.rs:466-556
    (generated as `…pow2k_loop.body`, Charon span 480:16-492:86).
    MATH (ASCII), for limbs [x0..x4] with Bnd(a,2^54) and k ≥ 1:
      body (k, a) = ok cf  where either
        k = 1   and cf = done r          (Rust `break` path), or
        k ≥ 2   and cf = cont (k-1, r)   (next iteration),
      and in both cases Bnd(r, 2^51 + 2^13) and [[r]] = [[a]]*[[a]].
    The `ControlFlow` disjunction is exactly the Rust
    `k -= 1; if k == 0 { break; }` protocol made explicit.
    WHY NEEDED: the induction step of `pow2k_loop_spec_aux`; its totality
    (~80 machine ops + 5 massert) is one conjunct of pow2k's panic-freedom. -/
theorem pow2k_body_spec (k : U32) (a : Fe) (x0 x1 x2 x3 x4 : U64)
    (ha : (↑a : List U64) = [x0, x1, x2, x3, x4])
    (hba : Bnd a (2^54)) (hk : 1 ≤ k.val) :
    backend.serial.u64.field.FieldElement51.pow2k_loop.body k a ⦃ cf =>
      (k.val = 1 ∧ ∃ r : Fe, cf = .done r ∧ Bnd r (2^51 + 2^13) ∧ ⟪r⟫ = ⟪a⟫ * ⟪a⟫) ∨
      (2 ≤ k.val ∧ ∃ (k1 : U32) (r : Fe), cf = .cont (k1, r) ∧ k1.val = k.val - 1 ∧
        Bnd r (2^51 + 2^13) ∧ ⟪r⟫ = ⟪a⟫ * ⟪a⟫) ⦄ := by
  -- turn the abstract invariant into 5 named limb bounds x_i < 2^54
  rw [Bnd_eq a x0 x1 x2 x3 x4 _ ha] at hba
  unfold backend.serial.u64.field.FieldElement51.pow2k_loop.body
  -- ── limb loads + 19·a3, 19·a4 precomputations (field.rs:480-481) ─────────
  -- each read is identified (he_*) and bounded (hv_*); 19·2^54 < 2^64
  let* ⟨ i, i_post ⟩ ← Array.index_usize_spec by dis
  have he_i : i = x3 := by simp [i_post, ha]
  have hv_i : i.val < 2^54 := by rw [he_i]; omega
  let* ⟨ a3_19, a3_19_post ⟩ ← U64.mul_spec by dis
  have hv_a3_19 : a3_19.val < 19 * 2^54 := by rw [a3_19_post]; omega
  let* ⟨ i1, i1_post ⟩ ← Array.index_usize_spec by dis
  have he_i1 : i1 = x4 := by simp [i1_post, ha]
  have hv_i1 : i1.val < 2^54 := by rw [he_i1]; omega
  let* ⟨ a4_19, a4_19_post ⟩ ← U64.mul_spec by dis
  have hv_a4_19 : a4_19.val < 19 * 2^54 := by rw [a4_19_post]; omega
  let* ⟨ i2, i2_post ⟩ ← Array.index_usize_spec by dis
  have he_i2 : i2 = x0 := by simp [i2_post, ha]
  have hv_i2 : i2.val < 2^54 := by rw [he_i2]; omega
  -- ── column c0 = a0·a0 + 2·(a1·(19·a4) + a2·(19·a3)) (field.rs:488) ───────
  -- partial products < 2^108 (or < 19·2^108); the ×2 is a u128 multiply;
  -- the running sums stay < 77·2^108 < 2^128, so every u128 op is in range
  let* ⟨ i3, i3_post ⟩ ← pow2k_m_spec by dis
  have hv_i3 : i3.val < 2^108 := by
    rw [i3_post]; have := Nat.mul_lt_mul'' hv_i2 hv_i2; omega
  let* ⟨ i4, i4_post ⟩ ← Array.index_usize_spec by dis
  have he_i4 : i4 = x1 := by simp [i4_post, ha]
  have hv_i4 : i4.val < 2^54 := by rw [he_i4]; omega
  let* ⟨ i5, i5_post ⟩ ← pow2k_m_spec by dis
  have hv_i5 : i5.val < 2^54 * (19 * 2^54) := by
    rw [i5_post]; have := Nat.mul_lt_mul'' hv_i4 hv_a4_19; omega
  let* ⟨ i6, i6_post ⟩ ← Array.index_usize_spec by dis
  have he_i6 : i6 = x2 := by simp [i6_post, ha]
  have hv_i6 : i6.val < 2^54 := by rw [he_i6]; omega
  let* ⟨ i7, i7_post ⟩ ← pow2k_m_spec by dis
  have hv_i7 : i7.val < 2^54 * (19 * 2^54) := by
    rw [i7_post]; have := Nat.mul_lt_mul'' hv_i6 hv_a3_19; omega
  let* ⟨ i8, i8_post ⟩ ← U128.add_spec by scalar_tac
  have hv_i8 : i8.val < 38 * 2^108 := by rw [i8_post]; omega
  let* ⟨ i9, i9_post ⟩ ← U128.mul_spec by scalar_tac
  have hv_i9 : i9.val < 76 * 2^108 := by rw [i9_post]; omega
  let* ⟨ c0, c0_post ⟩ ← U128.add_spec by scalar_tac
  have hv_c0 : c0.val < 77 * 2^108 := by rw [c0_post]; omega
  -- ── column c1 = a3·(19·a3) + 2·(a0·a1 + a2·(19·a4)) (field.rs:489) ───────
  let* ⟨ i10, i10_post ⟩ ← pow2k_m_spec by dis
  have hv_i10 : i10.val < 2^54 * (19 * 2^54) := by
    rw [i10_post]; have := Nat.mul_lt_mul'' hv_i hv_a3_19; omega
  let* ⟨ i11, i11_post ⟩ ← pow2k_m_spec by dis
  have hv_i11 : i11.val < 2^108 := by
    rw [i11_post]; have := Nat.mul_lt_mul'' hv_i2 hv_i4; omega
  let* ⟨ i12, i12_post ⟩ ← pow2k_m_spec by dis
  have hv_i12 : i12.val < 2^54 * (19 * 2^54) := by
    rw [i12_post]; have := Nat.mul_lt_mul'' hv_i6 hv_a4_19; omega
  let* ⟨ i13, i13_post ⟩ ← U128.add_spec by scalar_tac
  have hv_i13 : i13.val < 20 * 2^108 := by rw [i13_post]; omega
  let* ⟨ i14, i14_post ⟩ ← U128.mul_spec by scalar_tac
  have hv_i14 : i14.val < 40 * 2^108 := by rw [i14_post]; omega
  let* ⟨ c1, c1_post ⟩ ← U128.add_spec by scalar_tac
  have hv_c1 : c1.val < 59 * 2^108 := by rw [c1_post]; omega
  -- ── column c2 = a1·a1 + 2·(a0·a2 + a4·(19·a3)) (field.rs:490) ────────────
  let* ⟨ i15, i15_post ⟩ ← pow2k_m_spec by dis
  have hv_i15 : i15.val < 2^108 := by
    rw [i15_post]; have := Nat.mul_lt_mul'' hv_i4 hv_i4; omega
  let* ⟨ i16, i16_post ⟩ ← pow2k_m_spec by dis
  have hv_i16 : i16.val < 2^108 := by
    rw [i16_post]; have := Nat.mul_lt_mul'' hv_i2 hv_i6; omega
  let* ⟨ i17, i17_post ⟩ ← pow2k_m_spec by dis
  have hv_i17 : i17.val < 2^54 * (19 * 2^54) := by
    rw [i17_post]; have := Nat.mul_lt_mul'' hv_i1 hv_a3_19; omega
  let* ⟨ i18, i18_post ⟩ ← U128.add_spec by scalar_tac
  have hv_i18 : i18.val < 20 * 2^108 := by rw [i18_post]; omega
  let* ⟨ i19, i19_post ⟩ ← U128.mul_spec by scalar_tac
  have hv_i19 : i19.val < 40 * 2^108 := by rw [i19_post]; omega
  let* ⟨ c2, c2_post ⟩ ← U128.add_spec by scalar_tac
  have hv_c2 : c2.val < 41 * 2^108 := by rw [c2_post]; omega
  -- ── column c3 = a4·(19·a4) + 2·(a0·a3 + a1·a2) (field.rs:491) ────────────
  let* ⟨ i20, i20_post ⟩ ← pow2k_m_spec by dis
  have hv_i20 : i20.val < 2^54 * (19 * 2^54) := by
    rw [i20_post]; have := Nat.mul_lt_mul'' hv_i1 hv_a4_19; omega
  let* ⟨ i21, i21_post ⟩ ← pow2k_m_spec by dis
  have hv_i21 : i21.val < 2^108 := by
    rw [i21_post]; have := Nat.mul_lt_mul'' hv_i2 hv_i; omega
  let* ⟨ i22, i22_post ⟩ ← pow2k_m_spec by dis
  have hv_i22 : i22.val < 2^108 := by
    rw [i22_post]; have := Nat.mul_lt_mul'' hv_i4 hv_i6; omega
  let* ⟨ i23, i23_post ⟩ ← U128.add_spec by scalar_tac
  have hv_i23 : i23.val < 2 * 2^108 := by rw [i23_post]; omega
  let* ⟨ i24, i24_post ⟩ ← U128.mul_spec by scalar_tac
  have hv_i24 : i24.val < 4 * 2^108 := by rw [i24_post]; omega
  let* ⟨ c3, c3_post ⟩ ← U128.add_spec by scalar_tac
  have hv_c3 : c3.val < 23 * 2^108 := by rw [c3_post]; omega
  -- ── column c4 = a2·a2 + 2·(a0·a4 + a1·a3) (field.rs:492) ─────────────────
  -- no 19-folding here: this is the 2^204 column, it never wraps past 2^255
  let* ⟨ i25, i25_post ⟩ ← pow2k_m_spec by dis
  have hv_i25 : i25.val < 2^108 := by
    rw [i25_post]; have := Nat.mul_lt_mul'' hv_i6 hv_i6; omega
  let* ⟨ i26, i26_post ⟩ ← pow2k_m_spec by dis
  have hv_i26 : i26.val < 2^108 := by
    rw [i26_post]; have := Nat.mul_lt_mul'' hv_i2 hv_i1; omega
  let* ⟨ i27, i27_post ⟩ ← pow2k_m_spec by dis
  have hv_i27 : i27.val < 2^108 := by
    rw [i27_post]; have := Nat.mul_lt_mul'' hv_i4 hv_i; omega
  let* ⟨ i28, i28_post ⟩ ← U128.add_spec by scalar_tac
  have hv_i28 : i28.val < 2 * 2^108 := by rw [i28_post]; omega
  let* ⟨ i29, i29_post ⟩ ← U128.mul_spec by scalar_tac
  have hv_i29 : i29.val < 4 * 2^108 := by rw [i29_post]; omega
  let* ⟨ c4, c4_post ⟩ ← U128.add_spec by scalar_tac
  have hv_c4 : c4.val < 5 * 2^108 := by rw [c4_post]; omega
  -- ── the five debug_assert!(a[i] < 2^54) (field.rs:505-509) ───────────────
  -- kept by Charon as `massert`; massert_spec makes us PROVE each bound
  -- (from hba via scalar_tac) — verified, not assumed. i30 = 1 << 54 = 2^54.
  let* ⟨ i30, i30_post1, i30_post2 ⟩ ← U64.ShiftLeft_IScalar_spec by dis
  have hv_i30 : i30.val = 2^54 := by
    rw [i30_post1]; simp [Nat.shiftLeft_eq, U64.size, U64.numBits]
  let* ⟨ _ ⟩ ← massert_spec by scalar_tac
  let* ⟨ _ ⟩ ← massert_spec by scalar_tac
  let* ⟨ _ ⟩ ← massert_spec by scalar_tac
  let* ⟨ _ ⟩ ← massert_spec by scalar_tac
  let* ⟨ _ ⟩ ← massert_spec by scalar_tac
  -- ── carry pass (field.rs:515-528). Per limb: c_{k+1} += (c_k >> 51) as u64
  --    as u128; a[k] = (c_k as u64) & mask. The u128→u64→u128 cast round-trip
  --    is lossless because c_k/2^51 < 77·2^57 < 2^64 (the hv_* div facts). ──
  -- carry c0 -> c11; limb 0
  let* ⟨ i31, i31_post1, i31_post2 ⟩ ← U128.ShiftRight_IScalar_spec by dis
  let* ⟨ i32, i32_post ⟩ ← UScalar.cast.step_spec by scalar_tac
  let* ⟨ i33, i33_post ⟩ ← UScalar.cast.step_spec by scalar_tac
  have hv_i33 : i33.val = c0.val / 2^51 := by
    simp [i33_post, i32_post, i31_post1, UScalar.cast_val_eq, U64.size, U128.size]; omega
  let* ⟨ c11, c11_post ⟩ ← U128.add_spec by scalar_tac
  have hv_c11 : c11.val < 60 * 2^108 := by
    rw [c11_post]; omega
  let* ⟨ i34, i34_post ⟩ ← UScalar.cast.step_spec by scalar_tac
  let* ⟨ i35, i35_post ⟩ ← pow2k_mask_spec by dis
  let* ⟨ i36, i36_post1, i36_post2 ⟩ ← UScalar.and_spec by scalar_tac
  have hv_i36 : i36.val = c0.val % 2^51 := by
    simp [i36_post1, i34_post, i35_post, UScalar.cast_val_eq, U64.size, U128.size]
  let* ⟨ a1, a1_post ⟩ ← Array.update_spec by scalar_tac
  -- carry c11 -> c21; limb 1
  let* ⟨ i37, i37_post1, i37_post2 ⟩ ← U128.ShiftRight_IScalar_spec by dis
  let* ⟨ i38, i38_post ⟩ ← UScalar.cast.step_spec by scalar_tac
  let* ⟨ i39, i39_post ⟩ ← UScalar.cast.step_spec by scalar_tac
  have hv_i39 : i39.val = c11.val / 2^51 := by
    simp [i39_post, i38_post, i37_post1, UScalar.cast_val_eq, U64.size, U128.size]; omega
  let* ⟨ c21, c21_post ⟩ ← U128.add_spec by scalar_tac
  have hv_c21 : c21.val < 42 * 2^108 := by
    rw [c21_post]; omega
  let* ⟨ i40, i40_post ⟩ ← UScalar.cast.step_spec by scalar_tac
  let* ⟨ i41, i41_post1, i41_post2 ⟩ ← UScalar.and_spec by scalar_tac
  have hv_i41 : i41.val = c11.val % 2^51 := by
    simp [i41_post1, i40_post, i35_post, UScalar.cast_val_eq, U64.size, U128.size]
  let* ⟨ a2, a2_post ⟩ ← Array.update_spec by scalar_tac
  -- carry c21 -> c31; limb 2
  let* ⟨ i42, i42_post1, i42_post2 ⟩ ← U128.ShiftRight_IScalar_spec by dis
  let* ⟨ i43, i43_post ⟩ ← UScalar.cast.step_spec by scalar_tac
  let* ⟨ i44, i44_post ⟩ ← UScalar.cast.step_spec by scalar_tac
  have hv_i44 : i44.val = c21.val / 2^51 := by
    simp [i44_post, i43_post, i42_post1, UScalar.cast_val_eq, U64.size, U128.size]; omega
  let* ⟨ c31, c31_post ⟩ ← U128.add_spec by scalar_tac
  have hv_c31 : c31.val < 24 * 2^108 := by
    rw [c31_post]; omega
  let* ⟨ i45, i45_post ⟩ ← UScalar.cast.step_spec by scalar_tac
  let* ⟨ i46, i46_post1, i46_post2 ⟩ ← UScalar.and_spec by scalar_tac
  have hv_i46 : i46.val = c21.val % 2^51 := by
    simp [i46_post1, i45_post, i35_post, UScalar.cast_val_eq, U64.size, U128.size]
  let* ⟨ a3, a3_post ⟩ ← Array.update_spec by scalar_tac
  -- carry c31 -> c41; limb 3
  let* ⟨ i47, i47_post1, i47_post2 ⟩ ← U128.ShiftRight_IScalar_spec by dis
  let* ⟨ i48, i48_post ⟩ ← UScalar.cast.step_spec by scalar_tac
  let* ⟨ i49, i49_post ⟩ ← UScalar.cast.step_spec by scalar_tac
  have hv_i49 : i49.val = c31.val / 2^51 := by
    simp [i49_post, i48_post, i47_post1, UScalar.cast_val_eq, U64.size, U128.size]; omega
  let* ⟨ c41, c41_post ⟩ ← U128.add_spec by scalar_tac
  have hv_c41 : c41.val < 6 * 2^108 := by
    rw [c41_post]; omega
  let* ⟨ i50, i50_post ⟩ ← UScalar.cast.step_spec by scalar_tac
  let* ⟨ i51, i51_post1, i51_post2 ⟩ ← UScalar.and_spec by scalar_tac
  have hv_i51 : i51.val = c31.val % 2^51 := by
    simp [i51_post1, i50_post, i35_post, UScalar.cast_val_eq, U64.size, U128.size]
  let* ⟨ a4, a4_post ⟩ ← Array.update_spec by scalar_tac
  -- last limb: carry out of c41 (field.rs:527-528); carry counts 2^255-units
  let* ⟨ i52, i52_post1, i52_post2 ⟩ ← U128.ShiftRight_IScalar_spec by dis
  let* ⟨ carry, carry_post ⟩ ← UScalar.cast.step_spec by scalar_tac
  have hv_carry : carry.val = c41.val / 2^51 := by
    simp [carry_post, i52_post1, UScalar.cast_val_eq, U64.size, U128.size]; omega
  let* ⟨ i53, i53_post ⟩ ← UScalar.cast.step_spec by scalar_tac
  let* ⟨ i54, i54_post1, i54_post2 ⟩ ← UScalar.and_spec by scalar_tac
  have hv_i54 : i54.val = c41.val % 2^51 := by
    simp [i54_post1, i53_post, i35_post, UScalar.cast_val_eq, U64.size, U128.size]
  let* ⟨ a5, a5_post ⟩ ← Array.update_spec by scalar_tac
  -- ── fold the final carry * 19 into limb 0 (field.rs:544, since 2^255 ≡ 19),
  --    then the mini-carry into limb 1 (field.rs:547-548). No overflow:
  --    carry < 6·2^57, 19·carry < 2^62, a[0] + 19·carry < 2^51 + 2^62 < 2^64 ──
  let* ⟨ i55, i55_post ⟩ ← U64.mul_spec by scalar_tac
  let* ⟨ i56, i56_post ⟩ ← Array.index_usize_spec by scalar_tac
  have hv_i56 : i56.val = c0.val % 2^51 := by
    simp [i56_post, a5_post, a4_post, a3_post, a2_post, a1_post,
          Array.set_val_eq, hv_i36]
  let* ⟨ i57, i57_post ⟩ ← U64.add_spec by scalar_tac
  let* ⟨ a6, a6_post ⟩ ← Array.update_spec by scalar_tac
  let* ⟨ i58, i58_post ⟩ ← Array.index_usize_spec by scalar_tac
  have hv_i58 : i58.val = i57.val := by
    simp [i58_post, a6_post, a5_post, a4_post, a3_post, a2_post, a1_post,
          Array.set_val_eq]
  let* ⟨ i59, i59_post1, i59_post2 ⟩ ← U64.ShiftRight_IScalar_spec by scalar_tac
  let* ⟨ i60, i60_post ⟩ ← Array.index_usize_spec by scalar_tac
  have hv_i60 : i60.val = c11.val % 2^51 := by
    simp [i60_post, a6_post, a5_post, a4_post, a3_post, a2_post, a1_post,
          Array.set_val_eq, hv_i41]
  let* ⟨ i61, i61_post ⟩ ← U64.add_spec by scalar_tac
  let* ⟨ a7, a7_post ⟩ ← Array.update_spec by scalar_tac
  let* ⟨ i62, i62_post ⟩ ← Array.index_usize_spec by scalar_tac
  have hv_i62 : i62.val = i57.val := by
    simp [i62_post, a7_post, a6_post, a5_post, a4_post, a3_post, a2_post,
          a1_post, Array.set_val_eq]
  let* ⟨ i63, i63_post1, i63_post2 ⟩ ← UScalar.and_spec by scalar_tac
  have hv_i63 : i63.val = i57.val % 2^51 := by
    simp [i63_post1, hv_i62, i35_post, UScalar.cast_val_eq, U64.size, U128.size]
  -- Rust `a[0] &= mask` is modeled as a mutable borrow: `index_mut` returns
  -- the current slot value q AND a write-back function with back v = a7.set 0 v
  let* ⟨ q, back, q_post, back_post ⟩ ← Array.index_mut_usize_spec by scalar_tac
  -- ── symbolic execution done; assemble facts shared by both loop exits ────
  -- the result limb list (a8 = a7.set 0 i63 in both branches):
  -- r = [i57 mod 2^51, (c11 mod 2^51) + i57/2^51,
  --      c21 mod 2^51, c31 mod 2^51, c41 mod 2^51]
  have hv_i59 : i59.val = i57.val / 2^51 := by
    simp [i59_post1, hv_i58]
  have hout : (↑(a7.set 0#usize i63) : List U64) = [i63, i61, i46, i51, i54] := by
    simp [a7_post, a6_post, a5_post, a4_post, a3_post, a2_post, a1_post,
          Array.set_val_eq, ha]
  -- output bound: four limbs are `mod 2^51` < 2^51; limb 1 adds the
  -- mini-carry i57/2^51 < 2^13, so it stays < 2^51 + 2^13
  have hbnd8 : Bnd (a7.set 0#usize i63) (2^51 + 2^13) :=
    (Bnd_eq _ _ _ _ _ _ _ hout).mpr
      ⟨by omega, by omega, by omega, by omega, by omega⟩
  -- ── layer (1): exact ℕ accounting of the carry pass ──────────────────────
  -- feVal r + p·carry = Σ_k c_k·2^(51k): shifting out carry·2^255 and adding
  -- back 19·carry changes the value by exactly (2^255-19)·carry = p·carry
  have hkey : feVal (a7.set 0#usize i63) + P * carry.val
      = c0.val + 2^51*c1.val + 2^102*c2.val + 2^153*c3.val + 2^204*c4.val := by
    rw [feVal_eq _ _ _ _ _ _ hout]; simp only [limbsVal, P]; omega
  -- ── layer (2): ℕ product expansions of the five columns ──────────────────
  -- substitute all step posts, then `ring` rearranges to a polynomial in
  -- x0..x4 (38 = 2·19 comes from doubling a 19-folded cross product)
  have hnc0 : c0.val = x0.val*x0.val + 38*(x1.val*x4.val) + 38*(x2.val*x3.val) := by
    simp only [c0_post, i9_post, i8_post, i3_post, i5_post, i7_post,
              a3_19_post, a4_19_post, he_i, he_i1, he_i2, he_i4, he_i6]
    ring
  have hnc1 : c1.val = 2*(x0.val*x1.val) + 19*(x3.val*x3.val) + 38*(x2.val*x4.val) := by
    simp only [c1_post, i14_post, i13_post, i10_post, i11_post, i12_post,
              a3_19_post, a4_19_post, he_i, he_i1, he_i2, he_i4, he_i6]
    ring
  have hnc2 : c2.val = x1.val*x1.val + 2*(x0.val*x2.val) + 38*(x3.val*x4.val) := by
    simp only [c2_post, i19_post, i18_post, i15_post, i16_post, i17_post,
              a3_19_post, a4_19_post, he_i, he_i1, he_i2, he_i4, he_i6]
    ring
  have hnc3 : c3.val = 19*(x4.val*x4.val) + 2*(x0.val*x3.val) + 2*(x1.val*x2.val) := by
    simp only [c3_post, i24_post, i23_post, i20_post, i21_post, i22_post,
              a3_19_post, a4_19_post, he_i, he_i1, he_i2, he_i4, he_i6]
    ring
  have hnc4 : c4.val = x2.val*x2.val + 2*(x0.val*x4.val) + 2*(x1.val*x3.val) := by
    simp only [c4_post, i29_post, i28_post, i25_post, i26_post, i27_post,
              a3_19_post, a4_19_post, he_i, he_i1, he_i2, he_i4, he_i6]
    ring
  -- ── layer (3): 𝔽_p bridge: A·A = Σ cᵢ·2⁵¹ⁱ using 2²⁵⁵ = 19 ───────────────
  have h255 : (2:Fp)^255 = 19 := by
    have h := two_pow_255_eq; push_cast at h; simpa using h
  -- over ℤ: A·A − Σ c_k·2^(51k) = (2^255 − 19)·D with the squaring
  -- wrap-around polynomial D = Σ_{i+j≥5} x_i·x_j·2^(51(i+j−5)), i.e.
  --   D = 2·x1·x4 + 2·x2·x3 + 2^51·(2·x2·x4 + x3²) + 2^102·(2·x3·x4) + 2^153·x4²
  -- (spelled out literally below); `linear_combination D * h255` certifies it
  have hAA : ((feVal a : ℕ) : Fp) * ((feVal a : ℕ) : Fp)
      = ((c0.val : ℕ) : Fp) + 2^51*(c1.val : ℕ) + 2^102*(c2.val : ℕ)
        + 2^153*(c3.val : ℕ) + 2^204*(c4.val : ℕ) := by
    rw [feVal_eq a x0 x1 x2 x3 x4 ha]
    simp only [limbsVal, hnc0, hnc1, hnc2, hnc3, hnc4]
    push_cast
    linear_combination (2*(x1.val:Fp)*(x4.val:Fp) + 2*(x2.val:Fp)*(x3.val:Fp)
      + 2^51*(2*(x2.val:Fp)*(x4.val:Fp) + (x3.val:Fp)*(x3.val:Fp))
      + 2^102*(2*(x3.val:Fp)*(x4.val:Fp))
      + 2^153*((x4.val:Fp)*(x4.val:Fp))) * h255
  -- ── conclude the denotation fact: cast (1) into F_p where (p : F_p) = 0
  --    kills p·carry, then chain with (3): ⟪r⟫ = ⟪a⟫·⟪a⟫ ───────────────────
  have hc := congrArg (Nat.cast : ℕ → Fp) hkey
  push_cast at hc
  have hp0 : ((P : ℕ) : Fp) = 0 := ZMod.natCast_self P
  rw [hp0] at hc
  simp only [zero_mul, add_zero] at hc
  have hfin : ⟪a7.set 0#usize i63⟫ = ⟪a⟫ * ⟪a⟫ := by
    simp only [denote]
    linear_combination hc - hAA
  -- ── k decrement + branch on k1 = 0 (Rust: k -= 1; if k == 0 { break })
  --    U32.sub_spec needs 1 ≤ k (no u32 underflow) — exactly the hk
  --    hypothesis; with k = 0 release Rust would wrap here (see README) ─────
  let* ⟨ k1, k1_post1, k1_post2 ⟩ ← U32.sub_spec by scalar_tac
  split
  next hcond =>
    -- k1 = 0: the loop breaks; we are in the `done` disjunct with k = 1
    have hkv : k.val = 1 := by
      have h0 : k1.val = 0 := by rw [hcond]; scalar_tac
      scalar_tac
    simp only [spec_ok]
    exact Or.inl ⟨hkv, a7.set 0#usize i63, by rw [back_post], hbnd8, hfin⟩
  next hcond =>
    -- k1 ≠ 0: continue with (k-1, a²); the `cont` disjunct with k ≥ 2
    have hkv : 2 ≤ k.val := by
      have h0 : k1.val ≠ 0 := fun hh => hcond (UScalar.eq_of_val_eq (by scalar_tac))
      scalar_tac
    simp only [spec_ok]
    exact Or.inr ⟨hkv, k1, a7.set 0#usize i63, by rw [back_post],
      by scalar_tac, hbnd8, hfin⟩

/-- Fuel-indexed loop spec: `pow2k_loop k a` computes `⟪a⟫ ^ (2^k)`.

    Rust: the whole `loop { … }` of `pow2k`,
    curve25519/solana-ed25519/src/backend/serial/u64/field.rs:466-556,
    modeled by `…FieldElement51.pow2k_loop` = `Aeneas.Std.loop body`.
    MATH (ASCII): for any fuel n with 1 ≤ k ≤ n and Bnd(a, 2^54):
      pow2k_loop k a = ok r  with  Bnd(r, 2^51 + 2^13)
      and  [[r]] = [[a]] ^ (2^k),
    because k successive squarings give ((a^2)^2…)^2 = a^(2^k).
    PROOF: `Aeneas.Std.loop` carries no termination measure, so we induct on
    the EXPLICIT fuel bound n (generalizing k, a and the limbs). Each step
    peels one iteration with `loop_step` and runs `pow2k_body_spec`:
    the `.done` branch has k = 1 and r = a², i.e. [[a]]^(2^1); the `.cont`
    branch recurses on (k-1, a²) — the body's output bound 2^51 + 2^13 ≤ 2^54
    re-establishes the input invariant (Bnd.mono) — and
    (a²)^(2^(k-1)) = a^(2^k) closes it. k decreases by 1 per iteration, so
    fuel n ≥ k always suffices; n = 0 contradicts 1 ≤ k.
    WHY NEEDED: induction needs the spec stated for ALL n; `pow2k_loop_spec`
    below instantiates n := k.val.                                          -/
theorem pow2k_loop_spec_aux (n : ℕ) (k : U32) (a : Fe) (x0 x1 x2 x3 x4 : U64)
    (ha : (↑a : List U64) = [x0, x1, x2, x3, x4])
    (hba : Bnd a (2^54)) (hk : 1 ≤ k.val) (hkn : k.val ≤ n) :
    backend.serial.u64.field.FieldElement51.pow2k_loop k a
      ⦃ r => Bnd r (2^51 + 2^13) ∧ ⟪r⟫ = ⟪a⟫ ^ (2^k.val) ⦄ := by
  -- fuel induction; everything that changes between iterations is generalized
  induction n generalizing k a x0 x1 x2 x3 x4 with
  | zero => exact absurd hkn (by omega)
  | succ n ih =>
    unfold backend.serial.u64.field.FieldElement51.pow2k_loop
    -- peel exactly one loop iteration (loop_step, Proofs/AddSpec.lean) and
    -- feed it the body spec; then case on the ControlFlow disjunction
    apply loop_step
    apply spec_mono (pow2k_body_spec k a x0 x1 x2 x3 x4 ha hba hk)
    rintro cf (⟨hk1, r, rfl, hbr, hr⟩ | ⟨hk2, k1, r, rfl, hk1v, hbr, hr⟩)
    · -- done: k = 1, one squaring; ⟪r⟫ = ⟪a⟫·⟪a⟫ = ⟪a⟫^(2^1)
      refine ⟨hbr, ?_⟩
      rw [hr, hk1]
      ring
    · -- cont: recurse on (k-1, a²)
      -- name the limbs of the squared element for the IH …
      obtain ⟨r0, r1, r2, r3, r4, hrl⟩ := Fe.exists_limbs r
      -- … re-establish the 2^54 input invariant (2^51 + 2^13 ≤ 2^54) and
      -- apply the induction hypothesis at fuel n, counter k1 = k-1 ≥ 1
      have hih := ih k1 r r0 r1 r2 r3 r4 hrl (hbr.mono (by norm_num))
        (by omega) (by omega)
      unfold backend.serial.u64.field.FieldElement51.pow2k_loop at hih
      apply spec_mono hih
      rintro r' ⟨hbr', hr'⟩
      refine ⟨hbr', ?_⟩
      -- exponent bookkeeping: (⟪a⟫²)^(2^(k-1)) = ⟪a⟫^(2·2^(k-1)) = ⟪a⟫^(2^k)
      have hexp : 2 * 2 ^ (k.val - 1) = 2 ^ k.val := by
        rw [← pow_succ']
        congr 1
        omega
      rw [hr', hr, hk1v, ← hexp, pow_mul]
      ring

/-- Loop spec: `pow2k_loop k a` computes `⟪a⟫ ^ (2^k)` (limbs < 2⁵¹ + 2¹³).

    Same statement as `pow2k_loop_spec_aux` with the fuel hidden: instantiate
    n := k.val (each iteration decrements k, so k.val iterations suffice).
    WHY NEEDED: the fuel is a proof artifact; `pow2k_spec` wants the clean
    statement.                                                              -/
theorem pow2k_loop_spec (k : U32) (a : Fe) (x0 x1 x2 x3 x4 : U64)
    (ha : (↑a : List U64) = [x0, x1, x2, x3, x4])
    (hba : Bnd a (2^54)) (hk : 1 ≤ k.val) :
    backend.serial.u64.field.FieldElement51.pow2k_loop k a
      ⦃ r => Bnd r (2^51 + 2^13) ∧ ⟪r⟫ = ⟪a⟫ ^ (2^k.val) ⦄ :=
  pow2k_loop_spec_aux k.val k a x0 x1 x2 x3 x4 ha hba hk (Nat.le_refl _)

/-- Main spec for `pow2k`: under the 2⁵⁴ invariant and `k ≥ 1`, no panic,
    output limbs < 2⁵¹ + 2¹³, and the denotation is `⟪a⟫ ^ (2^k)`.

    Rust: `FieldElement51::pow2k`,
    curve25519/solana-ed25519/src/backend/serial/u64/field.rs:454-559.
    MATH (ASCII):  Bnd(a,2^54) and k ≥ 1  ==>
      fe_pow2k a k = ok r  with  Bnd(r, 2^51 + 2^13)  and  [[r]] = [[a]]^(2^k).
    The generated body is `massert (k > 0); pow2k_loop k self` — the massert
    is the surviving `debug_assert!(k > 0)` (field.rs:456), provable from hk.
    The k ≥ 1 hypothesis encodes the documented caveat: pow2k(_, 0) would
    wrap k-1 in release Rust; all in-crate callers pass constants ≥ 1.
    WHY NEEDED: `square` below and every pow2k step of the pow22501 chain in
    Proofs/InvertSpec.lean (hence impl_mul_inv_cancel in FieldMain).        -/
@[step]
theorem pow2k_spec (a : Fe) (k : U32) (x0 x1 x2 x3 x4 : U64)
    (ha : (↑a : List U64) = [x0, x1, x2, x3, x4])
    (hba : Bnd a (2^54)) (hk : 1 ≤ k.val) :
    fe_pow2k a k ⦃ r => Bnd r (2^51 + 2^13) ∧ ⟪r⟫ = ⟪a⟫ ^ (2^k.val) ⦄ := by
  unfold fe_pow2k backend.serial.u64.field.FieldElement51.pow2k
  -- discharge the debug_assert!(k > 0) — provable, not assumed
  let* ⟨ _ ⟩ ← massert_spec by scalar_tac
  -- depending on how the trailing `ok a` bind got normalized, the goal is
  -- either exactly the loop spec or one bind away from it; handle both
  first
  | exact pow2k_loop_spec k a x0 x1 x2 x3 x4 ha hba hk
  | (apply spec_bind (pow2k_loop_spec k a x0 x1 x2 x3 x4 ha hba hk);
     intro r hr;
     simp only [spec_ok];
     exact hr)

/-- Main spec for `square`: under the 2⁵⁴ invariant, no panic, output limbs
    < 2⁵¹ + 2¹³, and the denotation squares in 𝔽_p.

    Rust: `FieldElement51::square` = `self.pow2k(1)`,
    curve25519/solana-ed25519/src/backend/serial/u64/field.rs:562-564.
    MATH (ASCII):  Bnd(a, 2^54)  ==>  fe_square a = ok r  with
      Bnd(r, 2^51 + 2^13)  and  [[r]] = [[a]] * [[a]]
    — instance of pow2k_spec at k = 1, since [[a]]^(2^1) = [[a]]·[[a]].
    WHY NEEDED: the squaring steps of InvertSpec's pow22501 chain run
    through this lemma; with mul_spec it underpins impl_mul_inv_cancel.    -/
@[step]
theorem square_spec (a : Fe) (x0 x1 x2 x3 x4 : U64)
    (ha : (↑a : List U64) = [x0, x1, x2, x3, x4])
    (hba : Bnd a (2^54)) :
    fe_square a ⦃ r => Bnd r (2^51 + 2^13) ∧ ⟪r⟫ = ⟪a⟫ * ⟪a⟫ ⦄ := by
  unfold fe_square backend.serial.u64.field.FieldElement51.square
  -- run pow2k at the literal 1#u32, then rewrite x^(2^1) to x*x
  apply spec_mono (pow2k_spec a 1#u32 x0 x1 x2 x3 x4 ha hba (by scalar_tac))
  rintro r ⟨hbr, hr⟩
  refine ⟨hbr, ?_⟩
  have h1 : (1#u32).val = 1 := by scalar_tac
  rw [hr, h1]
  ring

end CurveFieldProofs
