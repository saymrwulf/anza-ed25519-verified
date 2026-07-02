/- ──────────────────────────────────────────────────────────────────────────────
   Proofs/SubNegSpec.lean — subtraction and negation via the "add 16p" trick

   WHAT THIS FILE CONTAINS
   Specs for the transpiled `sub` (a + 16p − b, then reduce) and `negate`
   (16p − a, then reduce): no panic under the 2⁵⁴ invariant, output < 2⁵²,
   and the denotation is subtraction/negation in 𝔽_p. Plus three helpers:
   a composition-friendly restatement of `reduce_spec` (`reduce_make_spec`),
   the constant identity `sixteen_p`, and the ℕ→𝔽_p bridge `cast_key`.

   RUST ANALOG
   - `impl Sub<&FieldElement51> for &FieldElement51::sub`,
     curve25519/solana-ed25519/src/backend/serial/u64/field.rs:84-101
   - `FieldElement51::negate`, field.rs:276-286
   Transpiled bodies in gen/CurveField/Funs.lean:
   `Shared0FieldElement51.Insts.CoreOpsArithSubSharedAFieldElement51FieldElement51.sub`
   and `backend.serial.u64.field.FieldElement51.negate`.

   THE 16p TRICK (why the strange constants)
   u64 subtraction PANICS on underflow (in the Aeneas model: `fail`), and a_i − b_i
   would underflow whenever b_i > a_i. The Rust therefore computes a − b as
   a + 16p − b, with 16p pre-encoded limb-wise:
       C0 = 16·(2⁵¹ − 19) = 36028797018963664      (limb 0)
       Ci = 16·(2⁵¹ −  1) = 36028797018963952      (limbs 1..4)
   so that  C0 + C1·2⁵¹ + C2·2¹⁰² + C3·2¹⁵³ + C4·2²⁰⁴ = 16p  EXACTLY
   (lemma `sixteen_p`; this is the radix-2⁵¹ "borrowed" spelling of
   16p = 16·(2²⁵⁵ − 19): limb 0 carries the −19, every higher limb is one short of
   2⁵⁵ because it lent a borrow downward). Each Ci ≈ 2⁵⁵ exceeds any b_i < 2⁵⁴, so
   (a_i + Ci) − b_i never underflows, and a_i + Ci < 2⁵⁴ + 2⁵⁵ < 2⁶⁴ never overflows.
   Adding 16p ≡ 0 (mod p) leaves the denotation unchanged; the trailing `reduce`
   (Proofs/ReduceSpec.lean) restores limbs < 2⁵². `negate` is the b := a, a := 0
   special case: 16p − a.

   PROOF ARCHITECTURE (shared by sub_spec / neg_spec)
   1. Walk the monadic body with `let* ... ← op_spec by(...)` — one machine op per
      line, each producing a named postcondition hypothesis (i_post, i1_post, ...);
      the `by(...)` block discharges that op's overflow/underflow/bounds side
      condition (this IS the panic-freedom proof, op by op).
   2. End with `reduce_make_spec`, yielding the exact carry equation of reduce.
   3. Assemble everything into one purely ADDITIVE ℕ equation `key`
      (e.g. feVal r + p·carry + feVal b = feVal a + 16p) closed by `omega` —
      additive so ℕ truncated subtraction never appears.
   4. Cast once to 𝔽_p with `cast_key` (16p and p·carry vanish mod p).

   ROLE IN THE MAIN THEOREM
   `sub_spec`/`neg_spec` are the totality + correctness facts for the field's
   subtraction and additive inverse; Proofs/Field.lean and Proofs/FieldMain.lean
   consume them for `impl_add_neg` and friends. MulSpec.lean imports this file
   (its carry accounting reuses the same lemma style and `reduce_make_spec`).

   FILE RELATIONS
   Imports Proofs/ReduceSpec.lean (reduce_spec + the %/÷ simp lemmas).
   Imported by Proofs/MulSpec.lean and Proofs/Field.lean.
   ────────────────────────────────────────────────────────────────────────────── -/
import Proofs.ReduceSpec
open Aeneas Aeneas.Std Result
open curve25519

set_option maxHeartbeats 4000000

namespace CurveFieldProofs

/-- `reduce` applied to a literal `Array.make` — composition-friendly form.

    Rust: same as `reduce_spec` — `FieldElement51::reduce`,
    curve25519/solana-ed25519/src/backend/serial/u64/field.rs:290-323 — but matching the
    call shape `FieldElement51::reduce([e0, e1, e2, e3, e4])` that `sub` (field.rs:94-100)
    and `negate` (field.rs:278-284) produce: the transpiler emits
    `reduce (Array.make 5#usize [i3, i7, ...])`.

    MATH:  reduce [x0..x4] = ok r  with  Bnd(r, 2^51 + 19*2^13)
           and  feVal r + p*(x4 div 2^51) = x0 + x1*2^51 + x2*2^102 + x3*2^153 + x4*2^204.

    WHY NEEDED: pure plumbing. `reduce_spec` takes an abstract `Fe` plus a hypothesis
    naming its limbs; here the limbs are syntactically visible in the `Array.make`
    literal, so this version needs no side hypothesis and can be applied directly by
    the `let*`/`step` machinery (hence the `@[step]` registration) at the end of the
    sub/negate proofs below. -/
@[step]
theorem reduce_make_spec (x0 x1 x2 x3 x4 : U64) :
    fe_reduce (Array.make 5#usize [x0, x1, x2, x3, x4]) ⦃ r =>
      Bnd r (2^51 + 19 * 2^13) ∧
      feVal r + P * (x4.val / 2^51) = limbsVal x0 x1 x2 x3 x4 ⦄ := by
  have h : (↑(Array.make 5#usize [x0, x1, x2, x3, x4]) : List U64)
      = [x0, x1, x2, x3, x4] := rfl
  have hs := reduce_spec (Array.make 5#usize [x0, x1, x2, x3, x4])
    x0 x1 x2 x3 x4 h
  simpa [feVal_eq _ _ _ _ _ _ h] using hs

/-- Σ Cᵢ·2⁵¹ⁱ for the sub/neg constants (C₀ = 16(2⁵¹−19), Cᵢ = 16(2⁵¹−1))
    is exactly 16p.

    Rust: the magic literals 36028797018963664 / 36028797018963952 in `sub`
    (field.rs:95-99) and `negate` (field.rs:279-283); the Rust comment at
    field.rs:85-86 explains "first add a multiple of p. Choose 16*p = p << 4
    to be larger than 54-bit _rhs".

    MATH:
    ASCII:  C0 + C1*2^51 + C2*2^102 + C3*2^153 + C4*2^204 = 16 * (2^255 - 19)
    LaTeX:  $\sum_{i=0}^{4} C_i\,2^{51 i} = 16p$ with $C_0 = 16(2^{51}-19)$,
            $C_i = 16(2^{51}-1)$ for $i \ge 1$.
    This is the radix-2⁵¹ borrowed expansion of 16p: each upper limb is 16 short of
    16·2⁵¹ because it lends 16·2⁵¹ to the limb below, and limb 0 additionally absorbs
    16·(−19). Verified by `norm_num` literal arithmetic in the kernel.

    WHY NEEDED: the `key` equations of `sub_spec`/`neg_spec` below state
    "result + p·carry + b = a + 16p"; `omega` needs 16p both as the closed-form ℕ
    constant and as the limb-constant sum that actually appears in the executed code,
    and this lemma is that equality. -/
theorem sixteen_p :
    36028797018963664 + 2^51 * 36028797018963952 + 2^102 * 36028797018963952
      + 2^153 * 36028797018963952 + 2^204 * 36028797018963952 = 16 * P := by
  norm_num [P]

/-- The casting bridge: from the exact ℕ-level equation to 𝔽_p.

    No Rust analog — this is pure proof infrastructure.

    MATH:
    ASCII:  if  x + p*k + y = m + 16*p  over the naturals,
            then  (x : F_p) = (m : F_p) - (y : F_p).
    LaTeX:  $x + pk + y = m + 16p \;\Rightarrow\; \bar x = \bar m - \bar y$ in
            $\mathbb F_p$ (both $pk$ and $16p$ vanish, since $p \equiv 0$).
    Instantiated with x = feVal r, y = feVal b (or feVal a for negate), k = the
    reduce carry, m = feVal a (or 0).

    WHY NEEDED: this is the single point where the ℕ-level bookkeeping of the proofs
    becomes a field equation. The hypothesis is deliberately ADDITIVE (no subtraction)
    so it can be produced by `omega` over ℕ; subtraction only ever appears here, on the
    𝔽_p side, where it is total. `congrArg Nat.cast` maps the equation through the
    ring homomorphism ℕ → ZMod p, `push_cast` distributes it, and `P ≡ 0` kills the
    multiples of p. -/
theorem cast_key {x y k m : ℕ} (h : x + P * k + y = m + 16 * P) :
    (x : Fp) = (m : Fp) - (y : Fp) := by
  -- map the ℕ equation through the cast ring hom; (P : Fp) = 0 makes P·k and 16·P vanish
  have hc := congrArg (Nat.cast : ℕ → Fp) h
  push_cast at hc
  -- turn the goal x = m − y into x + y = m and close with the cast equation
  rw [eq_sub_iff_add_eq]
  simpa using hc

/-- `sub` spec: total under the 2⁵⁴ limb invariant, output < 2⁵², and the
    denotation subtracts in 𝔽_p.

    Rust: `impl Sub<&FieldElement51> for &FieldElement51::sub`,
    curve25519/solana-ed25519/src/backend/serial/u64/field.rs:84-101 —
    `FieldElement51::reduce([(a[i] + C_i) - b[i]; 5])` with the 16p constants C_i.

    MATH:
    ASCII:  forall a b : Fe,  Bnd(a, 2^54) and Bnd(b, 2^54)  ==>
            fe_sub a b = ok r  with  Bnd(r, 2^52)  and  [[r]] = [[a]] - [[b]] in F_p.
    LaTeX:  $\forall a\,b,\ \mathrm{Bnd}(a,2^{54}) \wedge \mathrm{Bnd}(b,2^{54})
            \Rightarrow \exists r,\ \mathrm{sub}(a,b) = \mathrm{ok}\ r \wedge
            \mathrm{Bnd}(r,2^{52}) \wedge
            \llbracket r\rrbracket = \llbracket a\rrbracket - \llbracket b\rrbracket$.

    Per-limb machine arithmetic (i = 0..4, all in u64):
      t_i = (a_i + C_i) − b_i ;  no overflow since a_i + C_i < 2⁵⁴ + 2⁵⁵·1.0007 < 2⁶⁴,
      no underflow since C_i ≥ 16(2⁵¹−19) > 2⁵⁴ > b_i;  then r = reduce [t0..t4].
    Value: Σ t_i 2^(51i) = feVal a + 16p − feVal b exactly over ℕ, and reduce removes
    p·carry, so feVal r + p·carry + feVal b = feVal a + 16p (`key` below); casting to
    𝔽_p (cast_key) gives ⟪r⟫ = ⟪a⟫ − ⟪b⟫.

    WHY NEEDED: this is the field-subtraction leg of the main theorem — its totality is
    part of `fieldImplementation`'s no-panic claim, and Field.lean/FieldMain.lean derive
    `impl_add_neg` (a + (−a) = 0) and the subtraction-compatibility laws from it. -/
theorem sub_spec (a b : Fe) (x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 : U64)
    (ha : (↑a : List U64) = [x0, x1, x2, x3, x4])
    (hb : (↑b : List U64) = [y0, y1, y2, y3, y4])
    (hba : Bnd a (2^54)) (hbb : Bnd b (2^54)) :
    fe_sub a b ⦃ r => Bnd r (2^52) ∧ ⟪r⟫ = ⟪a⟫ - ⟪b⟫ ⦄ := by
  -- restate the Bnd invariants as plain per-limb inequalities (x_i < 2⁵⁴ etc.)
  rw [Bnd_eq a x0 x1 x2 x3 x4 _ ha] at hba
  rw [Bnd_eq b y0 y1 y2 y3 y4 _ hb] at hbb
  -- expose the transpiled monadic body (gen/CurveField/Funs.lean)
  unfold fe_sub
    Shared0FieldElement51.Insts.CoreOpsArithSubSharedAFieldElement51FieldElement51.sub
  -- Symbolic execution, one machine op per `let*`: read a limb / add the 16p constant /
  -- read the other limb / subtract. Each `by(...)` block discharges that op's side
  -- condition (index in bounds, no u64 overflow on +, no underflow on −) from the 2⁵⁴
  -- bounds — these 20 discharges constitute the panic-freedom proof of `sub`.
  -- limb 0:  i3 = (x0 + C0) − y0
  let* ⟨ i, i_post ⟩ ← Array.index_usize_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i1, i1_post ⟩ ← U64.add_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i2, i2_post ⟩ ← Array.index_usize_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i3, i3_post1, i3_post2 ⟩ ← U64.sub_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  -- limb 1:  i7 = (x1 + C1) − y1
  let* ⟨ i4, i4_post ⟩ ← Array.index_usize_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i5, i5_post ⟩ ← U64.add_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i6, i6_post ⟩ ← Array.index_usize_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i7, i7_post1, i7_post2 ⟩ ← U64.sub_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  -- limb 2:  i11 = (x2 + C2) − y2
  let* ⟨ i8, i8_post ⟩ ← Array.index_usize_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i9, i9_post ⟩ ← U64.add_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i10, i10_post ⟩ ← Array.index_usize_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i11, i11_post1, i11_post2 ⟩ ← U64.sub_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  -- limb 3:  i15 = (x3 + C3) − y3
  let* ⟨ i12, i12_post ⟩ ← Array.index_usize_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i13, i13_post ⟩ ← U64.add_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i14, i14_post ⟩ ← Array.index_usize_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i15, i15_post1, i15_post2 ⟩ ← U64.sub_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  -- limb 4:  i19 = (x4 + C4) − y4  (i19's carry i19/2⁵¹ is the p-multiple reduce removes)
  let* ⟨ i16, i16_post ⟩ ← Array.index_usize_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i17, i17_post ⟩ ← U64.add_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i18, i18_post ⟩ ← Array.index_usize_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i19, i19_post1, i19_post2 ⟩ ← U64.sub_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  -- final reduce on the raw limbs [i3, i7, i11, i15, i19] (ReduceSpec, packaged form)
  let* ⟨ r, r_post1, r_post2 ⟩ ← reduce_make_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  -- Bnd conjunct: weaken reduce's bound 2⁵¹ + 19·2¹³ to the stated 2⁵² (Bnd.mono)
  refine ⟨r_post1.mono (by norm_num), ?_⟩
  -- Exact ℕ-level accounting: result + P·carry + b = a + 16p.
  have key : feVal r + P * (i19.val / 2^51) + feVal b
      = feVal a + 16 * P := by
    -- rewrite all three feVal's to limb sums; r_post2 is reduce's carry equation
    rw [r_post2, feVal_eq a x0 x1 x2 x3 x4 ha, feVal_eq b y0 y1 y2 y3 y4 hb]
    simp only [limbsVal] at *
    -- All limb equations (incl. ℕ-subtractions with their ≤ side facts) are
    -- in context; 16p is the constant sum (sixteen_p). Linear: omega.
    have h16 := sixteen_p
    simp [i_post, i2_post, i4_post, i6_post, i8_post, i10_post, i12_post,
          i14_post, i16_post, i18_post, ha, hb] at *
    omega
  -- one cast to 𝔽_p: 16p and p·carry vanish, leaving ⟪r⟫ = ⟪a⟫ − ⟪b⟫
  simpa [denote] using cast_key key

/-- `negate` spec: total under the 2⁵⁴ limb invariant, output < 2⁵², and the
    denotation is the additive inverse in 𝔽_p.

    Rust: `FieldElement51::negate`,
    curve25519/solana-ed25519/src/backend/serial/u64/field.rs:276-286 —
    `FieldElement51::reduce([C_i - self[i]; 5])` ("see commentary in the Sub impl").

    MATH:
    ASCII:  forall a : Fe,  Bnd(a, 2^54)  ==>
            fe_neg a = ok r  with  Bnd(r, 2^52)  and  [[r]] = -[[a]] in F_p.
    LaTeX:  $\forall a,\ \mathrm{Bnd}(a,2^{54}) \Rightarrow \exists r,\
            \mathrm{negate}(a) = \mathrm{ok}\ r \wedge \mathrm{Bnd}(r,2^{52}) \wedge
            \llbracket r\rrbracket = -\llbracket a\rrbracket$.

    This is `sub` specialised to 0 − a: per limb t_i = C_i − a_i (no underflow because
    C_i ≥ 16(2⁵¹−19) > 2⁵⁴ > a_i), so Σ t_i 2^(51i) = 16p − feVal a exactly, then
    reduce. The `key` equation is the m = 0 instance of sub's:
    feVal r + p·carry + feVal a = 0 + 16p.

    WHY NEEDED: provides the additive inverse for the field structure — FieldMain's
    `impl_add_neg` (run negate, run add, get 0) rests on this spec's totality and
    value clause. -/
theorem neg_spec (a : Fe) (x0 x1 x2 x3 x4 : U64)
    (ha : (↑a : List U64) = [x0, x1, x2, x3, x4])
    (hba : Bnd a (2^54)) :
    fe_neg a ⦃ r => Bnd r (2^52) ∧ ⟪r⟫ = -⟪a⟫ ⦄ := by
  -- restate Bnd as per-limb bounds, expose the transpiled body
  rw [Bnd_eq a x0 x1 x2 x3 x4 _ ha] at hba
  unfold fe_neg backend.serial.u64.field.FieldElement51.negate
  -- Symbolic execution, two ops per limb (read a_i, compute C_i − a_i); each `by(...)`
  -- discharges the underflow side condition from a_i < 2⁵⁴ < C_i.
  -- limb 0:  i1 = C0 − x0
  let* ⟨ i, i_post ⟩ ← Array.index_usize_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i1, i1_post1, i1_post2 ⟩ ← U64.sub_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  -- limb 1:  i3 = C1 − x1
  let* ⟨ i2, i2_post ⟩ ← Array.index_usize_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i3, i3_post1, i3_post2 ⟩ ← U64.sub_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  -- limb 2:  i5 = C2 − x2
  let* ⟨ i4, i4_post ⟩ ← Array.index_usize_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i5, i5_post1, i5_post2 ⟩ ← U64.sub_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  -- limb 3:  i7 = C3 − x3
  let* ⟨ i6, i6_post ⟩ ← Array.index_usize_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i7, i7_post1, i7_post2 ⟩ ← U64.sub_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  -- limb 4:  i9 = C4 − x4
  let* ⟨ i8, i8_post ⟩ ← Array.index_usize_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i9, i9_post1, i9_post2 ⟩ ← U64.sub_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  -- final reduce on [i1, i3, i5, i7, i9]
  let* ⟨ neg, neg_post1, neg_post2 ⟩ ← reduce_make_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  -- Bnd conjunct: weaken 2⁵¹ + 19·2¹³ to 2⁵²
  refine ⟨neg_post1.mono (by norm_num), ?_⟩
  -- Exact ℕ accounting (sub's `key` with a := 0): result + P·carry + a = 0 + 16p.
  have key : feVal neg + P * (i9.val / 2^51) + feVal a
      = 0 + 16 * P := by
    rw [neg_post2, feVal_eq a x0 x1 x2 x3 x4 ha]
    simp only [limbsVal] at *
    -- limb equations + sixteen_p in context; linear over ℕ: omega
    have h16 := sixteen_p
    simp [i_post, i2_post, i4_post, i6_post, i8_post, ha] at *
    omega
  -- cast once to 𝔽_p: ⟪neg⟫ = 0 − ⟪a⟫ = −⟪a⟫
  have := cast_key key
  simpa [denote] using this

end CurveFieldProofs
