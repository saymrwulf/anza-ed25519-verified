/- ────────────────────────────────────────────────────────────────────────────
   Proofs/Denote.lean — the SEMANTIC FOUNDATION: from machine limbs to 𝔽_p
   ────────────────────────────────────────────────────────────────────────────

   Denotation layer: interpret the transpiled `FieldElement51` into 𝔽_p,
   p = 2²⁵⁵ − 19, and define the limb-bound invariant.

   BACKGROUND.  The Rust crate curve25519/solana-ed25519 (Anza's fork of
   curve25519-dalek) implements arithmetic in the field F_p, p = 2^255 − 19,
   on five radix-2^51 u64 limbs (`FieldElement51`).  The files src/field.rs
   and src/backend/serial/u64/field.rs were transpiled MECHANICALLY to Lean 4
   with Charon + Aeneas (Rust → LLBC → Lean): gen/CurveField/Types.lean and
   gen/CurveField/Funs.lean.  In that model, machine integers become Aeneas
   types (`U64` = 64-bit unsigned, with `.val : ℕ` its mathematical value) and
   fallible machine arithmetic returns in the `Result` monad (`ok x` =
   success, `fail` = panic/overflow); `x ⦃ post ⦄` asserts total correctness:
   "x succeeds AND its value satisfies post".

   THIS FILE is where the transpiled machine code first meets mathematics.
   It defines, ABOUT the generated code (never modifying it):

     • `P`, `Fp`        — the prime p = 2²⁵⁵ − 19 and the field 𝔽_p (ZMod P);
     • `Fe`, `fe_*`     — short aliases for the transpiled type [u64; 5] and
                          its eleven operations;
     • `Fe.exists_limbs`— the destructuring device every proof starts with:
                          an `Fe` IS five named u64 limbs a0 … a4;
     • `limbsVal`/`feVal` — the EXACT natural-number value
                          a0 + a1·2⁵¹ + a2·2¹⁰² + a3·2¹⁵³ + a4·2²⁰⁴ (no mod);
     • `denote` ⟪·⟫     — THE bridge: ⟪a⟫ = (feVal a) mod p ∈ 𝔽_p.  The main
                          theorem (Proofs/FieldMain.lean, `fieldImplementation`)
                          says every transpiled op is total under the limb
                          invariant and implements the 𝔽_p op through this map;
     • `Bnd`            — the dalek limb discipline ("all limbs < c"): the
                          invariant under which the ops are proven panic-free;
     • `P_pos`, `two_pow_255_eq` — basic facts about p; in particular
                          2²⁵⁵ = 19 in 𝔽_p, the single modular identity on
                          which all carry / "19-folding" reasoning hangs.

   RUST CORRESPONDENCE (paths abbreviated in the rest of this file):
     u64/field.rs = curve25519/solana-ed25519/src/backend/serial/u64/field.rs
     field.rs     = curve25519/solana-ed25519/src/field.rs
   `Fe` models `pub struct FieldElement51(pub(crate) [u64; 5])`,
   u64/field.rs:43.  The radix-2⁵¹ representation and the "coefficients are
   allowed to grow up to 2⁵⁴ between reductions" discipline are the crate's
   own documentation, u64/field.rs:26-42.

   PLACE IN THE PROOF GRAPH.  Imports only the generated model
   (CurveField.Funs).  Imported by Proofs/ReduceSpec.lean and
   Proofs/ConstSpecs.lean and, through them, by every other proof file up to
   the main theorem (AddSpec, SubNegSpec, MulSpec, SquareSpec, Field,
   InvertSpec, FieldMain).

   NOTE: nothing in Proofs/ modifies the transpiled code (gen/CurveField/);
   we only define functions *about* it and prove equivalences. -/
import CurveField.Funs
open Aeneas Aeneas.Std Result
open curve25519

namespace CurveFieldProofs

-- ───────────────────────── The prime and the field ─────────────────────────

/-- The field characteristic p = 2²⁵⁵ − 19.

    MATH: P = 2^255 − 19 (a 255-bit number, ℕ-subtraction is exact here).
    P is prime — proved by an axiom-free Lucas/Pratt certificate chain in
    Proofs/P25519.lean; primality is what later makes `Fp` a field and powers
    Fermat's little theorem in the `invert` proof.
    WHY NEEDED: fixes the modulus once and for all; every denotation and
    every operation spec is an equation mod P. -/
def P : ℕ := 2^255 - 19

/-- The mathematical field 𝔽_p (mathlib's `ZMod P`).

    MATH: Z/pZ, integers modulo p.  It is a commutative ring by construction;
    it is known to be a FIELD only once `Fact P.Prime` is in scope
    (instantiated in Proofs/Field.lean from the certificate in P25519.lean).
    WHY NEEDED: the codomain of ⟪·⟫; "the code implements 𝔽_p" is stated as
    equations between elements of this type. -/
abbrev Fp := ZMod P

/-- Short alias for the transpiled field-element type ([u64; 5]).

    Rust: `pub struct FieldElement51(pub(crate) [u64; 5])`, u64/field.rs:43.
    Aeneas renders `[u64; 5]` as `Array U64 5#usize`: a Lean `List U64`
    bundled with a proof that its length is 5 (exploited by
    `Fe.exists_limbs` below).
    WHY NEEDED: the carrier type of the implementation; every spec in
    Proofs/ quantifies over it. -/
abbrev Fe := backend.serial.u64.field.FieldElement51

/-! Short aliases for the transpiled operations (the Aeneas names are long).
    These are definitionally the generated functions — `rfl`-equal.

    The Rust source spans cited below are taken verbatim from the generated
    docstrings in gen/CurveField/Funs.lean (Charon records them; they are
    ground truth).  Each alias points to the proof file that specifies it. -/

/-- Rust: `impl Add<&FieldElement51> for &FieldElement51`, u64/field.rs:68-72
    (limbwise `a[i] + b[i]`, no carry, no reduction — Proofs/AddSpec.lean). -/
abbrev fe_add :=
  Shared0FieldElement51.Insts.CoreOpsArithAddSharedAFieldElement51FieldElement51.add
/-- Rust: `impl Sub<&FieldElement51> for &FieldElement51`, u64/field.rs:84-101
    (adds the constant 16p limbwise before subtracting, so u64 subtraction
    cannot underflow; then reduces — Proofs/SubNegSpec.lean). -/
abbrev fe_sub :=
  Shared0FieldElement51.Insts.CoreOpsArithSubSharedAFieldElement51FieldElement51.sub
/-- Rust: `impl Mul<&FieldElement51> for &FieldElement51`, u64/field.rs:115-213
    (radix-2⁵¹ schoolbook product, high limbs folded back ×19, u128 carry
    chain — Proofs/MulSpec.lean). -/
abbrev fe_mul :=
  Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51.mul
/-- Rust: `FieldElement51::negate`, u64/field.rs:276-286
    (computes 16p − a limbwise, then reduces — Proofs/SubNegSpec.lean). -/
abbrev fe_neg := backend.serial.u64.field.FieldElement51.negate
/-- Rust: `FieldElement51::reduce`, u64/field.rs:290-323
    (carry chain: each limb keeps its low 51 bits, passes the high bits up;
    the top carry re-enters at limb 0 multiplied by 19 — ReduceSpec.lean). -/
abbrev fe_reduce := backend.serial.u64.field.FieldElement51.reduce
/-- Rust: `FieldElement51::square`, u64/field.rs:562-564
    (literally `pow2k(1)` — Proofs/SquareSpec.lean). -/
abbrev fe_square := backend.serial.u64.field.FieldElement51.square
/-- Rust: `FieldElement51::pow2k`, u64/field.rs:454-559
    (k-fold squaring, k ≥ 1 enforced by a `debug_assert!` that survives
    translation as a provable `massert` — Proofs/SquareSpec.lean). -/
abbrev fe_pow2k := backend.serial.u64.field.FieldElement51.pow2k
/-- Rust: `FieldElement51::invert`, field.rs:239-248
    (x^(p−2) via the pow22501 addition chain; equals x⁻¹ by Fermat's little
    theorem — Proofs/InvertSpec.lean). -/
abbrev fe_invert := field.FieldElement51.invert
/-- Rust: `FieldElement51::ZERO`, u64/field.rs:263 (limbs [0,0,0,0,0] —
    Proofs/ConstSpecs.lean). -/
abbrev fe_zero := backend.serial.u64.field.FieldElement51.ZERO
/-- Rust: `FieldElement51::ONE`, u64/field.rs:265 (limbs [1,0,0,0,0] —
    Proofs/ConstSpecs.lean). -/
abbrev fe_one := backend.serial.u64.field.FieldElement51.ONE
/-- Rust: `FieldElement51::MINUS_ONE`, u64/field.rs:267-273 (the limbs of the
    literal p − 1 — Proofs/ConstSpecs.lean). -/
abbrev fe_minus_one := backend.serial.u64.field.FieldElement51.MINUS_ONE

-- ───────────────────── Destructuring a field element ───────────────────────

/-- Every `Fe` is a 5-element list of u64 limbs.

    MATH:  forall a : Fe,  exists a0 a1 a2 a3 a4 : U64,
           a = [a0, a1, a2, a3, a4].
    LaTeX: $\forall a,\ \exists a_0\dots a_4,\ a = [a_0,a_1,a_2,a_3,a_4]$.

    The destructuring device EVERY proof in Proofs/ starts with
    (`obtain ⟨a0, a1, a2, a3, a4, hl⟩ := Fe.exists_limbs a`): `Fe` is a
    length-5 subtype, and the limbs must be given names before any limb
    arithmetic can be stated.
    WHY NEEDED: turns the abstract array into the concrete 5-element shape on
    which `feVal_eq` / `Bnd_eq` and the symbolic execution of the generated
    code (which indexes limbs 0..4) can fire. -/
theorem Fe.exists_limbs (a : Fe) :
    ∃ a0 a1 a2 a3 a4 : U64, (↑a : List U64) = [a0, a1, a2, a3, a4] := by
  -- The subtype carries the proof that the underlying list has length 5.
  have h : (↑a : List U64).length = 5 := by
    have := a.property
    simp_all
  -- Case-split on the shape of the list; only length 5 is consistent with h.
  match hl : (↑a : List U64) with
  | [a0, a1, a2, a3, a4] => exact ⟨a0, a1, a2, a3, a4, rfl⟩
  -- Lists of length 0–4 contradict h …
  | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] => simp [hl] at h
  -- … as does any list of length ≥ 6.
  | _::_::_::_::_::_::_ => simp [hl] at h

-- ─────────────────── Exact ℕ value and the denotation ⟪·⟫ ──────────────────

/-- Value of a limb vector as a natural number (radix 2⁵¹).

    MATH:  limbsVal a0 a1 a2 a3 a4
             = a0 + a1·2⁵¹ + a2·2¹⁰² + a3·2¹⁵³ + a4·2²⁰⁴      (in ℕ).
    LaTeX: $\sum_{i=0}^{4} a_i \cdot 2^{51 i}$.

    This is the EXACT integer value — no `mod p`, no wraparound.  All
    overflow/carry accounting in ReduceSpec/AddSpec/SubNegSpec/MulSpec/
    SquareSpec is performed on this ℕ value first (e.g. ReduceSpec proves
    `feVal r + p·(l4 >> 51) = feVal l` exactly); only at the end is the value
    cast into 𝔽_p by `denote`.
    WHY NEEDED: separates the bit-level bookkeeping (ℕ, decided by `omega`/
    `ring`) from the modular reasoning (𝔽_p, one cast at the end). -/
def limbsVal (a0 a1 a2 a3 a4 : U64) : ℕ :=
  a0.val + 2^51 * a1.val + 2^102 * a2.val + 2^153 * a3.val + 2^204 * a4.val

/-- Value of a field element as a natural number.

    MATH: feVal a = limbsVal a0 a1 a2 a3 a4 where [a0,…,a4] are a's limbs.
    Defined by matching on the underlying list; the `_ => 0` default is dead
    code (by `Fe.exists_limbs` the list always has exactly 5 elements) and
    exists only to make the function total without dependent matching.
    WHY NEEDED: lifts `limbsVal` from named limbs to whole field elements, so
    specs can be stated about an abstract `a : Fe`. -/
def feVal (a : Fe) : ℕ :=
  match (↑a : List U64) with
  | [a0, a1, a2, a3, a4] => limbsVal a0 a1 a2 a3 a4
  | _ => 0

/-- Rewriting lemma: once the limbs of `a` are named (via `Fe.exists_limbs`),
    `feVal a` unfolds to the explicit polynomial `limbsVal a0 a1 a2 a3 a4`.
    Marked `@[simp]` so it fires automatically during proofs.
    WHY NEEDED: the `match` inside `feVal` cannot reduce on an abstract `a`;
    this lemma is the bridge every value computation goes through. -/
@[simp]
theorem feVal_eq (a : Fe) (a0 a1 a2 a3 a4 : U64)
    (h : (↑a : List U64) = [a0, a1, a2, a3, a4]) :
    feVal a = limbsVal a0 a1 a2 a3 a4 := by
  simp [feVal, h]

/-- The denotation ⟪a⟫ : 𝔽_p of a field element.

    MATH:  ⟪a⟫ = (a0 + a1·2⁵¹ + a2·2¹⁰² + a3·2¹⁵³ + a4·2²⁰⁴) mod p.
    LaTeX: $\llbracket a\rrbracket=\bigl(\sum_i a_i\,2^{51 i}\bigr)\bmod p$
    (the ℕ → `ZMod P` coercion performs the reduction mod p).

    THE bridge from machine limbs to mathematics.  The main theorem
    (Proofs/FieldMain.lean, `fieldImplementation`) is phrased entirely through
    this map: e.g. "fe_mul a b succeeds with result r and ⟪r⟫ = ⟪a⟫ * ⟪b⟫".
    Note the map is total but NOT injective — many limb vectors denote the
    same field element (the representation is redundant), which is exactly
    why "the code is a field" must be stated via ⟪·⟫ (surjectivity + each op
    realizing its 𝔽_p counterpart) rather than as a `Field Fe` instance. -/
def denote (a : Fe) : Fp := (feVal a : Fp)

/- Bracket notation for the denotation.  (⟪·⟫ rather than ⟦·⟧, which collides
   with `Quotient.mk`.) -/
notation "⟪" a "⟫" => denote a

-- ───────────────────── The limb-bound invariant (Bnd) ──────────────────────

/-- Limb-bound invariant: all limbs < `c`. Operations require/provide:
    `reduce`/`mul`/`square` outputs satisfy `Bnd · (2^52)`;
    `mul`/`square`/`sub`/`neg` inputs require `Bnd · (2^54)`.

    MATH: Bnd a c  iff  a_i < c for all i in 0..4.

    This is the dalek "limb discipline" stated in the crate's own docs
    (u64/field.rs:29-32: radix-2⁵¹ coefficients "are allowed to grow up to
    2⁵⁴ between reductions modulo p").  Each operation's spec has the shape

        Bnd inputs (2⁵⁴)  ==>  op succeeds, output Bnd (2⁵²), ⟪·⟫ correct

    so any output (< 2⁵²) can be fed back as an input (< 2⁵⁴) via `Bnd.mono`,
    closing the composition loop.  Like `feVal`, the non-5-element branch
    (`False`) is dead code that keeps the definition total.
    WHY NEEDED: totality (panic-freedom: every u64/u128 add/mul/shift in the
    carry chains stays in range, every `debug_assert` holds) is only true
    under this invariant; it is the hypothesis of every clause of the main
    theorem. -/
def Bnd (a : Fe) (c : ℕ) : Prop :=
  match (↑a : List U64) with
  | [a0, a1, a2, a3, a4] =>
    a0.val < c ∧ a1.val < c ∧ a2.val < c ∧ a3.val < c ∧ a4.val < c
  | _ => False

/-- Rewriting lemma: once the limbs are named, `Bnd a c` unfolds to the five
    explicit inequalities (companion of `feVal_eq`; `@[simp]`).
    WHY NEEDED: the `match` inside `Bnd` cannot reduce on an abstract `a`. -/
@[simp]
theorem Bnd_eq (a : Fe) (a0 a1 a2 a3 a4 : U64) (c : ℕ)
    (h : (↑a : List U64) = [a0, a1, a2, a3, a4]) :
    Bnd a c ↔
      (a0.val < c ∧ a1.val < c ∧ a2.val < c ∧ a3.val < c ∧ a4.val < c) := by
  simp [Bnd, h]

/-- `Bnd` is monotone in the bound.

    MATH: Bnd a c  and  c ≤ c'   ==>   Bnd a c'.
    WHY NEEDED: glues operation specs together — outputs carry the tight
    bound 2⁵² while the next operation's hypothesis asks for 2⁵⁴ (and the
    main theorem's invariant clauses weaken bounds the same way). -/
theorem Bnd.mono {a : Fe} {c c' : ℕ} (h : Bnd a c) (hcc : c ≤ c') : Bnd a c' := by
  -- Name the limbs, rewrite both `Bnd`s to the five inequalities …
  obtain ⟨a0, a1, a2, a3, a4, hl⟩ := Fe.exists_limbs a
  rw [Bnd_eq a a0 a1 a2 a3 a4 c hl] at h
  rw [Bnd_eq a a0 a1 a2 a3 a4 c' hl]
  -- … then it is linear arithmetic.
  omega

/-! ## Basic facts about P -/

/-- MATH: 0 < p (p is a 255-bit number, so certainly positive).
    WHY NEEDED: positivity feeds the ℕ-subtraction and `mod p` lemmas used
    throughout the value-accounting proofs. -/
theorem P_pos : 0 < P := by norm_num [P]

/-- THE modular identity of the whole development:  2²⁵⁵ = 19 in 𝔽_p.

    MATH:  2^255 ≡ 19 (mod p),   because   2^255 − 19 = p ≡ 0 (mod p).
    LaTeX: $2^{255} \equiv 19 \pmod{2^{255}-19}$.

    Every appearance of the magic constant 19 in the Rust code is justified
    by exactly this identity: a contribution that overflows past bit 255 may
    be folded back into limb 0 multiplied by 19 (the ×19 limb products in
    `mul`/`square`, the re-entering top carry in `reduce`) and the 16p
    constants added by `sub`/`negate` vanish mod p for the same reason.
    WHY NEEDED: invoked, directly or through derived multiple-of-p facts, by
    every correctness proof that moves value across the 2²⁵⁵ boundary. -/
theorem two_pow_255_eq :
    ((2^255 : ℕ) : Fp) = (19 : Fp) := by
  -- p itself vanishes when cast into 𝔽_p …
  have h : ((P : ℕ) : Fp) = 0 := ZMod.natCast_self P
  -- … and over ℕ, 2²⁵⁵ is literally p + 19 (checked numerically).
  have : (2^255 : ℕ) = P + 19 := by norm_num [P]
  rw [this]
  -- Push the cast through the sum; the p-summand is 0, leaving 19.
  push_cast [h]
  ring

end CurveFieldProofs
