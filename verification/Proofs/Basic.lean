/- ────────────────────────────────────────────────────────────────────────────
   Proofs/Basic.lean — pin the hand-written external models + first sanity
   facts about the generated code
   ────────────────────────────────────────────────────────────────────────────

   First proofs over the Aeneas-generated field model (CurveField).

   BACKGROUND.  The Rust field code of curve25519/solana-ed25519
   (src/field.rs + src/backend/serial/u64/field.rs) was transpiled
   mechanically to Lean 4 with Charon + Aeneas into gen/CurveField/Types.lean
   and Funs.lean; fallible machine operations live in the `Result` monad
   (`ok x` = success, `fail` = panic/overflow).  Items OUTSIDE the crate —
   essentially the `subtle` crate (v2.6.1, constant-time primitives) — are
   not transpiled; they are modeled BY HAND in gen/CurveField/FunsExternal.lean
   and form the trusted base of the verification (see ../README.md,
   "External-model policy").

   These establish the proof pattern for this workspace:
   - pin down the semantics of the hand-written external models
     (gen/CurveField/FunsExternal.lean) as reusable simp lemmas, and
   - prove first sanity facts about the generated code itself.

   Every external-model lemma below is proved by `rfl` (definitional
   equality): it adds NO trust beyond the model itself.  Its value is
   (a) restating the model in the `= ok …` shape that simp / symbolic
   execution consumes, and (b) regression-pinning: if someone edits a model
   in FunsExternal.lean to mean something else, this file stops compiling.

   PLACE IN THE PROOF GRAPH.  Standalone: imports the generated model
   (CurveField.Funs) and is compiled first by ../check.sh, but is NOT
   imported by the Denote → … → FieldMain chain that proves the main theorem
   (CurveFieldProofs.fieldImplementation).  Proofs/ConstSpecs.lean proves the
   stronger, denotational versions of the constant facts below (it even
   reuses the name `zero_spec`, which is harmless precisely because this file
   is not imported there).

   The real verification targets (limb-bound invariants, add/sub/mul/square
   correctness vs. ℤ/(2²⁵⁵-19), panic-freedom of the carry chains, and the
   sqrt_ratio_i specification) build on these — see ../README.md. -/
import CurveField.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
open curve25519

namespace CurveFieldProofs

/-! ## Semantics of the external models (subtle)

    `subtle.Choice` is the subtle crate's constant-time boolean: a `u8` whose
    documented invariant is value ∈ {0, 1} (1 = true).  The model declares
    `subtle.Choice := U8` (gen/CurveField/TypesExternal.lean), so `c.val` below
    is that u8's numeric value.  Source spans cite subtle-2.6.1/src/lib.rs,
    copied from the model docstrings in gen/CurveField/FunsExternal.lean. -/

/-- `Choice::from(u8)` is the identity (the Rust `black_box` is a barrier).

    subtle crate: `impl From<u8> for Choice`, subtle-2.6.1/src/lib.rs:238.
    MATH: from b = ok b — total, value unchanged.  The Rust body is
    `Choice(black_box(input))`; `black_box` is a volatile read that only
    defeats compiler optimization, semantically the identity.
    WHY NEEDED: the transpiled field code builds `Choice`s through this
    conversion (e.g. in `sqrt_ratio_i`); the simp lemma lets proofs step
    over those calls. -/
@[simp]
theorem choice_from_u8_spec (b : Std.U8) :
    subtle.Choice.Insts.CoreConvertFromU8.from b = ok b := rfl

/-- `bool::from(Choice)` tests non-zeroness.

    subtle crate: `impl From<Choice> for bool`, subtle-2.6.1/src/lib.rs:153.
    MATH: from c = ok (c ≠ 0); on the documented {0,1} invariant this is
    exactly "c = 1".
    WHY NEEDED: the field API exposes results of constant-time comparisons
    as `bool` through this conversion. -/
@[simp]
theorem bool_from_choice_spec (c : subtle.Choice) :
    Bool.Insts.CoreConvertFromChoice.from c = ok (c.val != 0) := rfl

/-- `u64::conditional_select(a, b, c)` keeps `a` iff `c = 0`.

    subtle crate: `impl ConditionallySelectable for u64`,
    subtle-2.6.1/src/lib.rs:513.
    MATH: conditional_select a b c = ok (if c = 0 then a else b).
    The Rust mask trick `a ^ ((-(c as i64) as u64) & (a ^ b))` agrees with
    this if-then-else on the {0,1} Choice invariant (mask = 0 or all-ones).
    WHY NEEDED: limbwise constant-time selection is the building block of
    `FieldElement51`'s `ConditionallySelectable` impl, used by the
    decompression path (`sqrt_ratio_i`). -/
@[simp]
theorem u64_conditional_select_spec (a b : Std.U64) (c : subtle.Choice) :
    U64.Insts.SubtleConditionallySelectable.conditional_select a b c
      = ok (if c.val = 0 then a else b) := rfl

/-- `u64::conditional_assign(self, other, c)` keeps `self` iff `c = 0`.

    subtle crate: `impl ConditionallySelectable for u64`,
    subtle-2.6.1/src/lib.rs:521.
    MATH: conditional_assign self other c
            = ok (if c = 0 then self else other)
    — same mask trick as `conditional_select`, in-place flavor (Aeneas turns
    `&mut self` into returning the new value).
    WHY NEEDED: `sqrt_ratio_i` conditionally overwrites its candidate root
    through this operation. -/
@[simp]
theorem u64_conditional_assign_spec (a b : Std.U64) (c : subtle.Choice) :
    U64.Insts.SubtleConditionallySelectable.conditional_assign a b c
      = ok (if c.val = 0 then a else b) := rfl

/-- `u8::ct_eq` decides equality.

    subtle crate: `impl ConstantTimeEq for u8`, subtle-2.6.1/src/lib.rs:348.
    MATH: ct_eq a b = ok (if a = b then 1 else 0) — the specification the
    Rust xor/shift bit trick implements for ALL inputs (not just {0,1}).
    WHY NEEDED: byte-wise constant-time equality underlies the slice `ct_eq`
    used by the field API's equality test. -/
@[simp]
theorem u8_ct_eq_spec (a b : Std.U8) :
    U8.Insts.SubtleConstantTimeEq.ct_eq a b
      = ok (if a = b then 1#u8 else 0#u8) := rfl

/-! ## First facts about the generated field code

    Sanity checks that the TRANSPILED definitions compute what the Rust
    constants say — first uses of the `unfold`-then-`rfl`/`simp` pattern the
    *Spec files build on.  Path abbreviation below:
    u64/field.rs = curve25519/solana-ed25519/src/backend/serial/u64/field.rs -/

/-- `FieldElement51::ZERO` is the all-zero limb array.

    Rust: `FieldElement51::ZERO = FieldElement51::from_limbs([0,0,0,0,0])`,
    u64/field.rs:263.
    MATH: ZERO = ok [0, 0, 0, 0, 0] — the constant evaluates without panic to
    the all-zero limb vector (`Array.repeat 5 0` = five copies of 0#u64).
    Its denotation ⟪·⟫ = 0 is proved later in Proofs/ConstSpecs.lean.
    WHY NEEDED: sanity fact; the additive identity of the field must exist
    and be panic-free. -/
theorem zero_spec :
    backend.serial.u64.field.FieldElement51.ZERO
      = ok (Array.repeat 5#usize 0#u64) := by
  -- Unfold the generated constant and its `from_limbs` constructor;
  -- both sides are then the same literal term.
  unfold backend.serial.u64.field.FieldElement51.ZERO
    backend.serial.u64.field.FieldElement51.from_limbs
  rfl

/-- `<FieldElement51 as Default>::default()` is `ZERO`.

    Rust: `impl Default for FieldElement` (the serial-u64 alias of
    `FieldElement51`), curve25519/solana-ed25519/src/field.rs:66-70.
    MATH: default = ZERO (equal as `Result`-valued constants).
    WHY NEEDED: checks the transpiler's `Default`-trait plumbing dispatches
    to the right constant. -/
theorem default_eq_zero :
    backend.serial.u64.field.FieldElement51.Insts.CoreDefaultDefault.default
      = backend.serial.u64.field.FieldElement51.ZERO := by
  -- Unfolding the Default-impl wrapper exposes ZERO itself.
  unfold
    backend.serial.u64.field.FieldElement51.Insts.CoreDefaultDefault.default
  rfl

/-- `FieldElement51::from_limbs` never fails.

    Rust: `pub(crate) const fn from_limbs(limbs: [u64; 5])`,
    u64/field.rs:258-260 — a plain constructor wrapping the array.
    MATH: forall limbs, from_limbs limbs = ok limbs — total identity.
    WHY NEEDED: every transpiled constant (ZERO/ONE/MINUS_ONE/SQRT_M1) goes
    through this constructor; the `@[simp]` lemma erases it during symbolic
    execution. -/
@[simp]
theorem from_limbs_spec (limbs : Array Std.U64 5#usize) :
    backend.serial.u64.field.FieldElement51.from_limbs limbs = ok limbs := rfl

end CurveFieldProofs
