/- ──────────────────────────────────────────────────────────────────────────────
   Proofs/AddSpec.lean — limbwise addition (the transpiled Rust for-loop)

   WHAT THIS FILE CONTAINS
   Spec for the transpiled `FieldElement51` addition
   (`impl Add<&FieldElement51> for &FieldElement51`, which calls `AddAssign`):
   it never panics provided the limbwise sums do not overflow u64, and the
   output is the *limbwise* sum — this addition performs NO modular reduction.
   Plus the loop/iterator infrastructure needed to reason about the one Rust
   `for` loop in the field code (`loop_step`, `range_next_lt_spec`,
   `range_next_ge_spec`).

   RUST ANALOG
   - `impl AddAssign<&FieldElement51> for FieldElement51::add_assign`,
     curve25519/solana-ed25519/src/backend/serial/u64/field.rs:59-63:
         for i in 0..5 { self.0[i] += _rhs.0[i]; }
   - `impl Add<&FieldElement51> for &FieldElement51::add`, field.rs:68-72
     (copies self, then `output += _rhs`).
   Transpiled bodies in gen/CurveField/Funs.lean:
   `Shared0FieldElement51.Insts.CoreOpsArithAddSharedAFieldElement51FieldElement51.add`
   delegating to `...CoreOpsArithAddAssignSharedAFieldElement51.add_assign`, whose
   `for` loop Charon/Aeneas compiled into the tail-recursive combinator
   `Aeneas.Std.loop` applied to `add_assign_loop.body`, threading the state
   (range-iterator, self, _rhs). The body calls `Iterator::next` on `Range<usize>`
   (Rust std: core::iter::range, stepping via `Step::forward_checked`), and either
   `done` (range exhausted) or performs one `self[i] + rhs[i]` update and `cont`s.

   WHY THE SPEC IS "EXACT LIMBWISE SUMS"
   Unlike sub/negate/mul, `add` performs neither carry propagation nor reduction:
   r_i = a_i + b_i exactly as u64 (panics iff some a_i + b_i ≥ 2⁶⁴). Consequently
   feVal r = feVal a + feVal b holds EXACTLY over ℕ, and limb bounds DOUBLE:
   Bnd a c ∧ Bnd b c → Bnd r (2c). Callers must track this growth — e.g. adding two
   reduced elements (< 2⁵²) yields < 2⁵³ limbs, still safely below the 2⁵⁴ input
   invariant of mul/sub; this bookkeeping is done in Proofs/Field.lean / FieldMain.lean.

   PROOF ARCHITECTURE
   `add_limbs_spec` unrolls the loop 5-fold by hand: 5 × (apply `loop_step`, run one
   body iteration with `range_next_lt_spec` + index/add/update steps) and a 6th
   `loop_step` where `range_next_ge_spec` (5 ≥ 5) makes the body return `done`.
   `add_spec` then repackages the limb equations into the feVal/Bnd form via the
   consequence rule `spec_mono`.

   ROLE IN THE MAIN THEOREM
   Field addition of `fieldImplementation`: totality under no-overflow is one conjunct
   of the no-panic claim, and feVal r = feVal a + feVal b casts to ⟪r⟫ = ⟪a⟫ + ⟪b⟫,
   from which FieldMain derives impl_add_comm/impl_add_assoc/impl_zero_add/impl_add_neg.

   FILE RELATIONS
   Imports Proofs/Denote.lean (Fe, feVal, Bnd) and Proofs/ReduceSpec.lean (whose
   ℕ-level simp lemmas are in scope for scalar_tac). Imported by Proofs/SquareSpec.lean
   and Proofs/Field.lean.
   ────────────────────────────────────────────────────────────────────────────── -/
import Proofs.Denote
import Proofs.ReduceSpec
open Aeneas Aeneas.Std Result
open curve25519

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace CurveFieldProofs

-- weakest-precondition helpers for the ⦃·⦄ assertions (spec_imp_exists, spec_ok, spec_mono)
open Aeneas.Std.WP

/-- Unfold one iteration of `Aeneas.Std.loop` under a `spec` goal.

    No Rust analog — proof infrastructure for the `loop` combinator that Aeneas
    emits for every Rust loop.

    MATH (one unfolding of the loop's fixed-point semantics):
    ASCII:  if  body x  succeeds with a result r such that
              - r = cont x'  implies  loop body x' ⦃ post ⦄   (loop continues), and
              - r = done y   implies  post y                  (loop exits),
            then  loop body x ⦃ post ⦄.
    `ControlFlow α β` is the transpiled `core::ops::ControlFlow`: `cont x'` carries the
    next loop state, `done y` the loop's final value.

    WHY NEEDED: `add_assign`'s `for` loop has a statically known trip count (0..5), so
    instead of a loop invariant we apply this lemma 6 times — 5 productive iterations
    plus the terminating `next = none` check — fully unrolling the loop. Without it the
    opaque `Aeneas.Std.loop` could not be executed symbolically. -/
theorem loop_step {α : Type u} {β : Type v}
    {body : α → Result (ControlFlow α β)} {x : α} {post : β → Prop}
    (h : body x ⦃ r => match r with
        | .cont x' => Aeneas.Std.loop body x' ⦃ post ⦄
        | .done y => post y ⦄) :
    Aeneas.Std.loop body x ⦃ post ⦄ := by
  -- extract the body's concrete result r and its postcondition from the spec assertion
  obtain ⟨r, hr, hpost⟩ := spec_imp_exists h
  -- unfold the fixed point once; the body's result decides continue vs. exit
  rw [Aeneas.Std.loop.eq_def, hr]
  cases r <;> simpa using hpost

/-- `Iterator::next` on a `usize` range that has not finished yet.

    Rust std analog: `impl Iterator for Range<usize>` —
    `core::iter::range::Iterator::next`, which (for `start < end`) clones `start`,
    advances it via `<usize as Step>::forward_checked(start, 1)`, and returns
    `Some(old_start)`. The transpiled model is
    `core.iter.range.IteratorRange.next core.iter.range.StepUsize`.

    MATH:
    ASCII:  start < end  ==>  next {start, end} = ok (some start, {start+1, end}).
    The `checked_add` inside cannot return `none`: start < end ≤ usize::MAX implies
    start + 1 ≤ usize::MAX.

    WHY NEEDED: each of the 5 productive iterations of the `for i in 0..5` loop begins
    with this call; the equations `o = some i` / `start' = i+1` are what let the
    iteration-k proof know which array index it is operating on. -/
theorem range_next_lt_spec (r : core.ops.range.Range Usize)
    (h : r.start.val < r.«end».val) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize r
      ⦃ (o, r') => o = some r.start ∧ r'.start.val = r.start.val + 1 ∧
                   r'.«end» = r.«end» ⦄ := by
  -- start+1 stays within usize, so checked_add must succeed
  have hmax : r.start.val + 1 ≤ Usize.max := by scalar_tac
  have hca := Usize.checked_add_bv_spec r.start 1#usize
  unfold core.iter.range.IteratorRange.next
  -- evaluate the model plumbing: the < comparison, clone, Step::forward_checked
  simp only [core.cmp.impls.PartialOrdUsize.lt,
    core.clone.impls.CloneUsize.clone, core.iter.range.StepUsize.forward_checked,
    liftFun1, liftFun2, bind_tc_ok]
  -- the start < end test is true by hypothesis
  simp only [h, decide_true, if_true]
  -- case on checked_add: the none branch contradicts hmax, the some branch computes
  cases hadd : Usize.checked_add r.start 1#usize with
  | none => rw [hadd] at hca; simp at hca; scalar_tac
  | some n =>
    rw [hadd] at hca
    simp at hca
    simp [spec_ok, hca]

/-- `Iterator::next` on a `usize` range that is finished.

    Rust std analog: same `impl Iterator for Range<usize>` as `range_next_lt_spec`,
    exhausted branch: when `start >= end`, `next` returns `None` and leaves the
    range untouched.

    MATH:
    ASCII:  end <= start  ==>  next {start, end} = ok (none, {start, end}).

    WHY NEEDED: drives the 6th and final `loop_step` of `add_limbs_spec` (range is
    {5, 5}): `next` yields `none`, the transpiled body takes the `done` branch, and
    the loop returns the accumulated element. -/
theorem range_next_ge_spec (r : core.ops.range.Range Usize)
    (h : r.«end».val ≤ r.start.val) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize r
      ⦃ (o, r') => o = none ∧ r' = r ⦄ := by
  unfold core.iter.range.IteratorRange.next
  -- evaluate the comparison/clone/step plumbing as before
  simp only [core.cmp.impls.PartialOrdUsize.lt,
    core.clone.impls.CloneUsize.clone, core.iter.range.StepUsize.forward_checked,
    liftFun1, liftFun2, bind_tc_ok]
  -- the start < end test is now false; the model returns (none, r) directly
  have : ¬ (r.start.val < r.«end».val) := by omega
  simp [this]

/-- Limb-level spec for `fe_add`: total (no panic) under the no-overflow
    hypothesis, and the output limbs are exactly the limbwise sums
    (no modular reduction, no carry propagation).

    Rust: `impl Add for &FieldElement51::add` → `add_assign`,
    curve25519/solana-ed25519/src/backend/serial/u64/field.rs:68-72 and 59-63.

    MATH:
    ASCII:  forall a b : Fe,  (a_i + b_i < 2^64 for i = 0..4)  ==>
            fe_add a b = ok r  with  r_i = a_i + b_i  for all i.
    LaTeX:  $\forall a\,b,\ (\forall i,\ a_i + b_i < 2^{64}) \Rightarrow
            \exists r,\ \mathrm{add}(a,b) = \mathrm{ok}\ r \wedge
            \forall i,\ r_i = a_i + b_i$.
    The hypothesis `hbnd` is exactly the panic condition of the Rust `+=` on u64
    (overflow aborts in debug; the Aeneas model makes it `fail` unconditionally), so
    proving the spec under `hbnd` IS the panic-freedom proof.

    WHY NEEDED: the strongest (limb-exact) description of `add`, consumed by
    `add_spec` below; keeping the loop-unrolling proof separate from the
    feVal/Bnd repackaging keeps both readable. -/
theorem add_limbs_spec (a b : Fe) (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : U64)
    (ha : (↑a : List U64) = [a0, a1, a2, a3, a4])
    (hb : (↑b : List U64) = [b0, b1, b2, b3, b4])
    (hbnd : a0.val + b0.val < 2^64 ∧ a1.val + b1.val < 2^64 ∧
            a2.val + b2.val < 2^64 ∧ a3.val + b3.val < 2^64 ∧
            a4.val + b4.val < 2^64) :
    fe_add a b ⦃ r => ∃ r0 r1 r2 r3 r4 : U64,
      (↑r : List U64) = [r0, r1, r2, r3, r4] ∧
      r0.val = a0.val + b0.val ∧ r1.val = a1.val + b1.val ∧
      r2.val = a2.val + b2.val ∧ r3.val = a3.val + b3.val ∧
      r4.val = a4.val + b4.val ⦄ := by
  obtain ⟨hbnd0, hbnd1, hbnd2, hbnd3, hbnd4⟩ := hbnd
  -- expose the Add → AddAssign → loop-combinator chain (gen/CurveField/Funs.lean)
  unfold fe_add
    Shared0FieldElement51.Insts.CoreOpsArithAddSharedAFieldElement51FieldElement51.add
    backend.serial.u64.field.FieldElement51.Insts.CoreOpsArithAddAssignSharedAFieldElement51.add_assign
    backend.serial.u64.field.FieldElement51.Insts.CoreOpsArithAddAssignSharedAFieldElement51.add_assign_loop
  -- Iteration 1 (i = 0)
  -- Pattern repeated for each of the 5 iterations:
  --   loop_step            — peel one iteration of the loop combinator,
  --   simp only [..body]   — substitute the loop body's definition,
  --   step with range_next_lt_spec — Iterator::next yields some i, range advances,
  --   step ×2              — read rhs[i] (x_k) and self[i] (y_k),
  --   step                 — u64 add; its overflow side condition is closed by hbnd_i,
  --   step                 — write the sum back into self (array update s_k),
  --   spec_ok              — the body returns `cont` with the updated state.
  -- hv_k records v_k = a_k + b_k; hd_k records the updated array for the next round.
  apply loop_step
  simp only [backend.serial.u64.field.FieldElement51.Insts.CoreOpsArithAddAssignSharedAFieldElement51.add_assign_loop.body]
  step with range_next_lt_spec as ⟨o1, iter1, ho1, hs1, he1⟩
  simp only [ho1]
  step as ⟨x1, hx1⟩
  step as ⟨y1, hy1⟩
  simp [ha, hb] at hx1 hy1
  step as ⟨v0, hv0⟩
  rw [hx1, hy1] at hv0
  step as ⟨s1, hd1⟩
  try simp only [spec_ok]
  -- Iteration 2 (i = 1) — same pattern; the simp at hx2/hy2 additionally rewrites
  -- through iteration 1's array update (hd1 + Array.set_val_eq: get-after-set) so the
  -- reads still refer to the ORIGINAL limbs a1/b1.
  apply loop_step
  simp only [backend.serial.u64.field.FieldElement51.Insts.CoreOpsArithAddAssignSharedAFieldElement51.add_assign_loop.body]
  step with range_next_lt_spec as ⟨o2, iter2, ho2, hs2, he2⟩
  simp only [ho2]
  step as ⟨x2, hx2⟩
  step as ⟨y2, hy2⟩
  simp [hd1, Array.set_val_eq, ha, hb, hs1, he1] at hx2 hy2
  step as ⟨v1, hv1⟩
  rw [hx2, hy2] at hv1
  step as ⟨s2, hd2⟩
  try simp only [spec_ok]
  -- Iteration 3 (i = 2)
  apply loop_step
  simp only [backend.serial.u64.field.FieldElement51.Insts.CoreOpsArithAddAssignSharedAFieldElement51.add_assign_loop.body]
  step with range_next_lt_spec as ⟨o3, iter3, ho3, hs3, he3⟩
  simp only [ho3]
  step as ⟨x3, hx3⟩
  step as ⟨y3, hy3⟩
  simp [hd1, hd2, Array.set_val_eq, ha, hb, hs1, he1, hs2, he2] at hx3 hy3
  step as ⟨v2, hv2⟩
  rw [hx3, hy3] at hv2
  step as ⟨s3, hd3⟩
  try simp only [spec_ok]
  -- Iteration 4 (i = 3)
  apply loop_step
  simp only [backend.serial.u64.field.FieldElement51.Insts.CoreOpsArithAddAssignSharedAFieldElement51.add_assign_loop.body]
  step with range_next_lt_spec as ⟨o4, iter4, ho4, hs4, he4⟩
  simp only [ho4]
  step as ⟨x4, hx4⟩
  step as ⟨y4, hy4⟩
  simp [hd1, hd2, hd3, Array.set_val_eq, ha, hb, hs1, he1, hs2, he2, hs3, he3] at hx4 hy4
  step as ⟨v3, hv3⟩
  rw [hx4, hy4] at hv3
  step as ⟨s4, hd4⟩
  try simp only [spec_ok]
  -- Iteration 5 (i = 4)
  apply loop_step
  simp only [backend.serial.u64.field.FieldElement51.Insts.CoreOpsArithAddAssignSharedAFieldElement51.add_assign_loop.body]
  step with range_next_lt_spec as ⟨o5, iter5, ho5, hs5, he5⟩
  simp only [ho5]
  step as ⟨x5, hx5⟩
  step as ⟨y5, hy5⟩
  simp [hd1, hd2, hd3, hd4, Array.set_val_eq, ha, hb, hs1, he1, hs2, he2, hs3, he3,
    hs4, he4] at hx5 hy5
  step as ⟨v4, hv4⟩
  rw [hx5, hy5] at hv4
  step as ⟨s5, hd5⟩
  try simp only [spec_ok]
  -- Iteration 6 (range exhausted: 5 ≥ 5) — next returns none, body answers `done`
  apply loop_step
  simp only [backend.serial.u64.field.FieldElement51.Insts.CoreOpsArithAddAssignSharedAFieldElement51.add_assign_loop.body]
  step with range_next_ge_spec as ⟨o6, iter6, ho6, hr6⟩
  simp only [ho6]
  try simp only [spec_ok]
  -- Final: exhibit the limbs — the result array is a's array overwritten at 0..4 with
  -- v0..v4; collapsing the five set operations (Array.set_val_eq) gives [v0,...,v4]
  refine ⟨v0, v1, v2, v3, v4, ?_, hv0, hv1, hv2, hv3, hv4⟩
  simp [hd1, hd2, hd3, hd4, hd5, Array.set_val_eq, ha, hs1, hs2, hs3, hs4]

/-- Main spec for `fe_add`: the output has 5 limbs, its (unreduced) value is
    the sum of the input values, and limb bounds double.

    Rust: same as `add_limbs_spec` —
    curve25519/solana-ed25519/src/backend/serial/u64/field.rs:58-73.

    MATH:
    ASCII:  forall a b : Fe,  (a_i + b_i < 2^64 for all i)  ==>
            fe_add a b = ok r  with  |r| = 5 limbs,
            feVal r = feVal a + feVal b      (EXACT over N, no mod p!),
            and  forall c, Bnd(a,c) and Bnd(b,c) ==> Bnd(r, 2c).
    LaTeX:  $\llbracket r\rrbracket_{\mathbb N} = \llbracket a\rrbracket_{\mathbb N}
            + \llbracket b\rrbracket_{\mathbb N}$, hence (cast through ℕ → ZMod p)
            $\llbracket r\rrbracket = \llbracket a\rrbracket + \llbracket b\rrbracket$
            in $\mathbb F_p$.
    The doubling clause `Bnd r (2c)` is the price of skipping reduction: limbs grow by
    one bit per addition. Downstream (Field.lean) instantiates c = 2⁵² (reduced
    operands), giving 2⁵³ < 2⁵⁴ — still inside mul/sub's input invariant, so a single
    unreduced add between reduced values is always safe.

    WHY NEEDED: this is the form FieldMain consumes for the additive field axioms; the
    ℕ-exact value equation makes additive laws (comm/assoc) literally inherited from ℕ
    before casting to 𝔽_p. -/
theorem add_spec (a b : Fe) (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : U64)
    (ha : (↑a : List U64) = [a0, a1, a2, a3, a4])
    (hb : (↑b : List U64) = [b0, b1, b2, b3, b4])
    (hbnd : a0.val + b0.val < 2^64 ∧ a1.val + b1.val < 2^64 ∧
            a2.val + b2.val < 2^64 ∧ a3.val + b3.val < 2^64 ∧
            a4.val + b4.val < 2^64) :
    fe_add a b ⦃ r => (↑r : List U64).length = 5 ∧
      feVal r = feVal a + feVal b ∧
      ∀ c, Bnd a c → Bnd b c → Bnd r (2*c) ⦄ := by
  -- consequence rule: weaken add_limbs_spec's postcondition to this one
  apply spec_mono (add_limbs_spec a b a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 ha hb hbnd)
  rintro r ⟨r0, r1, r2, r3, r4, hr, h0, h1, h2, h3, h4⟩
  refine ⟨by simp [hr], ?_, ?_⟩
  -- value: Σ (a_i + b_i)·2^(51i) = Σ a_i·2^(51i) + Σ b_i·2^(51i) — linear, omega
  · rw [feVal_eq r r0 r1 r2 r3 r4 hr, feVal_eq a a0 a1 a2 a3 a4 ha,
        feVal_eq b b0 b1 b2 b3 b4 hb]
    simp only [limbsVal]
    omega
  -- bounds: a_i < c and b_i < c give r_i = a_i + b_i < 2c — linear, omega
  · intro c hA hB
    rw [Bnd_eq a a0 a1 a2 a3 a4 c ha] at hA
    rw [Bnd_eq b b0 b1 b2 b3 b4 c hb] at hB
    rw [Bnd_eq r r0 r1 r2 r3 r4 (2*c) hr]
    omega

end CurveFieldProofs
