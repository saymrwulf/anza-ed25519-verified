/- ──────────────────────────────────────────────────────────────────────────────
   Proofs/ScalarLoop.lean — generic loop-combinator lemmas for the scalar
   layer's `for i in 0..5` reductions (sub_loop, add_loop, conditional_add_l).

   These three lemmas are identical in statement to the field layer's
   (Proofs/AddSpec.lean); they are about `Aeneas.Std.loop` and the transpiled
   `core::iter::range` iterator, NOT about any field/scalar specifics, so they
   are re-stated here to keep the scalar proofs independent of the field gen.
   ────────────────────────────────────────────────────────────────────────────── -/
import Proofs.ScalarDenote
open Aeneas Aeneas.Std Result ControlFlow
open curve25519

namespace ScalarProofs

open Aeneas.Std.WP

/-- Peel one iteration of the `Aeneas.Std.loop` fixed point under a `spec` goal. -/
theorem loop_step {α : Type u} {β : Type v}
    {body : α → Result (ControlFlow α β)} {x : α} {post : β → Prop}
    (h : body x ⦃ r => match r with
        | .cont x' => Aeneas.Std.loop body x' ⦃ post ⦄
        | .done y => post y ⦄) :
    Aeneas.Std.loop body x ⦃ post ⦄ := by
  obtain ⟨r, hr, hpost⟩ := spec_imp_exists h
  rw [Aeneas.Std.loop.eq_def, hr]
  cases r <;> simpa using hpost

/-- `Iterator::next` on a not-yet-finished `usize` range: yields `some start`
    and advances `start`. -/
theorem range_next_lt_spec (r : core.ops.range.Range Usize)
    (h : r.start.val < r.«end».val) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize r
      ⦃ (o, r') => o = some r.start ∧ r'.start.val = r.start.val + 1 ∧
                   r'.«end» = r.«end» ⦄ := by
  have hmax : r.start.val + 1 ≤ Usize.max := by scalar_tac
  have hca := Usize.checked_add_bv_spec r.start 1#usize
  unfold core.iter.range.IteratorRange.next
  simp only [core.cmp.impls.PartialOrdUsize.lt,
    core.clone.impls.CloneUsize.clone, core.iter.range.StepUsize.forward_checked,
    liftFun1, liftFun2, bind_tc_ok]
  simp only [h, decide_true, if_true]
  cases hadd : Usize.checked_add r.start 1#usize with
  | none => rw [hadd] at hca; simp at hca; scalar_tac
  | some n =>
    rw [hadd] at hca
    simp at hca
    simp [spec_ok, hca]

/-- `Iterator::next` on a finished `usize` range: yields `none`, range unchanged. -/
theorem range_next_ge_spec (r : core.ops.range.Range Usize)
    (h : r.«end».val ≤ r.start.val) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize r
      ⦃ (o, r') => o = none ∧ r' = r ⦄ := by
  unfold core.iter.range.IteratorRange.next
  simp only [core.cmp.impls.PartialOrdUsize.lt,
    core.clone.impls.CloneUsize.clone, core.iter.range.StepUsize.forward_checked,
    liftFun1, liftFun2, bind_tc_ok]
  have : ¬ (r.start.val < r.«end».val) := by omega
  simp [this]

end ScalarProofs
