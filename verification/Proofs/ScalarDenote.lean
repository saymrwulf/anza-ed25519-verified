/- ──────────────────────────────────────────────────────────────────────────────
   Proofs/ScalarDenote.lean — SEMANTIC FOUNDATION for the scalar layer:
   from Scalar52 machine limbs to ℤ/ℓℤ, ℓ the ed25519 group order.

   WHAT THIS FILE PROVIDES
   * `Ell` — the group order ℓ = 2²⁵² + 27742317777372353535851937790883648493
     (a prime; the order of the ed25519 basepoint).
   * `Sc := Scalar52` — the transpiled type: 5 little-endian 52-bit-limbed u64s
     (`Array U64 5`; each limb < 2⁵² by the crate's representation invariant).
   * `scVal`/`scLimbs` — the exact ℕ value Σ lᵢ·2^(52i).
   * `ScBnd` — the limb-bound invariant (all limbs < 2⁵²).
   * `scDenote` (⟦·⟧) — the denotation Scalar52 → ZMod ℓ.
   * `L_val` — the transpiled `constants::L` denotes exactly ℓ (kernel-checked).

   RUST ANALOG: `src/backend/serial/u64/scalar.rs` — `pub struct Scalar52(pub [u64; 5])`,
   invariant "5 limbs of 52 bits each, value < ℓ after reduction".

   SCOPE NOTE. This file + the add/sub specs are the tractable core. The
   Montgomery multiplication path (`mul_internal` → `montgomery_reduce`) shares
   the 4×64-Montgomery big-coefficient structure that overflows the Lean kernel
   in the pasta field layer (documented in that repo's POSTMORTEM); it is built
   the same isolated-lemma way but is not yet complete.

   Imports: gen/CurveScalar (the transpiled Scalar52 arithmetic).
   ────────────────────────────────────────────────────────────────────────────── -/
import CurveField.Funs
open Aeneas Aeneas.Std Result
open curve25519

namespace ScalarProofs

/-- The ed25519 group order ℓ = 2²⁵² + 27742317777372353535851937790883648493. -/
def Ell : ℕ := 7237005577332262213973186563042994240857116359379907606001950938285454250989

/-- The transpiled Scalar52 element type (5 little-endian 52-bit limbs). -/
abbrev Sc := backend.serial.u64.scalar.Scalar52

/-- Exact ℕ value of five little-endian 52-bit limbs. -/
def scLimbs (a0 a1 a2 a3 a4 : U64) : ℕ :=
  a0.val + 2^52 * a1.val + 2^104 * a2.val + 2^156 * a3.val + 2^208 * a4.val

/-- Exact ℕ value of a `Scalar52`. -/
def scVal (a : Sc) : ℕ :=
  match (↑a : List U64) with
  | [a0, a1, a2, a3, a4] => scLimbs a0 a1 a2 a3 a4
  | _ => 0

/-- Every `Scalar52` IS five named u64 limbs. -/
theorem Sc.exists_limbs (a : Sc) :
    ∃ a0 a1 a2 a3 a4 : U64, (↑a : List U64) = [a0, a1, a2, a3, a4] := by
  obtain ⟨l, hl⟩ := a
  match l, hl with
  | [a0, a1, a2, a3, a4], _ => exact ⟨a0, a1, a2, a3, a4, rfl⟩

@[simp]
theorem scVal_eq (a : Sc) (a0 a1 a2 a3 a4 : U64)
    (h : (↑a : List U64) = [a0, a1, a2, a3, a4]) :
    scVal a = scLimbs a0 a1 a2 a3 a4 := by
  unfold scVal; rw [h]

/-- The limb discipline: every limb below 2⁵² (52-bit limbs). -/
def ScBnd (a : Sc) : Prop :=
  ∃ a0 a1 a2 a3 a4 : U64, (↑a : List U64) = [a0, a1, a2, a3, a4] ∧
    a0.val < 2^52 ∧ a1.val < 2^52 ∧ a2.val < 2^52 ∧ a3.val < 2^52 ∧ a4.val < 2^52

/-- The denotation: machine limbs ↦ ℤ/ℓℤ. -/
def scDenote (a : Sc) : ZMod Ell := (scVal a : ZMod Ell)

notation "⟦" a "⟧" => scDenote a

/-- The transpiled `constants::L` as a limb list. -/
theorem L_limbs :
    (↑backend.serial.u64.constants.L : List U64) =
      [671914833335277#u64, 3916664325105025#u64, 1367801#u64, 0#u64,
       17592186044416#u64] := by
  unfold backend.serial.u64.constants.L
  rfl

/-- **The transpiled modulus constant denotes exactly the group order ℓ.**
    Kernel-checked literal arithmetic (no native_decide). -/
theorem L_val : scVal backend.serial.u64.constants.L = Ell := by
  rw [scVal_eq _ _ _ _ _ _ L_limbs]
  unfold scLimbs Ell
  norm_num

/-- The limbs of L are each below 2⁵² (needed by the add/sub reductions). -/
theorem L_bnd : ScBnd backend.serial.u64.constants.L := by
  refine ⟨_, _, _, _, _, L_limbs, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

end ScalarProofs
