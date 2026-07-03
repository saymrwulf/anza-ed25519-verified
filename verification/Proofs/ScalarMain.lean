/- ──────────────────────────────────────────────────────────────────────────────
   Proofs/ScalarMain.lean — the scalar-layer aggregate certificate.

   Clean-interface corollaries of the assembly proofs, stated through
   `ScBnd` (52-bit limb representation) and `scDenote` (⟦·⟧ : Scalar52 →
   ZMod ℓ), plus the single bundled certificate `scalarImplementation`:

     · add: canonical inputs           →  ⟦add a b⟧ = ⟦a⟧ + ⟦b⟧, ScBnd out
     · sub: canonical subtrahend       →  ⟦sub a b⟧ = ⟦a⟧ − ⟦b⟧, ScBnd out
     · mul: Montgomery input bound     →  ⟦mul a b⟧ = ⟦a⟧ · ⟦b⟧, ScBnd out
       (canonical inputs satisfy it: ℓ·ℓ < 2^260·ℓ)

   Audit: `#print axioms ScalarProofs.scalarImplementation` must report
   exactly [propext, Classical.choice, Quot.sound].
   ────────────────────────────────────────────────────────────────────────────── -/
import Proofs.ScalarFullMulSpec
import Proofs.ScalarAddSpec
open Aeneas Aeneas.Std Result
open curve25519

set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 600

namespace ScalarProofs

open Aeneas.Std.WP

/-- Addition, clean interface. -/
theorem scalar_add_correct (a b : Sc) (ha : ScBnd a) (hb : ScBnd b)
    (hca : scVal a < Ell) (hcb : scVal b < Ell) :
    backend.serial.u64.scalar.Scalar52.add a b
      ⦃ r => ScBnd r ∧ scDenote r = scDenote a + scDenote b ⦄ := by
  obtain ⟨a0, a1, a2, a3, a4, hal, hA0, hA1, hA2, hA3, hA4⟩ := ha
  obtain ⟨b0, b1, b2, b3, b4, hbl, hB0, hB1, hB2, hB3, hB4⟩ := hb
  apply spec_mono (add_val_spec a b a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 hal hbl
    ⟨hA0, hA1, hA2, hA3, hA4⟩ ⟨hB0, hB1, hB2, hB3, hB4⟩ hca hcb)
  intro r hr
  exact ⟨hr.1, hr.2⟩

/-- Subtraction, clean interface. -/
theorem scalar_sub_correct (a b : Sc) (ha : ScBnd a) (hb : ScBnd b)
    (hcb : scVal b ≤ Ell) :
    backend.serial.u64.scalar.Scalar52.sub a b
      ⦃ r => ScBnd r ∧ scDenote r = scDenote a - scDenote b ⦄ := by
  obtain ⟨a0, a1, a2, a3, a4, hal, hA0, hA1, hA2, hA3, hA4⟩ := ha
  obtain ⟨b0, b1, b2, b3, b4, hbl, hB0, hB1, hB2, hB3, hB4⟩ := hb
  apply spec_mono (sub_val_spec a b a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 hal hbl
    ⟨hA0, hA1, hA2, hA3, hA4⟩ ⟨hB0, hB1, hB2, hB3, hB4⟩ hcb)
  intro r hr
  exact ⟨hr.1, hr.2⟩

/-- Multiplication, clean interface. The Montgomery hypothesis
    scVal a · scVal b < 2^260·ℓ holds in particular for canonical inputs. -/
theorem scalar_mul_correct (a b : Sc) (ha : ScBnd a) (hb : ScBnd b)
    (hm : scVal a * scVal b < 2^260 * Ell) :
    backend.serial.u64.scalar.Scalar52.mul a b
      ⦃ r => ScBnd r ∧ scDenote r = scDenote a * scDenote b ⦄ := by
  obtain ⟨a0, a1, a2, a3, a4, hal, hA0, hA1, hA2, hA3, hA4⟩ := ha
  obtain ⟨b0, b1, b2, b3, b4, hbl, hB0, hB1, hB2, hB3, hB4⟩ := hb
  apply spec_mono (mul_spec a b a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 hal hbl
    ⟨hA0, hA1, hA2, hA3, hA4⟩ ⟨hB0, hB1, hB2, hB3, hB4⟩ hm)
  intro r hr
  exact ⟨hr.1, hr.2⟩

/-- Canonical inputs always satisfy the Montgomery multiplication bound. -/
theorem canonical_mul_bound {a b : Sc} (hca : scVal a < Ell) (hcb : scVal b < Ell) :
    scVal a * scVal b < 2^260 * Ell := by
  have h1 : scVal a * scVal b < Ell * Ell := Nat.mul_lt_mul'' hca hcb
  have h2 : Ell * Ell ≤ 2^260 * Ell :=
    Nat.mul_le_mul_right Ell (by unfold Ell; norm_num)
  exact lt_of_lt_of_le h1 h2

/-- **The scalar-layer certificate**: the transpiled `Scalar52` add, sub
    and mul all denote the ring operations of ZMod ℓ on canonical inputs,
    with 52-bit-bounded limb output. One theorem, one axiom audit. -/
theorem scalarImplementation :
    (∀ a b : Sc, ScBnd a → ScBnd b → scVal a < Ell → scVal b < Ell →
      backend.serial.u64.scalar.Scalar52.add a b
        ⦃ r => ScBnd r ∧ scDenote r = scDenote a + scDenote b ⦄) ∧
    (∀ a b : Sc, ScBnd a → ScBnd b → scVal b ≤ Ell →
      backend.serial.u64.scalar.Scalar52.sub a b
        ⦃ r => ScBnd r ∧ scDenote r = scDenote a - scDenote b ⦄) ∧
    (∀ a b : Sc, ScBnd a → ScBnd b → scVal a < Ell → scVal b < Ell →
      backend.serial.u64.scalar.Scalar52.mul a b
        ⦃ r => ScBnd r ∧ scDenote r = scDenote a * scDenote b ⦄) :=
  ⟨fun a b ha hb hca hcb => scalar_add_correct a b ha hb hca hcb,
   fun a b ha hb hcb => scalar_sub_correct a b ha hb hcb,
   fun a b ha hb hca hcb =>
     scalar_mul_correct a b ha hb (canonical_mul_bound hca hcb)⟩

end ScalarProofs
