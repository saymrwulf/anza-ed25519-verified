/- ──────────────────────────────────────────────────────────────────────────
   Proofs/InventoryScalar.lean — declaration inventory for the scalar layer.

   Audit INFRASTRUCTURE, not corpus. Compiled by check-scalar.sh Phase 2c,
   which is where these modules' compiled artifacts exist: check.sh does not
   compile the scalar layer, so its own inventory could not cover them and
   named them as uncovered on every run instead. This closes that.
────────────────────────────────────────────────────────────────────────── -/
import Proofs.InventoryCore
import Proofs.ScalarDenote
import Proofs.ScalarLoop
import Proofs.ScalarSubSpec
import Proofs.ScalarAddSpec
import Proofs.ScalarMulSpec
import Proofs.ScalarMontSpec
import Proofs.ScalarReduceSpec
import Proofs.ScalarFullMulSpec
import Proofs.ScalarMain
import Proofs.ScalarWideSpec
import Proofs.ScalarBytesSpec
import Proofs.ScalarUnpackSpec
import Proofs.ScalarFromBytesSpec
open Lean Ed25519Inventory

/-- Exactly check-scalar.sh's PROOFS manifest; that script asserts the
    correspondence in both directions. -/
def corpus : Array Name :=
  #[`Proofs.ScalarDenote, `Proofs.ScalarLoop, `Proofs.ScalarSubSpec, `Proofs.ScalarAddSpec, `Proofs.ScalarMulSpec, `Proofs.ScalarMontSpec, `Proofs.ScalarReduceSpec, `Proofs.ScalarFullMulSpec, `Proofs.ScalarMain, `Proofs.ScalarWideSpec, `Proofs.ScalarBytesSpec, `Proofs.ScalarUnpackSpec, `Proofs.ScalarFromBytesSpec]

#eval show MetaM Unit from emitInventory corpus
