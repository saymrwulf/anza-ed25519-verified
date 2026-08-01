/- ──────────────────────────────────────────────────────────────────────────
   Proofs/Inventory.lean — environment-derived declaration inventory (main chain).

   Audit INFRASTRUCTURE, not corpus: excluded from check.sh's compile manifest
   and from its own inventory (its constants live in modules the corpus list
   below does not name). It proves nothing and is imported by nothing.

   Covers every module check.sh compiles except any listed as needing a
   separate driver (see Proofs/InventoryBasic.lean if present). Whether
   a split is needed was determined by compiling a probe, per repo.
   ────────────────────────────────────────────────────────────────────────── -/
import Proofs.InventoryCore
import Proofs.Audit
import Proofs.Denote
import Proofs.P25519
import Proofs.ReduceSpec
import Proofs.SubNegSpec
import Proofs.ConstSpecs
import Proofs.AddSpec
import Proofs.MulSpec
import Proofs.SquareSpec
import Proofs.Square2Spec
import Proofs.Field
import Proofs.InvertSpec
import Proofs.FieldMain
import Proofs.FeQ
import Proofs.EdCurve
import Proofs.EdDenote
import Proofs.EdDouble
import Proofs.EdAddProjNiels
import Proofs.EdAddAffNiels
import Proofs.EdConvert
import Proofs.EdMain
import Proofs.DsmTableSpec
import Proofs.DsmStepSpec
import Proofs.DsmLoopSpec
import Proofs.DsmNafLoadSpec
import Proofs.DsmNafMath
import Proofs.DsmNafLoopSpec
import Proofs.DsmNafSpec
import Proofs.DsmMulSpec
import Proofs.ToBytesMath
import Proofs.ToBytesSpec
import Proofs.ScalarPackSpec
import Proofs.CompressSpec
import Proofs.SigApexSpec
import Proofs.PointLiftSpec
import Proofs.PointEqSpec
import Proofs.DecompressSpec
import Proofs.FromBytesSpec
import Proofs.DecompressMain
open Lean Ed25519Inventory

/-- Exactly the modules this driver covers. check.sh verifies, in BOTH
    directions, that the union of the two drivers' lists is its PROOFS
    manifest minus the audit infrastructure. -/
def corpus : Array Name :=
  #[`Proofs.Denote, `Proofs.P25519, `Proofs.ReduceSpec, `Proofs.SubNegSpec,
   `Proofs.ConstSpecs, `Proofs.AddSpec, `Proofs.MulSpec,
   `Proofs.SquareSpec, `Proofs.Square2Spec, `Proofs.Field,
   `Proofs.InvertSpec, `Proofs.FieldMain, `Proofs.FeQ, `Proofs.EdCurve,
   `Proofs.EdDenote, `Proofs.EdDouble, `Proofs.EdAddProjNiels,
   `Proofs.EdAddAffNiels, `Proofs.EdConvert, `Proofs.EdMain,
   `Proofs.DsmTableSpec, `Proofs.DsmStepSpec, `Proofs.DsmLoopSpec,
   `Proofs.DsmNafLoadSpec, `Proofs.DsmNafMath, `Proofs.DsmNafLoopSpec,
   `Proofs.DsmNafSpec, `Proofs.DsmMulSpec, `Proofs.ToBytesMath,
   `Proofs.ToBytesSpec, `Proofs.ScalarPackSpec, `Proofs.CompressSpec,
   `Proofs.SigApexSpec, `Proofs.PointLiftSpec, `Proofs.PointEqSpec,
   `Proofs.DecompressSpec, `Proofs.FromBytesSpec, `Proofs.DecompressMain]

-- The instruments. `Proofs.Audit` is the statement-binding driver: a member of
-- check.sh's compile manifest that was enumerated by NOTHING until 2026-07-31.
-- This module has no index while it is being elaborated, so `emitDrivers` picks
-- its own declarations up as the ones with no originating module.
def drivers : Array Name := #[`Proofs.InventoryCore, `Proofs.Audit]

#eval show MetaM Unit from emitInventory corpus
#eval show MetaM Unit from emitDrivers drivers
