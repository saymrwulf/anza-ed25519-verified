-- Hand-written external function models for the Scalar52 arithmetic extraction.
-- The two subtle items reuse the field extraction's proven models verbatim.
import Aeneas
import CurveScalar.Types
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
open curve25519

/-- [subtle::{impl core::convert::From<u8> for subtle::Choice}::from]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 238:4-238:32
    Name pattern: [subtle::{core::convert::From<subtle::Choice, u8>}::from]

    MODEL (faithful): Rust body is `Choice(black_box(input))`; the volatile
    read in `black_box` is semantically the identity. -/
@[rust_fun "subtle::{core::convert::From<subtle::Choice, u8>}::from"]
def subtle.Choice.Insts.CoreConvertFromU8.from
  (b : Std.U8) : Result subtle.Choice :=
  ok b

/-- [subtle::{impl subtle::ConditionallySelectable for u64}::conditional_select]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 513:12-513:77
    Name pattern: [subtle::{subtle::ConditionallySelectable<u64>}::conditional_select]

    MODEL: `a` if choice = 0, else `b`. The Rust mask trick
    `a ^ (-(choice as i64) as u64 & (a ^ b))` agrees with this on the Choice
    invariant {0,1} (mask = 0 or all-ones). -/
@[rust_fun
  "subtle::{subtle::ConditionallySelectable<u64>}::conditional_select"]
def U64.Insts.SubtleConditionallySelectable.conditional_select
  (a b : Std.U64) (choice : subtle.Choice) : Result Std.U64 :=
  ok (if choice.val = 0 then a else b)

