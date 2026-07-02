-- Hand-written models for external types (derived from TypesExternal_Template.lean).
-- [curve25519]: external types.
import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048

/-- [subtle::Choice]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 120:0-120:17
    Name pattern: [subtle::Choice]

    MODEL: `Choice` is a transparent `u8` newtype carrying the (informal)
    invariant that its value is 0 or 1. The wrapper exists in Rust purely as an
    optimization barrier (`black_box` volatile read), which is semantically the
    identity, so we model the type as `U8` directly. -/
@[reducible, rust_type "subtle::Choice"]
def subtle.Choice : Type := Std.U8
