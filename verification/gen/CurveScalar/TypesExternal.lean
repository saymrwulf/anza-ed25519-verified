-- Hand-written external types for the Scalar52 arithmetic extraction.
-- Self-contained; subtle.Choice modeled as the {0,1} u8 (same as the field layer).
import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

/-- [subtle::Choice] — MODEL: a u8 carrying the {0,1} invariant. -/
@[reducible, rust_type "subtle::Choice"]
def subtle.Choice : Type := Std.U8
