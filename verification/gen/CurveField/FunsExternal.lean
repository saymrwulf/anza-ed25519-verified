-- Hand-written models for external functions (derived from FunsExternal_Template.lean).
-- [curve25519]: external functions.
--
-- Modeling policy (see ../../README.md):
--  * `subtle` items whose Rust bodies are real bit math are modeled FAITHFULLY
--    (bitwise or, mask-based select collapses to if-then-else only on the
--    documented {0,1} Choice invariant — noted per item).
--  * `subtle` items whose Rust bodies are optimization barriers
--    (`black_box`/volatile reads) are semantically the identity and modeled so.
--  * core RangeFull slice indexing (`s[..]`) is the identity on the slice.
--  * Remaining axioms (Debug fmt, raw-pointer get_unchecked*, the deliberately
--    opaque `internal_invert_batch`) carry no semantics field proofs rely on.
import Aeneas
import CurveField.Types
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048
open curve25519

/-- [core::fmt::{impl core::fmt::Debug for [T]}::fmt]:
    Source: '/rustc/library/core/src/fmt/mod.rs', lines 3122:4-3122:50
    Name pattern: [core::fmt::{core::fmt::Debug<[@T]>}::fmt]
    Visibility: public

    AXIOM: only reachable from the `Debug` impl; no field proof depends on it. -/
@[rust_fun "core::fmt::{core::fmt::Debug<[@T]>}::fmt"]
axiom Slice.Insts.CoreFmtDebug.fmt
  {T : Type} (DebugInst : core.fmt.Debug T) :
  Slice T → core.fmt.Formatter → Result ((core.result.Result Unit
    core.fmt.Error) × core.fmt.Formatter)

/-- [core::slice::index::{impl core::slice::index::SliceIndex<[T], [T]> for core::ops::range::RangeFull}::index_mut]:
    Source: '/rustc/library/core/src/slice/index.rs', lines 660:4-660:51
    Name pattern: [core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::index_mut]

    MODEL: `&mut s[..]` is the whole slice; the backward function is the
    identity update. -/
@[rust_fun
  "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::index_mut"]
def
  core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut
  {T : Type} (_ : core.ops.range.RangeFull) (s : Slice T) :
  Result ((Slice T) × (Slice T → Slice T)) :=
  ok (s, fun s' => s')

/-- [core::slice::index::{impl core::slice::index::SliceIndex<[T], [T]> for core::ops::range::RangeFull}::index]:
    Source: '/rustc/library/core/src/slice/index.rs', lines 655:4-655:39
    Name pattern: [core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::index]

    MODEL: `&s[..]` is the whole slice. -/
@[rust_fun
  "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::index"]
def core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index
  {T : Type} (_ : core.ops.range.RangeFull) (s : Slice T) :
  Result (Slice T) :=
  ok s

/-- [core::slice::index::{impl core::slice::index::SliceIndex<[T], [T]> for core::ops::range::RangeFull}::get_unchecked_mut]:
    Source: '/rustc/library/core/src/slice/index.rs', lines 650:4-650:66
    Name pattern: [core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get_unchecked_mut]

    AXIOM: raw-pointer API, never called by the extracted field code. -/
@[rust_fun
  "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get_unchecked_mut"]
axiom
  core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut
  {T : Type} :
  core.ops.range.RangeFull → MutRawPtr (Slice T) → Result (MutRawPtr (Slice
    T))

/-- [core::slice::index::{impl core::slice::index::SliceIndex<[T], [T]> for core::ops::range::RangeFull}::get_unchecked]:
    Source: '/rustc/library/core/src/slice/index.rs', lines 645:4-645:66
    Name pattern: [core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get_unchecked]

    AXIOM: raw-pointer API, never called by the extracted field code. -/
@[rust_fun
  "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get_unchecked"]
axiom
  core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked
  {T : Type} :
  core.ops.range.RangeFull → ConstRawPtr (Slice T) → Result (ConstRawPtr
    (Slice T))

/-- [core::slice::index::{impl core::slice::index::SliceIndex<[T], [T]> for core::ops::range::RangeFull}::get_mut]:
    Source: '/rustc/library/core/src/slice/index.rs', lines 640:4-640:57
    Name pattern: [core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get_mut]

    MODEL: always `some` (RangeFull never fails); backward function folds an
    updated `some` back into the slice and keeps the original on `none`. -/
@[rust_fun
  "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get_mut"]
def core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut
  {T : Type} (_ : core.ops.range.RangeFull) (s : Slice T) :
  Result ((Option (Slice T)) × (Option (Slice T) → Slice T)) :=
  ok (some s, fun o => o.getD s)

/-- [core::slice::index::{impl core::slice::index::SliceIndex<[T], [T]> for core::ops::range::RangeFull}::get]:
    Source: '/rustc/library/core/src/slice/index.rs', lines 635:4-635:45
    Name pattern: [core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get]

    MODEL: always `some` (RangeFull never fails). -/
@[rust_fun
  "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get"]
def core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get
  {T : Type} (_ : core.ops.range.RangeFull) (s : Slice T) :
  Result (Option (Slice T)) :=
  ok (some s)

/-- [subtle::{impl core::convert::From<subtle::Choice> for bool}::from]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 153:4-153:35
    Name pattern: [subtle::{core::convert::From<bool, subtle::Choice>}::from]

    MODEL (faithful): Rust body is `source.0 != 0`. -/
@[rust_fun "subtle::{core::convert::From<bool, subtle::Choice>}::from"]
def Bool.Insts.CoreConvertFromChoice.from (c : subtle.Choice) : Result Bool :=
  ok (c.val != 0)

/-- [subtle::{impl core::ops::bit::BitOr<subtle::Choice, subtle::Choice> for subtle::Choice}::bitor]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 177:4-177:41
    Name pattern: [subtle::{core::ops::bit::BitOr<subtle::Choice, subtle::Choice, subtle::Choice>}::bitor]

    MODEL (faithful): Rust body is `(self.0 | rhs.0).into()`, and the `.into()`
    (`Choice::from`) is an optimization barrier = identity. Bitwise or on u8. -/
@[rust_fun
  "subtle::{core::ops::bit::BitOr<subtle::Choice, subtle::Choice, subtle::Choice>}::bitor"]
def subtle.Choice.Insts.CoreOpsBitBitOrChoiceChoice.bitor
  (a b : subtle.Choice) : Result subtle.Choice :=
  ok (a ||| b)

/-- [subtle::{impl core::convert::From<u8> for subtle::Choice}::from]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 238:4-238:32
    Name pattern: [subtle::{core::convert::From<subtle::Choice, u8>}::from]

    MODEL (faithful): Rust body is `Choice(black_box(input))`; the volatile
    read in `black_box` is semantically the identity. -/
@[rust_fun "subtle::{core::convert::From<subtle::Choice, u8>}::from"]
def subtle.Choice.Insts.CoreConvertFromU8.from
  (b : Std.U8) : Result subtle.Choice :=
  ok b

/-- [subtle::{impl subtle::ConstantTimeEq for [T]}::ct_eq]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 313:4-313:41
    Name pattern: [subtle::{subtle::ConstantTimeEq<[@T]>}::ct_eq]

    MODEL: 1 iff the slices are equal (length + elementwise), else 0.
    CAVEAT: this equates `ConstantTimeEqInst.ct_eq` with logical equality on
    `T`. That is exact for the only instantiation reachable from the field
    code (`T = u8`, whose `ct_eq` is genuine equality); a hypothetical exotic
    `ConstantTimeEq` instance would not be modeled faithfully. -/
@[rust_fun "subtle::{subtle::ConstantTimeEq<[@T]>}::ct_eq"]
noncomputable def Slice.Insts.SubtleConstantTimeEq.ct_eq
  {T : Type} (ConstantTimeEqInst : subtle.ConstantTimeEq T)
  (a b : Slice T) : Result subtle.Choice :=
  open Classical in
  ok (if a.val = b.val then 1#u8 else 0#u8)

/-- [subtle::{impl subtle::ConstantTimeEq for u8}::ct_eq]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 348:12-348:51
    Name pattern: [subtle::{subtle::ConstantTimeEq<u8>}::ct_eq]

    MODEL: 1 iff equal, else 0 — the specification the Rust xor/shift bit
    trick implements for all inputs. -/
@[rust_fun "subtle::{subtle::ConstantTimeEq<u8>}::ct_eq"]
def U8.Insts.SubtleConstantTimeEq.ct_eq
  (a b : Std.U8) : Result subtle.Choice :=
  ok (if a = b then 1#u8 else 0#u8)

/-- [subtle::ConditionallySelectable::conditional_assign]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 442:4-442:66
    Name pattern: [subtle::ConditionallySelectable::conditional_assign]

    MODEL (faithful): the trait's default body is
    `*self = Self::conditional_select(self, other, choice)`. -/
@[rust_fun "subtle::ConditionallySelectable::conditional_assign"]
def subtle.ConditionallySelectable.conditional_assign.default
  {Self : Type} (ConditionallySelectableInst : subtle.ConditionallySelectable
  Self) (self other : Self) (choice : subtle.Choice) : Result Self :=
  ConditionallySelectableInst.conditional_select self other choice

/-- [subtle::ConditionallySelectable::conditional_swap]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 469:4-469:67
    Name pattern: [subtle::ConditionallySelectable::conditional_swap]

    MODEL (faithful): the trait's default body conditionally assigns each side
    the other's original value. -/
@[rust_fun "subtle::ConditionallySelectable::conditional_swap"]
def subtle.ConditionallySelectable.conditional_swap.default
  {Self : Type} (ConditionallySelectableInst : subtle.ConditionallySelectable
  Self) (a b : Self) (choice : subtle.Choice) : Result (Self × Self) := do
  let a1 ← ConditionallySelectableInst.conditional_assign a b choice
  let b1 ← ConditionallySelectableInst.conditional_assign b a choice
  ok (a1, b1)

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

/-- [subtle::{impl subtle::ConditionallySelectable for u64}::conditional_assign]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 521:12-521:74
    Name pattern: [subtle::{subtle::ConditionallySelectable<u64>}::conditional_assign]

    MODEL: keep `self` if choice = 0, else take `other` (same mask trick). -/
@[rust_fun
  "subtle::{subtle::ConditionallySelectable<u64>}::conditional_assign"]
def U64.Insts.SubtleConditionallySelectable.conditional_assign
  (self other : Std.U64) (choice : subtle.Choice) : Result Std.U64 :=
  ok (if choice.val = 0 then self else other)

/-- [subtle::{impl subtle::ConditionallySelectable for u64}::conditional_swap]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 529:12-529:75
    Name pattern: [subtle::{subtle::ConditionallySelectable<u64>}::conditional_swap]

    MODEL: swap iff choice ≠ 0 (same mask trick, applied to both sides). -/
@[rust_fun "subtle::{subtle::ConditionallySelectable<u64>}::conditional_swap"]
def U64.Insts.SubtleConditionallySelectable.conditional_swap
  (a b : Std.U64) (choice : subtle.Choice) : Result (Std.U64 × Std.U64) :=
  ok (if choice.val = 0 then (a, b) else (b, a))

/-- [curve25519::field::{curve25519::backend::serial::u64::field::FieldElement51}::internal_invert_batch]:
    Source: 'curve25519/solana-ed25519/src/field.rs', lines 195:4-229:5

    AXIOM (deliberate): extracted opaque via charon `--opaque`. Dead code under
    the extraction feature set (its only caller `invert_batch_alloc` is
    alloc-gated); its iterator `rev/zip` loops have no Aeneas model. Give it a
    model here if batch inversion ever becomes a verification target. -/
axiom field.FieldElement51.internal_invert_batch
  :
  Slice backend.serial.u64.field.FieldElement51 → Slice
    backend.serial.u64.field.FieldElement51 → Result ((Slice
    backend.serial.u64.field.FieldElement51) × (Slice
    backend.serial.u64.field.FieldElement51))
