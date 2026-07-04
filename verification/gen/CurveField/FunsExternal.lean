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

/-- [core::array::{impl core::hash::Hash for [T; N]}::hash]:
    Source: '/rustc/library/core/src/array/mod.rs', lines 349:4-349:50
    Name pattern: [core::array::{core::hash::Hash<[@T; @N]>}::hash]
    Visibility: public -/
@[rust_fun "core::array::{core::hash::Hash<[@T; @N]>}::hash"]
axiom Array.Insts.CoreHashHash.hash
  {T : Type} {H : Type} {N : Std.Usize} (hashHashInst : core.hash.Hash T)
  (hashHasherInst : core.hash.Hasher H) :
  Array T N → H → Result H

/-- [core::fmt::{core::fmt::Formatter<'a>}::debug_struct_field2_finish]:
    Source: '/rustc/library/core/src/fmt/mod.rs', lines 2473:4-2480:15
    Name pattern: [core::fmt::{core::fmt::Formatter<'a>}::debug_struct_field2_finish]
    Visibility: public -/
@[rust_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_struct_field2_finish"]
axiom core.fmt.Formatter.debug_struct_field2_finish
  :
  core.fmt.Formatter → Str → Str → Dyn (fun _dyn => core.fmt.Debug _dyn)
    → Str → Dyn (fun _dyn => core.fmt.Debug _dyn) → Result
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)

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

/-- [core::hash::impls::{impl core::hash::Hash for u8}::hash]:
    Source: '/rustc/library/core/src/hash/mod.rs', lines 812:16-812:56
    Name pattern: [core::hash::impls::{core::hash::Hash<u8>}::hash]
    Visibility: public -/
@[rust_fun "core::hash::impls::{core::hash::Hash<u8>}::hash"]
axiom U8.Insts.CoreHashHash.hash
  {H : Type} (HasherInst : core.hash.Hasher H) : Std.U8 → H → Result H

/-- [core::iter::range::{impl core::iter::range::Step for u32}::backward_checked]:
    Source: '/rustc/library/core/src/iter/range.rs', lines 290:16-290:74
    Name pattern: [core::iter::range::{core::iter::range::Step<u32>}::backward_checked]
    Visibility: public -/
@[rust_fun
  "core::iter::range::{core::iter::range::Step<u32>}::backward_checked"]
axiom U32.Insts.CoreIterRangeStep.backward_checked
  : Std.U32 → Std.Usize → Result (Option Std.U32)

/-- [core::iter::range::{impl core::iter::range::Step for u32}::forward_checked]:
    Source: '/rustc/library/core/src/iter/range.rs', lines 282:16-282:73
    Name pattern: [core::iter::range::{core::iter::range::Step<u32>}::forward_checked]
    Visibility: public -/
@[rust_fun
  "core::iter::range::{core::iter::range::Step<u32>}::forward_checked"]
axiom U32.Insts.CoreIterRangeStep.forward_checked
  : Std.U32 → Std.Usize → Result (Option Std.U32)

/-- [core::iter::range::{impl core::iter::range::Step for u32}::steps_between]:
    Source: '/rustc/library/core/src/iter/range.rs', lines 271:16-271:84
    Name pattern: [core::iter::range::{core::iter::range::Step<u32>}::steps_between]
    Visibility: public -/
@[rust_fun "core::iter::range::{core::iter::range::Step<u32>}::steps_between"]
axiom U32.Insts.CoreIterRangeStep.steps_between
  : Std.U32 → Std.U32 → Result (Std.Usize × (Option Std.Usize))

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

/-- [subtle::{subtle::Choice}::unwrap_u8]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 133:4-133:33
    Name pattern: [subtle::{subtle::Choice}::unwrap_u8]
    Visibility: public -/
@[rust_fun "subtle::{subtle::Choice}::unwrap_u8"]
axiom subtle.Choice.unwrap_u8 : subtle.Choice → Result Std.U8

/-- [subtle::{impl core::convert::From<subtle::Choice> for bool}::from]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 153:4-153:35
    Name pattern: [subtle::{core::convert::From<bool, subtle::Choice>}::from]

    MODEL (faithful): Rust body is `source.0 != 0`. -/
@[rust_fun "subtle::{core::convert::From<bool, subtle::Choice>}::from"]
def Bool.Insts.CoreConvertFromChoice.from (c : subtle.Choice) : Result Bool :=
  ok (c.val != 0)

/-- [subtle::{impl core::ops::bit::BitAnd<subtle::Choice, subtle::Choice> for subtle::Choice}::bitand]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 162:4-162:42
    Name pattern: [subtle::{core::ops::bit::BitAnd<subtle::Choice, subtle::Choice, subtle::Choice>}::bitand]
    Visibility: public -/
@[rust_fun
  "subtle::{core::ops::bit::BitAnd<subtle::Choice, subtle::Choice, subtle::Choice>}::bitand"]
axiom subtle.Choice.Insts.CoreOpsBitBitAndChoiceChoice.bitand
  : subtle.Choice → subtle.Choice → Result subtle.Choice

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

/-- [curve25519::backend::serial::curve_models::{impl subtle::ConditionallySelectable for curve25519::backend::serial::curve_models::ProjectiveNielsPoint}::conditional_swap]:
    Source: 'curve25519/solana-ed25519/src/backend/serial/curve_models.rs', lines 295:0-311:1
    Visibility: public -/
axiom
  backend.serial.curve_models.ProjectiveNielsPoint.Insts.SubtleConditionallySelectable.conditional_swap
  :
  backend.serial.curve_models.ProjectiveNielsPoint →
    backend.serial.curve_models.ProjectiveNielsPoint → subtle.Choice →
    Result (backend.serial.curve_models.ProjectiveNielsPoint ×
    backend.serial.curve_models.ProjectiveNielsPoint)

/-- [curve25519::backend::serial::curve_models::{impl subtle::ConditionallySelectable for curve25519::backend::serial::curve_models::AffineNielsPoint}::conditional_swap]:
    Source: 'curve25519/solana-ed25519/src/backend/serial/curve_models.rs', lines 313:0-327:1
    Visibility: public -/
axiom
  backend.serial.curve_models.AffineNielsPoint.Insts.SubtleConditionallySelectable.conditional_swap
  :
  backend.serial.curve_models.AffineNielsPoint →
    backend.serial.curve_models.AffineNielsPoint → subtle.Choice → Result
    (backend.serial.curve_models.AffineNielsPoint ×
    backend.serial.curve_models.AffineNielsPoint)

/-- [curve25519::backend::serial::scalar_mul::variable_base::mul]:
    Source: 'curve25519/solana-ed25519/src/backend/serial/scalar_mul/variable_base.rs', lines 11:0-48:1 -/
axiom backend.serial.scalar_mul.variable_base.mul
  : edwards.EdwardsPoint → scalar.Scalar → Result edwards.EdwardsPoint

/-- [curve25519::backend::serial::scalar_mul::vartime_triple_base::mul_128_128_256_prechecked]:
    Source: 'curve25519/solana-ed25519/src/backend/serial/scalar_mul/vartime_triple_base.rs', lines 68:0-168:1 -/
axiom backend.serial.scalar_mul.vartime_triple_base.mul_128_128_256_prechecked
  :
  scalar.Scalar → edwards.EdwardsPoint → scalar.Scalar →
    edwards.EdwardsPoint → scalar.Scalar → Result edwards.EdwardsPoint

/-- [curve25519::backend::vector::scalar_mul::variable_base::spec_avx2::mul]:
    Source: 'curve25519/solana-ed25519/src/backend/vector/scalar_mul/variable_base.rs', lines 3:0-3:68
    Visibility: public -/
axiom backend.vector.scalar_mul.variable_base.spec_avx2.mul
  : edwards.EdwardsPoint → scalar.Scalar → Result edwards.EdwardsPoint

/-- [curve25519::backend::vector::scalar_mul::vartime_double_base::spec_avx2::mul]:
    Source: 'curve25519/solana-ed25519/src/backend/vector/scalar_mul/vartime_double_base.rs', lines 14:0-14:68
    Visibility: public -/
axiom backend.vector.scalar_mul.vartime_double_base.spec_avx2.mul
  :
  scalar.Scalar → edwards.EdwardsPoint → scalar.Scalar → Result
    edwards.EdwardsPoint

/-- [curve25519::backend::vector::scalar_mul::vartime_triple_base::spec_avx2::mul_128_128_256_prechecked]:
    Source: 'curve25519/solana-ed25519/src/backend/vector/scalar_mul/vartime_triple_base.rs', lines 10:0-10:68 -/
axiom
  backend.vector.scalar_mul.vartime_triple_base.spec_avx2.mul_128_128_256_prechecked
  :
  scalar.Scalar → edwards.EdwardsPoint → scalar.Scalar →
    edwards.EdwardsPoint → scalar.Scalar → Result edwards.EdwardsPoint

/-- [curve25519::backend::get_selected_backend]:
    Source: 'curve25519/solana-ed25519/src/backend.rs', lines 53:0-64:1 -/
axiom backend.get_selected_backend : Result backend.BackendKind

/-- [curve25519::backend::scalar_fits_in_128_bits]:
    Source: 'curve25519/solana-ed25519/src/backend.rs', lines 283:0-285:1 -/
axiom backend.scalar_fits_in_128_bits : scalar.Scalar → Result Bool

/-- [curve25519::edwards::affine::{impl subtle::ConditionallySelectable for curve25519::edwards::affine::AffinePoint}::conditional_swap]:
    Source: 'curve25519/solana-ed25519/src/edwards/affine.rs', lines 23:0-30:1
    Visibility: public -/
axiom
  edwards.affine.AffinePoint.Insts.SubtleConditionallySelectable.conditional_swap
  :
  edwards.affine.AffinePoint → edwards.affine.AffinePoint → subtle.Choice
    → Result (edwards.affine.AffinePoint × edwards.affine.AffinePoint)

/-- [curve25519::edwards::affine::{impl subtle::ConditionallySelectable for curve25519::edwards::affine::AffinePoint}::conditional_assign]:
    Source: 'curve25519/solana-ed25519/src/edwards/affine.rs', lines 23:0-30:1
    Visibility: public -/
axiom
  edwards.affine.AffinePoint.Insts.SubtleConditionallySelectable.conditional_assign
  :
  edwards.affine.AffinePoint → edwards.affine.AffinePoint → subtle.Choice
    → Result edwards.affine.AffinePoint

/-- [curve25519::edwards::affine::{impl core::cmp::Eq for curve25519::edwards::affine::AffinePoint}::assert_fields_are_eq]:
    Source: 'curve25519/solana-ed25519/src/edwards/affine.rs', lines 53:0-53:26
    Visibility: public -/
axiom edwards.affine.AffinePoint.Insts.CoreCmpEq.assert_fields_are_eq
  : edwards.affine.AffinePoint → Result Unit

/-- [curve25519::edwards::{impl core::cmp::Eq for curve25519::edwards::CompressedEdwardsY}::assert_fields_are_eq]:
    Source: 'curve25519/solana-ed25519/src/edwards.rs', lines 183:0-183:33
    Visibility: public -/
axiom edwards.CompressedEdwardsY.Insts.CoreCmpEq.assert_fields_are_eq
  : edwards.CompressedEdwardsY → Result Unit

/-- [curve25519::edwards::decompress::step_2]:
    Source: 'curve25519/solana-ed25519/src/edwards.rs', lines 240:4-257:5 -/
axiom edwards.decompress.step_2
  :
  edwards.CompressedEdwardsY → backend.serial.u64.field.FieldElement51 →
    backend.serial.u64.field.FieldElement51 →
    backend.serial.u64.field.FieldElement51 → Result edwards.EdwardsPoint

/-- [curve25519::edwards::decompress::step_1]:
    Source: 'curve25519/solana-ed25519/src/edwards.rs', lines 226:4-237:5 -/
axiom edwards.decompress.step_1
  :
  edwards.CompressedEdwardsY → Result (subtle.Choice ×
    backend.serial.u64.field.FieldElement51 ×
    backend.serial.u64.field.FieldElement51 ×
    backend.serial.u64.field.FieldElement51)

/-- [curve25519::edwards::{curve25519::edwards::CompressedEdwardsY}::from_slice]:
    Source: 'curve25519/solana-ed25519/src/edwards.rs', lines 423:4-425:5
    Visibility: public -/
axiom edwards.CompressedEdwardsY.from_slice
  :
  Slice Std.U8 → Result (core.result.Result edwards.CompressedEdwardsY
    core.array.TryFromSliceError)

/-- [curve25519::edwards::{impl subtle::ConditionallySelectable for curve25519::edwards::EdwardsPoint}::conditional_swap]:
    Source: 'curve25519/solana-ed25519/src/edwards.rs', lines 486:0-495:1
    Visibility: public -/
axiom edwards.EdwardsPoint.Insts.SubtleConditionallySelectable.conditional_swap
  :
  edwards.EdwardsPoint → edwards.EdwardsPoint → subtle.Choice → Result
    (edwards.EdwardsPoint × edwards.EdwardsPoint)

/-- [curve25519::edwards::{impl subtle::ConditionallySelectable for curve25519::edwards::EdwardsPoint}::conditional_assign]:
    Source: 'curve25519/solana-ed25519/src/edwards.rs', lines 486:0-495:1
    Visibility: public -/
axiom
  edwards.EdwardsPoint.Insts.SubtleConditionallySelectable.conditional_assign
  :
  edwards.EdwardsPoint → edwards.EdwardsPoint → subtle.Choice → Result
    edwards.EdwardsPoint

/-- [curve25519::edwards::{impl core::cmp::Eq for curve25519::edwards::EdwardsPoint}::assert_fields_are_eq]:
    Source: 'curve25519/solana-ed25519/src/edwards.rs', lines 520:0-520:27
    Visibility: public -/
axiom edwards.EdwardsPoint.Insts.CoreCmpEq.assert_fields_are_eq
  : edwards.EdwardsPoint → Result Unit

/-- [curve25519::edwards::{impl core::iter::traits::accum::Sum<T> for curve25519::edwards::EdwardsPoint}::sum]:
    Source: 'curve25519/solana-ed25519/src/edwards.rs', lines 829:4-834:5
    Visibility: public -/
axiom edwards.EdwardsPoint.Insts.CoreIterTraitsAccumSum.sum
  {T : Type} {I : Type} (coreborrowBorrowTEdwardsPointInst : core.borrow.Borrow
  T edwards.EdwardsPoint) (coreitertraitsiteratorIteratorInst :
  core.iter.traits.iterator.Iterator I T) :
  I → Result edwards.EdwardsPoint

/-- [curve25519::field::{impl core::cmp::Eq for curve25519::backend::serial::u64::field::FieldElement51}::assert_fields_are_eq]:
    Source: 'curve25519/solana-ed25519/src/field.rs', lines 52:0-52:27
    Visibility: public -/
axiom
  backend.serial.u64.field.FieldElement51.Insts.CoreCmpEq.assert_fields_are_eq
  : backend.serial.u64.field.FieldElement51 → Result Unit

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
