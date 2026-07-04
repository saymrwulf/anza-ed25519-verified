#!/usr/bin/env bash
# Regenerate the Lean model in gen/ from the Rust sources.
#
# SCOPE: field arithmetic + Edwards point arithmetic
#   roots: crate::field, crate::backend::serial::u64::field,
#          crate::backend::serial::curve_models, crate::edwards
#   (same widening the reference solution used for its Tier-1 addition-law
#    theorem; scalar-mul backends and decompress internals stay opaque —
#    upstream Aeneas cannot translate them; they are modeled/axiomatized in
#    gen/CurveField/FunsExternal.lean OUTSIDE every certificate's cone).
#
#   Rust --charon--> CurveField.llbc --aeneas--> gen/CurveField/*.lean
#
# The hand-written gen/CurveField/{TypesExternal,FunsExternal}.lean are NOT
# touched by regeneration (Aeneas only rewrites the *_Template variants).
# After regenerating, diff the templates against the hand-written files:
#   diff gen/CurveField/FunsExternal_Template.lean gen/CurveField/FunsExternal.lean
#
# Usage:  ./extract.sh
set -euo pipefail

source ~/aeneas-toolchain/env.sh
HERE="$(cd "$(dirname "$0")" && pwd)"
CRATE=~/GitClone/FormalVerification/sources/anza-cryptography-source/curve25519/solana-ed25519

echo "[1/2] charon: Rust -> LLBC (field + curve_models + edwards + scalar + verify [MERGED GEN])"
cd "$CRATE"
# Pin the serial backend: the AVX2 dispatch arm compiles out, so backend
# selection extracts as the real constant Serial (no dispatch axiom).
export RUSTFLAGS='--cfg curve25519_serial_only'
cargo clean -p solana-ed25519 2>/dev/null || true
charon cargo --preset=aeneas \
  --start-from crate::field \
  --start-from crate::backend::serial::u64::field \
  --start-from crate::backend::serial::curve_models \
  --start-from crate::edwards \
  --start-from 'crate::backend::serial::u64::scalar::_::add' \
  --start-from 'crate::backend::serial::u64::scalar::_::sub' \
  --start-from 'crate::backend::serial::u64::scalar::_::mul' \
  --start-from 'crate::backend::serial::u64::scalar::_::square' \
  --start-from 'crate::backend::serial::u64::scalar::_::montgomery_mul' \
  --start-from 'crate::backend::serial::u64::scalar::_::montgomery_square' \
  --start-from 'crate::backend::serial::u64::scalar::_::montgomery_reduce' \
  --start-from 'crate::backend::serial::u64::scalar::_::montgomery_invert' \
  --start-from 'crate::backend::serial::u64::scalar::_::as_montgomery' \
  --start-from 'crate::backend::serial::u64::scalar::_::from_montgomery' \
  --start-from 'crate::backend::serial::u64::scalar::_::from_bytes_wide' \
  --start-from 'crate::scalar::_::from_bytes_mod_order' \
  --start-from 'crate::scalar::_::from_bytes_mod_order_wide' \
  --start-from 'crate::ed_sigs::verification_key::_::verify_sha512' \
  --opaque 'crate::ed_sigs::sha512_hash3' \
  --opaque 'ed25519' \
  --opaque 'crate::field::_::internal_invert_batch' \
  --opaque 'crate::backend::serial::scalar_mul::variable_base' \
  --opaque 'crate::backend::serial::scalar_mul::vartime_triple_base' \
  --opaque 'crate::scalar::_::non_adjacent_form_128' \
  --opaque 'crate::backend::serial::scalar_mul::straus' \
  --opaque 'crate::backend::serial::scalar_mul::precomputed_straus' \
  --opaque 'crate::backend::serial::scalar_mul::pippenger' \
  --opaque 'crate::backend::vector' \
  --opaque 'crate::backend::scalar_fits_in_128_bits' \
  --opaque 'crate::edwards::decompress' \
  --opaque 'crate::edwards::_::sum' \
  --opaque 'crate::edwards::_::from_slice' \
  --dest-file "$HERE/CurveField.llbc" \
  -- --no-default-features

echo "[2/2] aeneas: LLBC -> Lean (split files, CurveField.* modules)"
cd "$HERE"
aeneas -backend lean -split-files -subdir CurveField -dest gen CurveField.llbc

echo "Done. Now run ./check.sh to type-check the regenerated model."
