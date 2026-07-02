#!/usr/bin/env bash
# Regenerate the SCALAR-layer Lean model (gen/CurveScalar) from Rust.
#
# SCOPE: the Scalar52 limb backend (backend::serial::u64::scalar) — the
#   iterator-free ARITHMETIC core: add/sub/mul/square/montgomery_reduce/
#   from_bytes/to_bytes mod ℓ = 2²⁵² + 27742317777372353535851937790883648493.
#   The high-level crate::scalar wrapper (Sum/Product/NAF/radix/byte-parsing,
#   all iterator-heavy) is brought in only for the signature layer.
set -euo pipefail
source ~/aeneas-toolchain/env.sh
HERE="$(cd "$(dirname "$0")" && pwd)"
CRATE=~/GitClone/FormalVerification/sources/anza-cryptography-source/curve25519/solana-ed25519

echo "[1/2] charon: Rust -> LLBC (scalar + Scalar52)"
cd "$CRATE"
charon cargo --preset=aeneas \
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
  --dest-file "$HERE/CurveScalar.llbc" \
  -- --no-default-features

echo "[2/2] aeneas: LLBC -> Lean (split files, CurveScalar.* modules)"
cd "$HERE"
aeneas -backend lean -split-files -subdir CurveScalar -dest gen CurveScalar.llbc
echo "Done."
