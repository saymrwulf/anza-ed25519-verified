# Trusted base

What you must believe for the theorems in this repository to transfer to the
running Rust code. Everything else is machine-checked.

1. **Lean 4 kernel** (v4.30.0-rc2) and its three foundational axioms
   `[propext, Classical.choice, Quot.sound]`. Every certificate is
   `#print axioms`-audited against exactly this list.
2. **mathlib** (prebuilt oleans fetched by `lake exe cache get`).
3. **Charon + Aeneas** (pinned `9dd7f23c` / `bf13c42e`): the translation
   from Rust MIR to the Lean model is assumed faithful. The generated
   `gen/` files are never edited (comments only); proofs are stated ABOUT them.
4. **External-function models** (`gen/*/FunsExternal.lean`): Rust items that
   Aeneas cannot translate (constant-time `subtle` primitives, iterator
   plumbing, formatting) are axiomatized as opaque symbols. The axiom audit
   proves none of these axioms enters the dependency cone of any certificate,
   except where a model is explicitly listed below.
5. **The signature-apex boundary (signature layer only)**: the apex
   certificate `CurveFieldProofs.verify_accepts_iff` ("the verifier accepts
   iff compress([s]·B − [k]·A) = R byte-for-byte") is `#print axioms`-audited
   by check.sh Phase 3b against EXACTLY the standard three plus this
   documented set, and the build fails on any deviation:
   `ed25519.Signature` (the foreign wire-format type), the single SHA-512
   oracle `ed_sigs.sha512_hash3` (semantically `Sha512(R ‖ A ‖ msg)`), and
   the two byte accessors `ed25519.Signature.r_bytes`/`s_bytes`. The
   `Error` enum, the parse/filter helpers, and backend selection are real
   extracted code (no axioms). The hash is an oracle with no algebraic
   properties assumed — the theorem holds for whatever bytes it produces;
   the SHA-512 implementation itself is NOT verified. The verified entry
   point is `verify_sha512` ≡ `verify_dalek` (canonical-R path), not the
   crate's default HEEA/Zebra `verify()`.
6. **Compilation of Rust to machine code** (rustc backend) is out of scope,
   as is side-channel behaviour (timing, speculation). The proofs are about
   functional correctness at the MIR/LLBC level.
