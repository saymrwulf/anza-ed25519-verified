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
5. **The signature-apex boundary (signature layer only)**: FOUR apex-tier
   certificates — `CurveFieldProofs.verify_accepts_iff` (byte apex:
   accepted iff compress([s]·B − [k]·A) = R byte-for-byte),
   `verify_accepts_iff_point` (half-lift: R is the canonical encoding of
   the recomputed point), `verify_accepts_iff_point_eq` (point equation:
   canonically-encoded Q accepted iff Q equals the recomputed point), and
   `verify_accepts_iff_decompress` (full lift: R decompresses to a valid
   on-curve point that equals the recomputed point) — are each
   `#print axioms`-audited by check.sh Phase 3b against EXACTLY the
   standard three plus this documented set, and the build fails on any
   deviation:
   `ed25519.Signature` (the foreign wire-format type), the single SHA-512
   oracle `ed_sigs.sha512_hash3` (semantically `Sha512(R ‖ A ‖ msg)`), and
   the two byte accessors `ed25519.Signature.r_bytes`/`s_bytes`. The
   `Error` enum, the parse/filter helpers, and backend selection are real
   extracted code (no axioms). The hash is an oracle with no algebraic
   properties assumed — the theorems hold for whatever bytes it produces;
   the SHA-512 implementation itself is NOT verified. The verified entry
   point is `verify_sha512` ≡ `verify_dalek` (canonical-R path), not the
   crate's default HEEA/Zebra `verify()`. The constructive decompress theorem underneath the full lift
   (`decompress_of_canonical`) carries the standard three axioms ONLY.
6. **Compilation of Rust to machine code** (rustc backend) is out of scope,
   as is side-channel behaviour (timing, speculation). The proofs are about
   functional correctness at the MIR/LLBC level.
7. **What the axiom gate binds, and what it does not.** `check.sh` Phase 2b
   reads every compiled `Proofs/*.olean` and fails the build if any
   declaration there is an axiom. It asks the kernel rather than parsing
   source text, because the source-text check in Phase 1 is evadable four
   ways — an indented `axiom`, `@[simp] axiom`, `unsafe axiom`, and `axiom`
   with the name on the following line all compile and all miss its pattern.
   Membership self-derives from the filesystem, so `Scalar*` and `AxiomCheck`
   are covered as well, and the count of compiled modules must equal the
   count of shipped sources, so a deleted `.olean` cannot make the scan pass
   vacuously. `selftest-axgate.sh` attacks the shipping gate rather than a
   copy of it, and was itself negative-tested by removing the gate's error.
   **The residue you must still supply yourself:** this binds *declarations*,
   not *statements*. Nothing in the button establishes that a certificate's
   theorem says what its name — or this document — suggests it says. A
   theorem gutted to a tautology with the same axiom cone would pass every
   phase. Reading the statements remains a human act.
