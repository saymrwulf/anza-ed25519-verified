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
5. **SHA-512 (signature layer only)**: the hash is modeled as an opaque
   function ℬ* → ℬ⁶⁴ with no algebraic properties assumed. The signature
   certificate has the shape "IF the hash model computes SHA-512, THEN an
   accepted signature satisfies the EdDSA verification equation". The hash
   implementation itself is NOT verified.
6. **Compilation of Rust to machine code** (rustc backend) is out of scope,
   as is side-channel behaviour (timing, speculation). The proofs are about
   functional correctness at the MIR/LLBC level.
