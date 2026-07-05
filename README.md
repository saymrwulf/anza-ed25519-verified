# anza-ed25519-verified

Formal verification of the ed25519 implementation in **anza-xyz/cryptography (Solana, solana-ed25519 crate)**, built as a
coherent proof pyramid in Lean 4 via the Charon/Aeneas transpilation pipeline:

```
        ┌──────────────────────────────┐
        │  Signature (EdDSA verify)    │   accepted ⇔ compress([s]B−[k]A) = R
        ├──────────────────────────────┤
        │  Scalar arithmetic mod ℓ     │   Scalar52 ops correct mod ℓ
        ├──────────────────────────────┤
        │  Group law (twisted Edwards) │   point ops = complete addition law
        ├──────────────────────────────┤
        │  Field 𝔽_p, p = 2²⁵⁵ − 19    │   FieldElement51 ops correct mod p
        └──────────────────────────────┘
```

Every layer states its theorems about the **actual Aeneas-transpiled Rust
code** (never about a hand-written re-model), and every claim in the status
table below is backed by a compiled proof plus an axiom audit of the named
certificate. Files that do not compile under `verification/check.sh` are not
in this repository.

## Layer status

| Layer | Certificate | Status | Axioms of certificate |
|-------|-------------|--------|-----------------------|
| Field 𝔽_p          | `fieldImplementation`    | ✅ proven | `[propext, Classical.choice, Quot.sound]` |
| Group law (Edwards) | `edwardsImplementation`  | ✅ proven | `[propext, Classical.choice, Quot.sound]` |
| Scalar mod ℓ        | `scalarImplementation` (add ✅ sub ✅ mul ✅) | ✅ proven | `[propext, Classical.choice, Quot.sound]` |
| Signature (EdDSA)   | `verify_accepts_iff` | ✅ proven (phase 1) | standard three + the button-enforced SHA-512/wire-format boundary — see [The signature apex](#the-signature-apex-phase-1) |

Status legend: ✅ proven & axiom-audited · ⏳ in progress · ❌ not started.
This table is updated only when `verification/check.sh` passes for the layer.

## The signature apex (phase 1)

The apex certificate `CurveFieldProofs.verify_accepts_iff` is the literal EdDSA
acceptance criterion, proven about the extracted verifier:

> For a signature that parses, the verifier returns `Ok(())` **iff** the
> recomputed compressed point `compress([s]·B − [k]·A)` equals the signature's
> `R`, byte-for-byte — where `k` is whatever scalar the opaque SHA-512 oracle
> produces from `(R, A, msg)`.

The recomputation runs entirely through the **proven** model: anza's verify code lives in the **same crate** as the curve (`src/ed_sigs`), so
the whole verify path joins the one merged `gen/CurveField` extraction directly —
no glue layer, no name-welding. The `Error` enum and the parse/filter helpers are
real extracted code; only the SHA-512 oracle (`sha512_hash3`) and the foreign
`ed25519::Signature` type with its two byte accessors stay opaque — the tightest
boundary of the four sibling repos.

> **Which verifier is verified?** The certificate is about
> `VerificationKey::verify_sha512`, which is semantically identical (documented,
> pure refactor) to `VerificationKey::verify_dalek` — the dalek-style
> canonical-`R` byte-comparison path, **including** this crate's legacy filters
> (all-zero key, excluded-`R` list) and the strict `s < ℓ` check. The crate's
> *default* `verify()` uses the HEEA-accelerated Zebra/ZIP-215 path, which is a
> different acceptance criterion and is **not** covered by this certificate.

`check.sh` has a dedicated audit phase (Phase 3b) that fails the build unless
the apex certificate's axiom cone is **exactly**

`[propext, Classical.choice, Quot.sound]` + `{ed25519.Signature, ed_sigs.sha512_hash3, ed25519.Signature.r_bytes, ed25519.Signature.s_bytes}`

— i.e. the three Lean foundations plus the documented SHA-512/wire-format
boundary. Zero curve, scalar, or backend axioms. The companion certificate
`verify_loop_full` (the 32-byte comparison loop computes array equality)
carries the standard three axioms only.

**Phase 2 (deferred, documented):** lifting the byte-level equation to the
point level (`[s]B − [k]A = decompress R`) additionally needs `compress`
canonicity and a verified `decompress`; it is deliberately out of scope for
this milestone, mirroring the layer-by-layer phase split used below the apex.


## Source

- **Upstream**: [anza-xyz/cryptography](https://github.com/anza-xyz/cryptography), commit `0a54cca`
- **Pinned/patched source**: [saymrwulf/anza-cryptography-source](https://github.com/saymrwulf/anza-cryptography-source), commit `77043ab`
- **Patches**: minimal Aeneas-compatibility only (documented in the source repo)
- Closest relative of the reference solution (same crate layout as solana-ed25519).

## Toolchain (pinned)

| Component | Version |
|-----------|---------|
| Aeneas    | `bf13c42e` |
| Charon    | `9dd7f23c` |
| Lean      | `v4.30.0-rc2` |
| OCaml     | `5.3.0` |

## Reproducing

```bash
source ~/aeneas-toolchain/env.sh
cd verification
./extract.sh    # Rust → LLBC → Lean (regenerates gen/)
./check.sh      # compiles EVERY shipped file + axiom-audits EVERY certificate
```

The gen model is ONE merged universe (`gen/CurveField`: field + curve +
scalar + the verify path's reachable code), regenerated in full by
`extract.sh`. The scalar layer keeps its own check button:

```bash
./check-scalar.sh     # compiles the merged gen + all scalar proofs (add, sub,
                      # Montgomery mul, byte-parsing) and kernel-audits the
                      # scalar certificates, incl. the scalarImplementation
                      # aggregate
```


## Trusted base

See [TRUSTED-BASE.md](TRUSTED-BASE.md) for the complete list of assumptions
(Lean kernel, mathlib, Charon/Aeneas semantics, external-function models,
and — in the signature layer only — an opaque SHA-512 model).
