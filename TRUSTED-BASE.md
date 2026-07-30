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
8. **What the statement binding covers.** `check.sh` Phase 3c compiles
   `Proofs/Audit.lean`, which emits a canonical block containing the policy
   constants, every certificate's fully-elaborated statement (`pp.all`, so
   implicit arguments, instances and universe levels are all visible), and the
   fully-elaborated body of every specification constant transitively
   reachable from those statements. The SHA-256 of that block is pinned in
   `check.sh` and the block itself is committed as `AUDIT-MANIFEST.txt`, so a
   mismatch is diffed rather than merely reported. This is what makes a
   certificate gutted to a tautology of the same axiom cone fail, and what
   makes a reference definition redefined to BE the extracted code fail — two
   attacks that move no cone at all. Phase 0b separately pins the bytes of
   every extracted-model file under `gen/`, with membership derived from the
   filesystem so a new model file fails closed.

   **The residue you must still supply yourself.** Three things, stated
   plainly because a reader would otherwise assume them:

   · *A digest binds identity, not meaning.* The audit proves the statements
     are the ones that were reviewed. Whether those statements say something
     worth believing about ed25519 is a question only a human reading them
     answers. `AUDIT-MANIFEST.txt` is committed precisely so that reading is
     possible without re-running anything.

   · *An author can rotate the pins.* Editing a statement and refreshing the
     digest in the same commit passes every phase. The defence is that both
     changes are visible in the diff, reviewed at the pinned commit — not that
     the script prevents it. No harness audits its own author.

   · *Phase 0b pins the model; it does not verify the translation.* That the
     bytes under `gen/` are the reviewed bytes says nothing about whether
     Charon and Aeneas translated the Rust faithfully. That assumption is
     item 3 above and is unchanged.

9. **The harness is pinned, and what that is worth.** `check.sh` Phase 0c
   requires every executable file under `verification/` — plus the audit
   driver, the committed manifests and the policy tables, which are not
   executable and are therefore listed explicitly in the script — to match
   `HARNESS.sha256`. Membership is derived from the executable bit, so a new
   script fails the build until someone pins it deliberately, and the required
   set is computed from the filesystem rather than read out of the pin file,
   so deleting an entry is a failure rather than a silent un-pinning.
   `lean-guard` is inside that set: stubbing the memory-capped compiler
   wrapper is the cheapest known route to a false green, demonstrated
   elsewhere in this estate as ALL GREEN in 3.6 seconds over deliberately
   destroyed proofs. `selftest-harness.sh` replays that attack and four
   others.

   **What it does NOT buy, stated plainly.** Pinning a harness from inside
   that harness is circular, and no amount of engineering removes the
   circularity. An author who edits `check.sh` — or `lean-guard`, or the
   audit driver — and refreshes its pin in the SAME commit passes every
   phase. What the pin changes is that the edit can no longer be silent: it
   must appear in the diff, at the commit you are reviewing. That is why the
   consumer's protection is, and has always been, *review at the pinned
   commit* rather than the button's own verdict. A green button says "this is
   the apparatus that was reviewed", never "this apparatus is trustworthy".

10. **The whole declaration surface is pinned, not just the certificates.**
   `check.sh` Phase 2c reads the compiled environment and records, for EVERY
   constant originating in an audited module — roughly three thousand of them,
   compiler-generated auxiliaries included — its originating module, fully
   qualified name, declaration kind and complete axiom cone. The observed set
   must equal `inventory-allowlist.txt` exactly, in BOTH directions: a
   declaration present but not allowlisted (`UNCLASSIFIED`) and an allowlist
   entry with no declaration (`STALE`) are both build failures, and a count
   trailer disagreeing with the lines received is a third.

   The gap this closes: Phase 2b asks the kernel only whether an AXIOM is
   declared, and Phase 3 pins the cones of the named certificates. Between
   them sat every helper lemma in the corpus. One of those quietly acquiring
   a hash oracle in its cone moved nothing either phase looked at.

   **Two limits, stated because a reader would otherwise assume neither.**

   · *No independent cone walker here.* The companion accumulator runs a
     hand-written closure walker alongside the kernel's `collectAxioms` and
     requires the two to agree on every constant, so each checks the other.
     Ported to this corpus on 2026-07-29 that walker was wrong in BOTH
     directions on mathlib's inductive shapes — it reported no axioms for
     `CurveFieldProofs.EdPoint` where the kernel reported three, and after
     being extended it reported three for `CurveFieldProofs.ProjPoint` where
     the kernel reported none. Two implementations disagreeing both ways are
     not a cross-check; they are a second wrong answer. The cone figures here
     therefore rest on `collectAxioms` alone. The accumulator keeps its
     cross-check, its corpus being mathlib-free.

   · *The scalar layer is outside this phase.* Thirteen `Proofs/Scalar*`
     modules belong to `check-scalar.sh` and are inventoried by nothing. That
     is the two-button seam, still open. Phase 2c prints every uncovered
     module by name on every run, so the omission is visible rather than
     inferred.

11. **Both buttons, and the seam between them.** This repository is checked by
   two scripts: `check.sh` covers the field, curve and signature layers,
   `check-scalar.sh` the scalar layer. Until 2026-07-30 neither asserted
   anything about the other's scope and the main one simply SKIPPED anything
   named `Scalar*`, so a new `Proofs/ScalarX.lean` was gated by nothing at all
   — absent from one manifest by exemption, from the other by omission,
   compiled by neither, inventoried by neither. Each button now reads the
   other's manifest and requires every shipped proof source to belong to
   EXACTLY ONE of them, both directions: neither orphaned nor double-claimed.

   The scalar button was also brought to the main one's standard, having been
   left behind by every hardening round: it now checks source integrity,
   verifies the harness pins (so running it alone is protected too), asks the
   KERNEL about axiom declarations instead of grepping source text, inventories
   its ~1,880 declarations against its own allowlist, and asserts each of its
   13 certificates by name rather than counting how many lines of output
   matched. A count cannot say WHICH certificate is clean, and passes just as
   happily if one cone is reported twice.

   **What this cost, recorded because the lesson generalises.** Three separate
   gates in this work reasoned about how a thing is SPELLED rather than what it
   BELONGS TO, and the corpus punished each one: `Proofs/ScalarPackSpec.lean`
   is named like the scalar layer and owned by the main button. A dead-file
   gate globbing `Scalar*` demanded it be scalar-owned; an axiom gate scanning
   `Scalar*.olean` swept in an artifact this button does not compile, which on
   a fresh tree is absent and would have failed the run for a false reason; and
   the inventory driver discovery globbing `Inventory*.lean` claimed the other
   button's driver. All three now test membership in a manifest. This is the
   same family as the source-text axiom grep that began this campaign:
   reasoning about names instead of about the thing itself.
