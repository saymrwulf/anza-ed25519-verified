/- ──────────────────────────────────────────────────────────────────────────────
   Proofs/ConstSpecs.lean — the precomputed field constants denote what they claim

   WHAT THIS FILE CONTAINS
   Specs for the transpiled field constants:
   `ZERO`, `ONE`, `MINUS_ONE` (FieldElement51) and `SQRT_M1` (constants).
   Each constant evaluates totally (no panic), satisfies the limb-bound
   invariant `Bnd`, and denotes the expected element of 𝔽_p.

   RUST ANALOG
   - `FieldElement51::ZERO  = from_limbs([0,0,0,0,0])`,
     curve25519/solana-ed25519/src/backend/serial/u64/field.rs:263
   - `FieldElement51::ONE   = from_limbs([1,0,0,0,0])`, field.rs:265
   - `FieldElement51::MINUS_ONE = from_limbs([2251799813685228, 2251799813685247, ...])`,
     field.rs:267-273
   - `constants::SQRT_M1 = from_limbs([1718705420411056, ...])`,
     curve25519/solana-ed25519/src/backend/serial/u64/constants.rs:99-105
     ("Precomputed value of one of the square roots of -1 (mod p)").
   Transpiled in gen/CurveField/Funs.lean as `...FieldElement51.{ZERO,ONE,MINUS_ONE}`
   and `backend.serial.u64.constants.SQRT_M1` (each a `Result Fe` — in the Aeneas
   model a Rust `const` is a 0-argument fallible computation that we must prove `ok`).

   THE MATH (what each limb vector denotes; recall the radix-2⁵¹ denotation
   feVal a = a0 + a1·2⁵¹ + a2·2¹⁰² + a3·2¹⁵³ + a4·2²⁰⁴, ⟪a⟫ = feVal a mod p)
   - ZERO:      feVal = 0,                           ⟪·⟫ = 0.
   - ONE:       feVal = 1,                           ⟪·⟫ = 1.
   - MINUS_ONE: limbs are [2⁵¹−20, 2⁵¹−1, 2⁵¹−1, 2⁵¹−1, 2⁵¹−1], the radix-2⁵¹
     spelling of p − 1 = 2²⁵⁵ − 20; so feVal = p − 1 and ⟪·⟫ = −1.
   - SQRT_M1:   feVal = N := 19681161376707505956807079304988542015446066515923890162744021073123829784752,
     a 255-bit number with N² ≡ −1 (mod p); checked by computing the ~510-bit
     square N² and reducing mod p with kernel-verified literal arithmetic
     (norm_num) — no decision procedure or native code is trusted for this.

   ROLE IN THE MAIN THEOREM
   `fieldImplementation` (Proofs/FieldMain.lean) needs distinguished elements 0 and 1
   realized by the implementation: FieldMain obtains them from `zero_spec`/`one_spec`
   (see its `spec_exists zero_spec` / `spec_exists one_spec`) and derives
   impl_zero_add, impl_one_mul, impl_zero_ne_one. `minus_one_spec` and `sqrt_m1_spec`
   validate the remaining precomputed constants of the extracted module — `SQRT_M1`
   is the constant on which Ed25519 point decompression (`sqrt_ratio_i`) relies, so
   a wrong table entry here would be a real-world key-validation bug; the spec proves
   the table entry correct.

   FILE RELATIONS
   Imports Proofs/Denote.lean (denotation + Bnd; no other spec files needed since
   constants run no arithmetic beyond `from_limbs`). Imported by Proofs/Field.lean,
   hence by FieldMain.lean.
   ────────────────────────────────────────────────────────────────────────────── -/
import Proofs.Denote
open Aeneas Aeneas.Std Result
open curve25519

namespace CurveFieldProofs

/-! ## Casting `P - 1` into 𝔽_p gives `-1` -/

/-- No Rust analog — arithmetic helper.

    MATH:  ((p - 1 : N) : F_p) = -1   (since p ≡ 0 in F_p, p − 1 ≡ −1).
    The proof moves the ℕ-subtraction through the cast (legal because 1 ≤ p),
    rewrites (p : F_p) = 0, and finishes by ring.

    WHY NEEDED: both MINUS_ONE and SQRT_M1 reduce to a feVal equal to p − 1
    (directly, resp. after squaring mod p); this lemma converts that ℕ value into
    the field element −1 in their specs. -/
theorem natCast_P_sub_one : ((P - 1 : ℕ) : Fp) = -1 := by
  -- 1 ≤ p lets Nat.cast_sub distribute the truncated subtraction
  have h1 : (1 : ℕ) ≤ P := by norm_num [P]
  rw [Nat.cast_sub h1, ZMod.natCast_self]
  push_cast
  ring

/-! ## ZERO -/

/-- Rust: `FieldElement51::ZERO`,
    curve25519/solana-ed25519/src/backend/serial/u64/field.rs:263.

    MATH:  ZERO = ok z  with limbs [0,0,0,0,0],  Bnd(z, 2^51),  [[z]] = 0 in F_p.
    (The limb list is exposed verbatim because downstream proofs also need the
    syntactic limbs, e.g. to feed `add_spec`.)

    WHY NEEDED: provides the implementation's additive identity for
    `fieldImplementation` (FieldMain's impl_zero_add / impl_zero_ne_one start from
    `spec_exists zero_spec`). `Bnd z (2^51)` certifies that the constant satisfies
    the strictest limb invariant, so it can be fed to any operation. -/
theorem zero_spec :
    fe_zero ⦃ z =>
      (↑z : List U64) = [0#u64, 0#u64, 0#u64, 0#u64, 0#u64] ∧
      Bnd z (2^51) ∧ denote z = 0 ⦄ := by
  unfold fe_zero backend.serial.u64.field.FieldElement51.ZERO
    backend.serial.u64.field.FieldElement51.from_limbs
  -- everything is a literal: simp evaluates Array.repeat to [0,...,0], Bnd to
  -- 0 < 2⁵¹, and feVal to 0
  simp [Bnd, denote, feVal, limbsVal, Array.repeat, List.replicate]

/-! ## ONE -/

/-- Rust: `FieldElement51::ONE`,
    curve25519/solana-ed25519/src/backend/serial/u64/field.rs:265.

    MATH:  ONE = ok o  with limbs [1,0,0,0,0],  Bnd(o, 2^51),  [[o]] = 1 in F_p
    (feVal = 1 + 0·2⁵¹ + ... = 1).

    WHY NEEDED: the implementation's multiplicative identity; FieldMain's
    impl_one_mul and impl_zero_ne_one consume it via `spec_exists one_spec`. -/
theorem one_spec : fe_one ⦃ o => Bnd o (2^51) ∧ denote o = 1 ⦄ := by
  unfold fe_one backend.serial.u64.field.FieldElement51.ONE
    backend.serial.u64.field.FieldElement51.from_limbs
  -- literal evaluation: feVal [1,0,0,0,0] = 1, and 1 < 2⁵¹
  simp [Bnd, denote, feVal, limbsVal, Array.make]

/-! ## MINUS_ONE -/

/-- Rust: `FieldElement51::MINUS_ONE`,
    curve25519/solana-ed25519/src/backend/serial/u64/field.rs:267-273.

    MATH:  MINUS_ONE = ok m  with  Bnd(m, 2^52)  and  [[m]] = -1 in F_p.
    The limbs are
        [2251799813685228, 2251799813685247, 2251799813685247,
         2251799813685247, 2251799813685247]
      = [2^51 - 20, 2^51 - 1, 2^51 - 1, 2^51 - 1, 2^51 - 1],
    the radix-2⁵¹ "borrowed" spelling of p − 1 (cf. sixteen_p in SubNegSpec.lean):
        (2^51-20) + (2^51-1)·(2^51 + 2^102 + 2^153 + 2^204) = 2^255 - 20 = p - 1,
    so feVal m = p − 1 and ⟪m⟫ = −1 by `natCast_P_sub_one`.
    (Each limb is < 2⁵¹; the bound is stated as the looser 2⁵² used uniformly for
    reduced values in this development.)

    WHY NEEDED: validates the third hard-coded table constant of the extracted
    module: a typo in any of those 16-digit limbs would silently negate nothing.
    It also documents that −1 has a canonical bounded representative, the element
    `negate`/`sub` effectively build from. -/
theorem minus_one_spec : fe_minus_one ⦃ m => Bnd m (2^52) ∧ denote m = -1 ⦄ := by
  unfold fe_minus_one backend.serial.u64.field.FieldElement51.MINUS_ONE
    backend.serial.u64.field.FieldElement51.from_limbs
  -- simp discharges the Bnd conjunct and evaluates `feVal` to the literal
  -- 2²⁵⁵ − 20 = P − 1; the remaining goal is `(P − 1 : 𝔽_p) = -1`.
  simp [Bnd, denote, feVal, limbsVal, Array.make]
  -- specialize natCast_P_sub_one to the literal that simp produced for P − 1
  have h := natCast_P_sub_one
  have hc : (P - 1 : ℕ) =
      57896044618658097711785492504343953926634992332820282019728792003956564819948 := by
    norm_num [P]
  rw [hc] at h
  exact_mod_cast h

/-! ## SQRT_M1 -/

/-- Rust: `constants::SQRT_M1`,
    curve25519/solana-ed25519/src/backend/serial/u64/constants.rs:99-105 —
    "Precomputed value of one of the square roots of -1 (mod p)" (it exists since
    p ≡ 1 mod 4).

    MATH:  SQRT_M1 = ok s  with  Bnd(s, 2^52)  and  [[s]] * [[s]] = -1 in F_p.
    The limbs [1718705420411056, 234908883556509, 2233514472574048,
    2117202627021982, 765476049583133] denote the 255-bit number
        N = 19681161376707505956807079304988542015446066515923890162744021073123829784752
    and the spec certifies N² ≡ −1 (mod p). The verification is brute literal
    arithmetic: `norm_num` makes the kernel compute the ~510-bit square N² and its
    remainder mod p, equal to p − 1 (lemma `hmod` below), then `natCast_P_sub_one`
    converts p − 1 to −1. (Each limb is < 2⁵¹; stated at the uniform 2⁵² bound.)

    WHY NEEDED: `sqrt_ratio_i` — the square-root routine behind Ed25519 point
    decompression — multiplies by this table constant whenever the candidate root
    fails its sign/QR check; a corrupted constant would make decompression accept or
    produce wrong points. This spec pins the precomputed table entry to its defining
    equation, complementing the operation-level proofs that feed FieldMain. -/
theorem sqrt_m1_spec :
    backend.serial.u64.constants.SQRT_M1 ⦃ s => Bnd s (2^52) ∧ denote s * denote s = -1 ⦄ := by
  unfold backend.serial.u64.constants.SQRT_M1
    backend.serial.u64.field.FieldElement51.from_limbs
  -- simp discharges the Bnd conjunct and evaluates `feVal` to the literal N
  -- (the 255-bit value of the SQRT_M1 limbs); the remaining goal is
  -- `(N : 𝔽_p) * (N : 𝔽_p) = -1`.
  simp [Bnd, denote, feVal, limbsVal, Array.make]
  -- N² ≡ P − 1 (mod P), checked by literal arithmetic on ℕ.
  -- (norm_num evaluates the 510-bit product and the division by P inside the kernel)
  have hmod :
      ((19681161376707505956807079304988542015446066515923890162744021073123829784752 *
        19681161376707505956807079304988542015446066515923890162744021073123829784752 : ℕ))
        % P = P - 1 := by
    norm_num [P]
  -- assemble: (N:Fp)·(N:Fp) = (N·N : Fp) = ((N·N mod P) : Fp) = ((P−1) : Fp) = −1
  have key :
      ((19681161376707505956807079304988542015446066515923890162744021073123829784752 : ℕ) : Fp) *
      ((19681161376707505956807079304988542015446066515923890162744021073123829784752 : ℕ) : Fp)
        = -1 := by
    rw [← Nat.cast_mul, ← ZMod.natCast_mod, hmod, natCast_P_sub_one]
  exact_mod_cast key

end CurveFieldProofs
