/- ───────────────────────────────────────────────────────────────────────────
   Proofs/Field.lean — Field packaging, part 1 of 2 (part 2 = multiplicative
   inverses, which land in InvertSpec.lean and FieldMain.lean).

   CONTEXT. The Rust crate curve25519/solana-ed25519 implements arithmetic in
   F_p, p = 2^255 - 19, on 5 radix-2^51 u64 limbs (`FieldElement51`, in
   curve25519/solana-ed25519/src/backend/serial/u64/field.rs, driven by
   src/field.rs). That code was transpiled mechanically (Charon + Aeneas) to
   gen/CurveField/{Types,Funs}.lean. The denotation ⟪a⟫ ∈ F_p of a limb
   vector a and the limb-bound invariant `Bnd` live in Proofs/Denote.lean.

   THIS FILE supplies the purely mathematical scaffolding that the main
   theorem (Proofs/FieldMain.lean: `fieldImplementation`) needs around the
   per-operation specs:

   * 𝔽_p IS a field: p = 2²⁵⁵ − 19 is prime (Proofs/P25519.lean, axiom-free),
     so mathlib's `ZMod.instField` applies.  Registering `Fact (Nat.Prime P)`
     is what unlocks that instance (`P_prime`, the two instances below).
   * The denotation ⟪·⟫ : Fe → 𝔽_p is SURJECTIVE on bounded elements (via the
     canonical `encode`, which writes y < p in base 2⁵¹), so the transpiled
     type covers all of 𝔽_p — without this, "implements the field" would be
     vacuous on unreachable elements (`encode` … `denote_surjective`).
   * The transpiled ops realize the field ops of 𝔽_p through ⟪·⟫ (proved in
     the *Spec.lean files this file imports; re-packaged in FieldMain.lean).
   * `spec_exists` converts total-correctness triples `x ⦃ post ⦄` into plain
     existentials `∃ r, x = ok r ∧ post r`, the form used by FieldMain.lean.

   There is NO Rust analog for this file: it is meta-level mathematics about
   the transpiled code, not transpiled code itself.

   Imports: ConstSpecs/AddSpec/SubNegSpec/MulSpec (the operation specs) and
   P25519 (primality).  Imported by: InvertSpec.lean (needs the `Field Fp`
   instance for `⁻¹` and Fermat) and, through it, FieldMain.lean.
   ─────────────────────────────────────────────────────────────────────── -/
import Proofs.ConstSpecs
import Proofs.AddSpec
import Proofs.SubNegSpec
import Proofs.MulSpec
import Proofs.P25519
open Aeneas Aeneas.Std Result
open curve25519

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace CurveFieldProofs

/-! ## 𝔽_p is a field -/

/- MATH:  Nat.Prime P  where  P = 2^255 - 19  (the numeral defined in
   Proofs/Denote.lean).  This is `p25519_prime` from Proofs/P25519.lean — a
   fully kernel-checked Pratt/Lucas primality certificate, no `native_decide`,
   no axioms — restated with the literal `2^255 - 19` rewritten to `P` so it
   matches the form mathlib's instance machinery will look for.
   WHY NEEDED: primality of the modulus is THE reason `ZMod P` is a field
   (inverses exist); everything in InvertSpec/FieldMain rests on it. -/
theorem P_prime : Nat.Prime P := by
  have h := p25519_prime                       -- the certificate, for 2^255 - 19
  have : (2:ℕ)^255 - 19 = P := by norm_num [P] -- the numeral really is P
  rwa [this] at h                              -- transport the certificate to P

/- Register the primality as a typeclass `Fact`, the hook mathlib uses to
   activate `Field (ZMod P)` (instance `ZMod.instField`).  Without this
   instance, `Fp` would only be a commutative ring and `⟪a⟫⁻¹` would not be
   available.  WHY NEEDED: unlocks `Field Fp` for every later proof. -/
instance : Fact (Nat.Prime P) := ⟨P_prime⟩

/- MATH: P ≠ 0.  A small side instance some mathlib lemmas about `ZMod.val`
   require (e.g. `ZMod.val_lt` used in `val_lt_P` below). -/
instance : NeZero P := ⟨by norm_num [P]⟩

/-- 𝔽_p = ZMod p with p prime is a field (mathlib instance).
    This `example` is a compile-time sanity check that the two instances
    above really do trigger mathlib's `ZMod.instField`; it generates no
    code and is never referenced (FieldMain.lean re-exposes the instance
    as the abbrev `Fp_field`). -/
noncomputable example : Field Fp := inferInstance

/-! ## Surjectivity of the denotation

The representation is REDUNDANT: many limb vectors denote the same field
element, and arbitrary `Fe`s (limbs up to 2⁶⁴) may not even satisfy the
operations' preconditions. To state "the code implements all of 𝔽_p" we must
therefore exhibit, for every y ∈ 𝔽_p, at least one WELL-BOUNDED limb vector
denoting y. `encode` constructs the canonical one: the base-2⁵¹ digits of
the unique representative y.val ∈ [0, p). -/

/-- Build a `U64` from a natural number (mod 2⁶⁴).
    Aeneas's `U64` wraps a 64-bit `BitVec`; `.val : Nat` is its mathematical
    value. Rust analog: a `u64` literal / `as u64` cast.
    WHY NEEDED: `encode` must manufacture concrete machine limbs. -/
def mkU64 (n : ℕ) : U64 := ⟨BitVec.ofNat 64 n⟩

/- MATH:  forall n < 2^64,  (mkU64 n).val = n  — the round-trip is exact as
   long as the input fits in 64 bits (BitVec.ofNat reduces mod 2^64, and the
   hypothesis makes the reduction a no-op).
   WHY NEEDED: lets `encode_bnd`/`denote_encode` compute with the limb values
   of `encode y` as plain naturals. -/
theorem mkU64_val (n : ℕ) (h : n < 2^64) : (mkU64 n).val = n := by
  show (BitVec.ofNat 64 n).toNat = n
  simp only [BitVec.toNat_ofNat]  -- .val of ofNat is n % 2^64
  omega                            -- n < 2^64 kills the mod

/-- Canonical (reduced, base-2⁵¹) representative of a field element:
    limb i = the i-th base-2⁵¹ digit of y.val (the canonical natural < p).

    MATH:  encode y = [ y mod 2^51, (y / 2^51) mod 2^51, (y / 2^102) mod 2^51,
                        (y / 2^153) mod 2^51,  y / 2^204 ]
    so   limbsVal (encode y) = y.val   exactly (no mod p reduction needed,
    since y.val < p < 2^255).  The top limb needs no mask: y.val / 2^204 <
    2^51 because y.val < p < 2^255.

    Rust analog (conceptually): `FieldElement51::from_bytes` of the little-
    endian encoding of y — here built directly as digits, which is simpler
    to reason about.  `Array.make 5#usize [...]` mirrors the transpiled
    representation `FieldElement51 = Array U64 5` (a Rust `[u64; 5]`).
    WHY NEEDED: the witness for `denote_surjective`. -/
def encode (y : Fp) : Fe :=
  Array.make 5#usize
    [ mkU64 (y.val % 2^51),
      mkU64 (y.val / 2^51 % 2^51),
      mkU64 (y.val / 2^102 % 2^51),
      mkU64 (y.val / 2^153 % 2^51),
      mkU64 (y.val / 2^204) ]

/- MATH: the underlying limb list of `encode y` is literally the 5-digit
   list above (`rfl`: true by unfolding the definitions).
   WHY NEEDED: `Bnd`/`feVal` are stated via the limb LIST (`Bnd_eq`,
   `feVal_eq` in Proofs/Denote.lean), so the next two proofs need the list
   in explicit form. -/
theorem encode_list (y : Fp) :
    (↑(encode y) : List U64)
      = [ mkU64 (y.val % 2^51), mkU64 (y.val / 2^51 % 2^51),
          mkU64 (y.val / 2^102 % 2^51), mkU64 (y.val / 2^153 % 2^51),
          mkU64 (y.val / 2^204) ] := rfl

/- MATH:  forall y in F_p,  y.val < P  — the canonical representative is
   reduced.  Pure mathlib (`ZMod.val_lt`, needs `NeZero P` above); restated
   here for convenient repeated use.
   WHY NEEDED: gives the size bound that makes all of `encode`'s digits and
   their recombination fit (P < 2^255 = (2^51)^5). -/
theorem val_lt_P (y : Fp) : y.val < P := ZMod.val_lt y

/- MATH:  forall y in F_p,  Bnd (encode y) (2^51)  — every limb of the
   canonical representative is < 2^51 (it is a base-2^51 digit; the top limb
   because y.val < P < 2^255).  This is even stronger than the 2^52 "valid
   output" bound used downstream.
   WHY NEEDED: surjectivity must produce BOUNDED witnesses, otherwise the
   operations' preconditions could never be met on them. -/
theorem encode_bnd (y : Fp) : Bnd (encode y) (2^51) := by
  have h := val_lt_P y
  have hP : P < 2^255 := by norm_num [P]
  -- switch from the opaque `Fe` to the explicit 5-element limb list
  rw [Bnd_eq _ _ _ _ _ _ _ (encode_list y)]
  -- 5 goals, one per limb: each digit is < 2^51 by omega
  -- (mod-2^51 digits trivially; the top limb via y.val < P < 2^255)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [mkU64_val _ (by omega)]; omega)

/- MATH:  forall y in F_p,  ⟪encode y⟫ = y  — decode ∘ encode = id.
   LaTeX:  $\forall y,\ \llbracket \mathrm{encode}\,y \rrbracket = y$.
   Proof: the base-2^51 digits recombine to exactly y.val (omega), and
   casting y.val back into ZMod P is the identity.
   WHY NEEDED: the second half of the surjectivity witness. -/
theorem denote_encode (y : Fp) : ⟪encode y⟫ = y := by
  have h := val_lt_P y
  have hP : P < 2^255 := by norm_num [P]
  -- step 1: the natural-number value of the limbs is exactly y.val
  have hval : feVal (encode y) = y.val := by
    rw [feVal_eq _ _ _ _ _ _ (encode_list y)]
    simp only [limbsVal]
    -- each digit fits in u64, so mkU64 is value-preserving on it
    rw [mkU64_val _ (by omega), mkU64_val _ (by omega), mkU64_val _ (by omega),
        mkU64_val _ (by omega), mkU64_val _ (by omega)]
    -- digit recombination: d0 + d1·2^51 + d2·2^102 + d3·2^153 + d4·2^204 = y.val
    omega
  -- step 2: (y.val : ZMod P) = y  (cast of the canonical representative)
  simp [denote, hval, ZMod.natCast_val, ZMod.cast_id]

/-- Every element of 𝔽_p is the denotation of a (well-bounded) `Fe`.

    MATH:  forall y : F_p,  exists a : Fe,  Bnd(a, 2^52)  and  ⟪a⟫ = y.
    LaTeX: $\forall y \in \mathbb{F}_p\ \exists a,\
            \mathrm{Bnd}(a,2^{52}) \wedge \llbracket a\rrbracket = y$.
    The witness is `encode y` (bounded by 2⁵¹, weakened to the standard
    "valid element" bound 2⁵² via `Bnd.mono`).
    WHY NEEDED: this is the `surj` field of `IsFieldImplementation`
    (FieldMain.lean) — it makes "implements 𝔽_p" mean ALL of 𝔽_p. -/
theorem denote_surjective : ∀ y : Fp, ∃ a : Fe, Bnd a (2^52) ∧ ⟪a⟫ = y :=
  fun y => ⟨encode y, (encode_bnd y).mono (by norm_num), denote_encode y⟩

/-! ## The triple → existential bridge (library: `Std.WP.spec_imp_exists`) -/

/- MATH:  if  x ⦃ post ⦄  (total correctness: x does not panic AND its result
   satisfies post), then  exists r, x = ok r and post r.
   This merely re-exports the Aeneas library lemma `Std.WP.spec_imp_exists`
   with the triple written in this project's notation.
   WHY NEEDED: the `run_*` theorems and `IsFieldImplementation` fields in
   FieldMain.lean are phrased as plain existentials over `= ok r` (readable
   without knowing the WP calculus); this is the converter. -/
theorem spec_exists {α} {x : Result α} {p : α → Prop}
    (h : x ⦃ r => p r ⦄) : ∃ r, x = ok r ∧ p r :=
  Std.WP.spec_imp_exists h

end CurveFieldProofs
