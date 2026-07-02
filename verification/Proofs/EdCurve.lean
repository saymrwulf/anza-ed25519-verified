/-
═══════════════════════════════════════════════════════════════════════════════
Proofs/EdCurve.lean — pure mathematics of the curve25519 twisted Edwards curve
                      (curve constant d, completeness of the addition law,
                      and the basic point-arithmetic laws over 𝔽_p)
═══════════════════════════════════════════════════════════════════════════════

WHAT THIS FILE PROVES (all in 𝔽_p, p = 2²⁵⁵ − 19, over `Fp := ZMod P` from
Proofs/Field.lean — no transpiled code appears here):

  * `edD`             — the Ed25519 curve constant d = −121665/121666 ∈ 𝔽_p,
                        with its decode-friendly characterization `edD_char`.
  * `OnCurve x y`     — the twisted Edwards curve equation with a = −1:
                        −x² + y² = 1 + d·x²·y²  (the Ed25519 curve −x²+y² =
                        1 + d x² y², RFC 8032 §5.1).
  * `edAdd/edNeg/edId`— the complete twisted Edwards addition law, negation
                        and neutral element on coordinate pairs.
  * `edD_not_square`  — d is a quadratic NON-residue mod p.  This is the
                        number-theoretic heart of the file: by Euler's
                        criterion it reduces to the 255-bit exponentiation
                        d^((p−1)/2) ≡ −1 (mod p), which the Lean KERNEL
                        checks via a fuel-based `powMod` (the technique of
                        Proofs/P25519.lean — no `native_decide`, no axioms).
  * `completeness`    — THE Bernstein–Lange completeness theorem (BBJLP,
                        "Twisted Edwards curves" / Bernstein–Lange "Faster
                        addition and doubling on elliptic curves", Thm 3.3):
                        because d is not a square (and −1 IS a square), the
                        denominators 1 ± d·x₁x₂y₁y₂ of the addition law NEVER
                        vanish on curve points.  Hence `edAdd` is total: no
                        case distinctions, no exceptional pairs — the property
                        that makes Edwards form attractive for constant-time
                        cryptography in the first place.
  * `onCurve_id`, `onCurve_neg`, `edAdd_id`, `edAdd_comm`, `edAdd_neg`,
    `edAdd_closure` — the mechanical group-operation laws: (0,1) is neutral,
                        negation stays on the curve, p + (−p) = identity,
                        addition is commutative and CLOSED on the curve.
                        (Associativity is deliberately out of scope — Tier 2.)

RUST ANALOG (indirect — this file is meta-level mathematics):
  curve25519/solana-ed25519/src/backend/serial/u64/constants.rs defines
  `EDWARDS_D` (the limb encoding of d = −121665/121666) and `SQRT_M1`;
  src/edwards.rs implements point addition in extended coordinates whose
  projective denominators are exactly the 1 ± d·x₁x₂y₁y₂ treated here.  The
  Rust code never checks for exceptional cases — `completeness` is the
  mathematical fact that justifies this.

PLACE IN THE IMPORT GRAPH
  Imports Proofs.Field (for `P`, `Fp := ZMod P`, the `Fact (Nat.Prime P)` and
  `NeZero P` instances) plus mathlib (Euler's criterion).  Nothing imports it
  yet: it is the Tier-1 pure-mathematics layer for the upcoming verification
  of the transpiled twisted Edwards point arithmetic.

PROOF TECHNIQUE, FOR THE LAY READER
  1. Big-number facts (d^((p−1)/2) = −1, sqrt(−1)² = −1, the canonical
     residue of d) are stated as closed equations between `Nat` literals and
     checked by the KERNEL with `decide`, through the same fuel-based
     square-and-multiply `powMod` used by Proofs/P25519.lean.  GMP-backed
     kernel `Nat` arithmetic makes each check milliseconds.
  2. Algebraic identities on the curve are proved with `linear_combination`:
     every identity is exhibited as an EXPLICIT polynomial combination of the
     two curve equations (the cofactor polynomials below were computed and
     verified offline with an exact Gröbner-basis computation; the Lean
     `ring` normalizer re-verifies them from scratch, so they are trusted
     only as HINTS, not as facts).
  3. The completeness argument follows Bernstein–Lange: if a denominator
     1 ± d·x₁x₂y₁y₂ vanished, d = (…/…)² would be a square — contradiction
     with `edD_not_square`.  The a = −1 twist is handled directly using
     i = √−1 ∈ 𝔽_p (p ≡ 1 mod 4): the role (x₁ ± y₁)² plays for a = 1 is
     played by (i·x₁ ± ε·y₁)² here.
-/
import Proofs.Field
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

-- Big decimal literals (255-bit numbers) build deep numeral terms during
-- elaboration; same limits as Proofs/P25519.lean and Proofs/Field.lean.
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace CurveFieldProofs

/-! ## Kernel-checkable modular exponentiation

The technique of Proofs/P25519.lean, recreated here so this file depends only
on the MATHEMATICAL interface of Proofs/Field.lean (`P`, `Fp`, the instances)
and not on the primality certificate's internal helpers: a fuel-based
square-and-multiply on raw `Nat`, with a once-proved correctness lemma.  Each
255-bit exponentiation below then becomes a single closed `Nat` equation that
the kernel `decide`s with GMP big-integer arithmetic in milliseconds — no
`native_decide`, no axioms. -/

/-- Fuel-based binary modular exponentiation, kernel-reducible.

MATH (for sufficient fuel; made precise by `powModAux_eq`):
  `powModAux fuel a k n = a^k mod n`.
Algorithm: square-and-multiply along the binary digits of `k`, every
intermediate reduced mod n (so nothing exceeds n² ≈ 510 bits here).

WHY THE `fuel` ARGUMENT: structural recursion on `fuel` is what the kernel
can unfold step by step during `decide`; recursion on `k/2 < k` would compile
to `WellFounded.fix`, which the kernel cannot evaluate. -/
def powModAux : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, n => 1 % n
  | fuel + 1, a, k, n =>
    if k = 0 then 1 % n
    else if k % 2 = 1 then powModAux fuel (a * a % n) (k / 2) n * a % n
    else powModAux fuel (a * a % n) (k / 2) n

/- Correctness of `powModAux`.

   MATH (ASCII):  forall fuel a k n,  k < 2^fuel  ==>
                  powModAux fuel a k n = a^k mod n
   The hypothesis `k < 2^fuel` says the fuel covers every binary digit of the
   exponent, so the recursion never runs dry.
   WHY NEEDED: turns each kernel computation `powMod a k n = …` into the
   mathematical statement `a^k % n = …` consumed by the bridge lemmas below.
   Proof: induction on `fuel`, mirroring the recursion of `powModAux`. -/
theorem powModAux_eq : ∀ (fuel a k n : ℕ), k < 2 ^ fuel → powModAux fuel a k n = a ^ k % n := by
  intro fuel
  induction fuel with
  | zero =>
    -- base case: k < 2^0 = 1 forces k = 0, and both sides reduce to 1 % n
    intro a k n hk
    rw [pow_zero] at hk
    have hk0 : k = 0 := by omega
    subst hk0
    simp [powModAux]
  | succ f ih =>
    intro a k n hk
    by_cases hk0 : k = 0
    -- k = 0: both sides are 1 % n by definition
    · subst hk0; simp [powModAux]
    -- k ≠ 0: the recursive call gets exponent k/2, which fits in f bits…
    · have hk2 : k / 2 < 2 ^ f := by
        rw [pow_succ] at hk
        omega
      -- …so the induction hypothesis describes it: (a²%n)^(k/2) % n
      have hrec := ih (a * a % n) (k / 2) n hk2
      have haa : a * a = a ^ 2 := (pow_two a).symm
      simp only [powModAux, if_neg hk0]
      -- split on the lowest bit of k and reassemble the exponent:
      by_cases hodd : k % 2 = 1
      -- odd k: (a²)^(k/2) · a = a^(2·(k/2)+1) = a^k  (mods commute via Nat.pow_mod)
      · rw [if_pos hodd, hrec, ← Nat.pow_mod, Nat.mod_mul_mod, haa, ← pow_mul, ← pow_succ,
          show 2 * (k / 2) + 1 = k by omega]
      -- even k: (a²)^(k/2) = a^(2·(k/2)) = a^k
      · rw [if_neg hodd, hrec, ← Nat.pow_mod, haa, ← pow_mul,
          show 2 * (k / 2) = k by omega]

/-- `powMod a k n = a ^ k % n` for all `k < 2 ^ 256` — fuel fixed at 256,
    enough for every exponent below 2²⁵⁶, in particular for `P / 2` (< 2²⁵⁴).
    WHY NEEDED: the single entry point of all kernel computations below. -/
def powMod (a k n : ℕ) : ℕ := powModAux 256 a k n

/- Bridge from the `Nat` computation into `ZMod n`.

   MATH:  k < 2^256  ==>  (a : ZMod n)^k = (powMod a k n : ZMod n).
   Casting `a` into Z/n and exponentiating there agrees with computing
   `a^k mod n` over the naturals and casting the result (the cast is a ring
   homomorphism that kills `% n`).
   WHY NEEDED: this is how the kernel-checked equation
   `powMod dNum (P/2) P = P − 1` becomes the field equation
   `edD^(P/2) = −1` in `edD_pow_eq_neg_one`. -/
theorem cast_pow_eq (a k n : ℕ) (hk : k < 2 ^ 256) :
    (a : ZMod n) ^ k = ((powMod a k n : ℕ) : ZMod n) := by
  rw [powMod, powModAux_eq 256 a k n hk, ZMod.natCast_mod, Nat.cast_pow]

/-! ## Casting `Nat` residues into 𝔽_p

Two tiny workhorses: a natural number is 0 in 𝔽_p iff p divides it.  Every
kernel-checked congruence below enters the field through these. -/

/- MATH:  n % P = 0  ==>  (n : F_p) = 0  — multiples of p vanish in 𝔽_p.
   WHY NEEDED: imports each kernel-checked `Nat` congruence (a closed `% P`
   equation, checked by `decide`) into the field 𝔽_p. -/
theorem natCast_eq_zero_of_mod {n : ℕ} (h : n % P = 0) : (n : Fp) = 0 := by
  rw [← ZMod.natCast_mod n P, h, Nat.cast_zero]

/- MATH:  n % P ≠ 0  ==>  (n : F_p) ≠ 0  — non-multiples of p survive in 𝔽_p.
   Distinct naturals can collide in Z/p, so the cast-level inequality needs
   the residues compared mod p (`ZMod.natCast_eq_natCast_iff'`).
   WHY NEEDED: gives the nonvanishing of the small constants 2, 121665,
   121666 (each `% P` check is a kernel `decide`: P is huge, they are tiny). -/
theorem natCast_ne_zero_of_mod {n : ℕ} (h : n % P ≠ 0) : (n : Fp) ≠ 0 := by
  intro hc
  apply h
  have h0 : ((n : ℕ) : Fp) = ((0 : ℕ) : Fp) := by rw [Nat.cast_zero]; exact hc
  have h1 := (ZMod.natCast_eq_natCast_iff' n 0 P).mp h0
  rwa [Nat.zero_mod] at h1

/- MATH: (121666 : F_p) ≠ 0.  True because 0 < 121666 < P, i.e. P ∤ 121666.
   WHY NEEDED: 121666 is the denominator of d — without this, `edD` would be
   division by zero and `edD_char`/`dNum_cast` would be vacuous.
   (`private`: Proofs/EdDenote.lean exports an identical public lemma of the
   same name; importers that need both files use that one.  Privacy here
   avoids a duplicate-declaration clash without changing any statement.) -/
private theorem c121666_ne_zero : (121666 : Fp) ≠ 0 := by
  have h : ((121666 : ℕ) : Fp) ≠ 0 := natCast_ne_zero_of_mod (by decide)
  exact_mod_cast h

/- MATH: (121665 : F_p) ≠ 0 (numerator of −d).  WHY NEEDED: `edD_ne_zero`. -/
theorem c121665_ne_zero : (121665 : Fp) ≠ 0 := by
  have h : ((121665 : ℕ) : Fp) ≠ 0 := natCast_ne_zero_of_mod (by decide)
  exact_mod_cast h

/- MATH: (2 : F_p) ≠ 0 — the field has characteristic ≠ 2 (p is odd).
   WHY NEEDED: the completeness proof at one point divides the curve world
   into i·x₂ = ±y₂ and needs "both" to force x₂ = 0 via 2·i·x₂ = 0. -/
theorem two_ne_zero_Fp : (2 : Fp) ≠ 0 := by
  have h : ((2 : ℕ) : Fp) ≠ 0 := natCast_ne_zero_of_mod (by decide)
  exact_mod_cast h

/-! ## The curve constant d = −121665/121666 -/

/-- The Ed25519 twisted Edwards curve constant

    MATH: d := −121665/121666 ∈ 𝔽_p  (RFC 8032 §5.1; BBJLP "Twisted Edwards
    curves" parameters a = −1, d).
    Rust analog: `constants::EDWARDS_D` in curve25519/solana-ed25519/src/
    backend/serial/u64/constants.rs — the limb vector denoting exactly this
    field element.
    WHY NEEDED: parametrizes the curve equation `OnCurve` and the addition
    law `edAdd`; its NON-squareness (`edD_not_square`) is what makes the
    addition law complete. -/
noncomputable def edD : Fp := -(121665 : Fp) / 121666

/- MATH:  121666 · d = −121665  — the denominator-free characterization.
   This is the form a DECODER of the constant can check by pure limb
   arithmetic (multiply by 121666, compare with −121665), with no inversion.
   Proof: cancel the nonzero denominator 121666.
   WHY NEEDED: the bridge between the abstract fraction and any concrete
   representation of d — used right below to certify the canonical residue
   `dNum`, and intended as the spec hook for the transpiled `EDWARDS_D`. -/
theorem edD_char : (121666 : Fp) * edD = -121665 := by
  unfold edD
  rw [mul_comm, div_mul_cancel₀ _ c121666_ne_zero]

/- MATH: d ≠ 0 — numerator −121665 and denominator 121666 are both nonzero.
   WHY NEEDED: Euler's criterion (`ZMod.euler_criterion`) only speaks about
   nonzero elements; also gives x,y ≠ 0 extraction in the completeness proof. -/
theorem edD_ne_zero : edD ≠ 0 := by
  unfold edD
  exact div_ne_zero (neg_ne_zero.mpr c121665_ne_zero) c121666_ne_zero

/-! ## d as a canonical residue, and d^((p−1)/2) = −1

To exponentiate d with the kernel we need d as a NATURAL number.  `dNum` is
the canonical representative (computed offline as
(p − 121665)·121666⁻¹ mod p; the kernel re-certifies it below, so the
literal is trusted only as a hint). -/

/-- The unique n < P with (n : 𝔽_p) = d, as a decimal literal.

    MATH: dNum := (p − 121665) · (121666⁻¹ mod p) mod p.
    WHY NEEDED: `powMod` computes on `Nat`, not on `ZMod P`; this literal is
    the entry ticket for the kernel computation of d^((p−1)/2). -/
def dNum : ℕ := 37095705934669439343138083508754565189542113879843219016388785533085940283555

/- MATH:  (dNum : F_p) = d.
   Proof: by `edD_char`-style cancellation it suffices that
   121666·dNum + 121665 ≡ 0 (mod p) — a closed `Nat` congruence the kernel
   `decide`s (one big multiplication and one division by P).
   WHY NEEDED: transports the kernel-checked power of `dNum` to a statement
   about `edD` itself. -/
theorem dNum_cast : (dNum : Fp) = edD := by
  unfold edD
  rw [eq_div_iff c121666_ne_zero]
  -- the kernel certifies: p | dNum·121666 + 121665
  have key : ((dNum * 121666 + 121665 : ℕ) : Fp) = 0 := natCast_eq_zero_of_mod (by decide)
  push_cast at key
  linear_combination key

/- MATH:  d^((p−1)/2) = −1  in 𝔽_p  (stated with `P / 2`, which equals
   (p−1)/2 since p is odd — this is the exact exponent in mathlib's
   `ZMod.euler_criterion`).
   Proof: the kernel computes powMod dNum (P/2) P = P − 1 (≈255 squarings of
   255-bit numbers — milliseconds via GMP), and (P − 1 : 𝔽_p) = −1 because
   (P−1) + 1 = P ≡ 0.
   WHY NEEDED: with Euler's criterion this IS the non-squareness of d. -/
theorem edD_pow_eq_neg_one : edD ^ (P / 2) = -1 := by
  rw [← dNum_cast, cast_pow_eq dNum (P / 2) P (by decide),
      show powMod dNum (P / 2) P = P - 1 from by decide]
  -- (P − 1 : 𝔽_p) = −1, i.e. ↑(P−1) + 1 = 0, i.e. ↑P = 0
  have hP1 : 1 ≤ P := by norm_num [P]
  have h : ((P - 1 : ℕ) : Fp) + ((1 : ℕ) : Fp) = 0 := by
    rw [← Nat.cast_add, Nat.sub_add_cancel hP1]
    exact natCast_eq_zero_of_mod (by simp)
  rw [Nat.cast_one] at h
  linear_combination h

/- MATH: −1 ≠ 1 in 𝔽_p (characteristic ≠ 2: their difference is 2 ≠ 0).
   WHY NEEDED: turns `edD^(P/2) = −1` into `edD^(P/2) ≠ 1` for Euler. -/
theorem neg_one_ne_one_Fp : (-1 : Fp) ≠ 1 := by
  intro hc
  exact two_ne_zero_Fp (by linear_combination -hc)

/-- d is a quadratic NON-residue modulo p.

    MATH (ASCII):  ¬ exists r in F_p,  d = r·r.
    LaTeX: $\left(\frac{d}{p}\right) = -1$.
    Proof: Euler's criterion (`ZMod.euler_criterion`, d ≠ 0) reduces
    squareness to d^(p/2) = 1; but d^(p/2) = −1 ≠ 1 by the kernel
    computation above.
    WHY NEEDED: THE hypothesis of the Bernstein–Lange completeness theorem.
    A square d would admit exceptional point pairs where the addition law's
    denominators vanish; non-square d (this theorem) rules them ALL out. -/
theorem edD_not_square : ¬ IsSquare edD := by
  intro hsq
  have h := (ZMod.euler_criterion P edD_ne_zero).mp hsq
  rw [edD_pow_eq_neg_one] at h
  exact neg_one_ne_one_Fp h

/-! ## √−1 in 𝔽_p

p ≡ 1 (mod 4), so −1 is a square mod p.  A concrete square root (the same
distinguished one the Rust constant `SQRT_M1` denotes, namely
2^((p−1)/4) mod p) lets the a = −1 completeness proof run DIRECTLY on the
twisted curve: wherever the classical a = 1 proof squares (x₁ ± y₁), we
square (i·x₁ ± ε·y₁) instead. -/

/-- The canonical √−1 of 𝔽_p as a decimal literal: 2^((p−1)/4) mod p
    (computed offline; the kernel re-certifies the defining equation below).
    Rust analog: `constants::SQRT_M1`.
    WHY NEEDED: makes −1 an EXPLICIT square, which is what lets the a = −1
    twisted curve reuse the Bernstein–Lange square-exhibition argument. -/
def sNum : ℕ := 19681161376707505956807079304988542015446066515923890162744021073123829784752

/-- √−1 as a field element. -/
noncomputable def sqrtM1 : Fp := (sNum : Fp)

/- MATH:  sqrtM1² = −1.  Proof: the kernel certifies p | sNum·sNum + 1 (one
   255×255-bit multiplication), and a multiple of p vanishes in 𝔽_p.
   WHY NEEDED: the only property of `sqrtM1` the completeness proof uses. -/
theorem sqrtM1_sq : sqrtM1 ^ 2 = -1 := by
  have key : ((sNum * sNum + 1 : ℕ) : Fp) = 0 := natCast_eq_zero_of_mod (by decide)
  push_cast at key
  unfold sqrtM1
  linear_combination key

/- MATH: sqrtM1 ≠ 0 (its square is −1 ≠ 0).
   WHY NEEDED: cancellation in the `i·x₂ = ±y₂ ⇒ x₂ = 0` step. -/
theorem sqrtM1_ne_zero : sqrtM1 ≠ 0 := by
  intro h0
  have h := sqrtM1_sq
  rw [h0] at h
  exact one_ne_zero (by linear_combination h)

/-! ## The curve, its addition law, negation, neutral element -/

/-- The twisted Edwards curve equation with a = −1 (Ed25519, RFC 8032 §5.1):

    MATH (ASCII):  OnCurve x y  :<=>  -x^2 + y^2 = 1 + d·x^2·y^2.
    LaTeX: $-x^2 + y^2 = 1 + d x^2 y^2$.
    Rust analog: the (implicit) invariant of `EdwardsPoint` in
    curve25519/solana-ed25519/src/edwards.rs — affine coordinates here,
    extended coordinates there. -/
def OnCurve (x y : Fp) : Prop := -(x^2) + y^2 = 1 + edD * x^2 * y^2

/-- The COMPLETE twisted Edwards addition law (BBJLP "Twisted Edwards
    curves", §6, a = −1):

    MATH:  (x₁,y₁) + (x₂,y₂) =
      ( (x₁y₂ + x₂y₁) / (1 + d·x₁x₂y₁y₂),  (y₁y₂ + x₁x₂) / (1 − d·x₁x₂y₁y₂) ).

    By `completeness` the denominators never vanish on curve points, so the
    division is honest field division everywhere we ever apply it.  (On the
    pair type `Fp × Fp` at large, mathlib's junk-value convention x/0 = 0
    applies — all theorems below restrict to curve points.)
    Rust analog: `EdwardsPoint: Add` (extended-coordinate version) in
    src/edwards.rs — the projective P³ formulas compute exactly these two
    fractions. -/
noncomputable def edAdd (p q : Fp × Fp) : Fp × Fp :=
  ( (p.1*q.2 + q.1*p.2) / (1 + edD*p.1*q.1*p.2*q.2),
    (p.2*q.2 + p.1*q.1) / (1 - edD*p.1*q.1*p.2*q.2) )

/-- Point negation: −(x, y) = (−x, y) (Edwards curves negate the
    x-coordinate).  Rust analog: `EdwardsPoint: Neg` in src/edwards.rs. -/
def edNeg (p : Fp × Fp) : Fp × Fp := (-p.1, p.2)

/-- The neutral element (0, 1).
    Rust analog: `EdwardsPoint::identity()` (X=0, Y=Z=1, T=0). -/
def edId : Fp × Fp := (0, 1)

/-! ## Completeness of the addition law (Bernstein–Lange)

The mathematical heart of the file.  Shape of the argument (BBJLP Thm 3.3 /
Bernstein–Lange "Faster addition and doubling", adapted to a = −1):

Suppose some denominator vanished, i.e. ε := d·x₁x₂y₁y₂ ∈ {−1, +1}.  Then
x₁, x₂, y₁, y₂ are all nonzero (their product is ±1/d ≠ 0), and with
i := √−1 the two curve equations combine into the EXPLICIT square identities

    (i·x₁ + ε·y₁)² = d · x₁²y₁² · (i·x₂ + y₂)²
    (i·x₁ − ε·y₁)² = d · x₁²y₁² · (i·x₂ − y₂)²

(kernel-of-the-proof: ε² = 1 turns d²·(x₁x₂y₁y₂)² into 1, which is what
collapses everything).  At least one of i·x₂ ± y₂ is nonzero — otherwise
2·i·x₂ = 0 forces x₂ = 0 — so dividing the corresponding identity by the
nonzero square (x₁y₁·(i·x₂ ± y₂))² exhibits d as a SQUARE in 𝔽_p,
contradicting `edD_not_square`.  ∎ -/

/- The shared core: NO curve points make d·x₁x₂y₁y₂ a square root of 1.

   MATH (ASCII): OnCurve x1 y1 ∧ OnCurve x2 y2 ∧ ε² = 1 ∧
                 d·x1·x2·y1·y2 = ε  ==>  False.
   Instantiated with ε = −1 (resp. ε = +1) this kills the "+" (resp. "−")
   denominator of `edAdd`.  The two `linear_combination` certificates are the
   polynomial cofactors of the square identities above w.r.t. the ideal
   generated by the two curve equations, heq, i² = −1 and ε² = 1 (computed
   and verified offline; `ring` re-verifies them here).
   WHY NEEDED: the engine behind both halves of `completeness`. -/
theorem denominator_core {x1 y1 x2 y2 : Fp} (h1 : OnCurve x1 y1) (h2 : OnCurve x2 y2)
    (ε : Fp) (hε : ε ^ 2 = 1) (heq : edD * x1 * x2 * y1 * y2 = ε) : False := by
  -- ε is a unit, hence so is the product d·x₁x₂y₁y₂: all factors are nonzero
  have hε0 : ε ≠ 0 := by
    intro h0
    rw [h0] at hε
    exact one_ne_zero (by linear_combination -hε)
  have hne : edD * x1 * x2 * y1 * y2 ≠ 0 := by rw [heq]; exact hε0
  have hy2 : y2 ≠ 0 := right_ne_zero_of_mul hne
  have hy1 : y1 ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hne)
  have hx2 : x2 ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hne))
  have hx1 : x1 ≠ 0 :=
    right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hne)))
  have hi := sqrtM1_sq
  unfold OnCurve at h1 h2
  -- the two Bernstein–Lange square identities (cofactors verified offline)
  have key₁ : (sqrtM1*x1 + ε*y1)^2 = edD * x1^2*y1^2 * (sqrtM1*x2 + y2)^2 := by
    linear_combination h1 - edD*x1^2*y1^2 * h2
      - (edD*x1*x2*y1*y2 + ε + 2*sqrtM1*x1*y1) * heq
      + (x1^2 - edD*x1^2*y1^2*x2^2) * hi + (y1^2 - 1) * hε
  have key₂ : (sqrtM1*x1 - ε*y1)^2 = edD * x1^2*y1^2 * (sqrtM1*x2 - y2)^2 := by
    linear_combination h1 - edD*x1^2*y1^2 * h2
      - (edD*x1*x2*y1*y2 + ε - 2*sqrtM1*x1*y1) * heq
      + (x1^2 - edD*x1^2*y1^2*x2^2) * hi + (y1^2 - 1) * hε
  -- at least one of i·x₂ ± y₂ is a unit; divide the matching identity by it
  by_cases hc : sqrtM1*x2 + y2 = 0
  · -- i·x₂ + y₂ = 0, so i·x₂ − y₂ ≠ 0 (else 2·i·x₂ = 0 forces x₂ = 0)
    have hc2 : sqrtM1*x2 - y2 ≠ 0 := by
      intro hc2
      apply hx2
      have h2x : (2 * sqrtM1) * x2 = 0 := by linear_combination hc + hc2
      rcases mul_eq_zero.mp h2x with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' two_ne_zero_Fp
        · exact absurd h' sqrtM1_ne_zero
      · exact h
    -- d = ((i·x₁ − ε·y₁)/(x₁y₁(i·x₂ − y₂)))² — a square, contradiction
    apply edD_not_square
    refine ⟨(sqrtM1*x1 - ε*y1) / (x1*y1*(sqrtM1*x2 - y2)), ?_⟩
    have hden : x1*y1*(sqrtM1*x2 - y2) ≠ 0 := mul_ne_zero (mul_ne_zero hx1 hy1) hc2
    rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hden hden)]
    linear_combination -key₂
  · -- i·x₂ + y₂ ≠ 0: same square exhibition with the "+" identity
    apply edD_not_square
    refine ⟨(sqrtM1*x1 + ε*y1) / (x1*y1*(sqrtM1*x2 + y2)), ?_⟩
    have hden : x1*y1*(sqrtM1*x2 + y2) ≠ 0 := mul_ne_zero (mul_ne_zero hx1 hy1) hc
    rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hden hden)]
    linear_combination -key₁

/-- THE COMPLETENESS THEOREM (Bernstein–Lange, a = −1 twisted case).

    MATH (ASCII): for all curve points (x1,y1), (x2,y2):
        1 + d·x1·x2·y1·y2 ≠ 0   and   1 − d·x1·x2·y1·y2 ≠ 0.
    LaTeX: $1 \pm d\,x_1x_2y_1y_2 \neq 0$ on $E \times E$.

    Both denominators of `edAdd` are units at EVERY pair of curve points —
    the addition law is complete: one formula, no exceptions, defined even
    for doubling (p = q).  This is precisely why the Rust implementation can
    be branch-free (constant-time) without an exceptional-case audit.
    Proof: if a denominator vanished, d·x₁x₂y₁y₂ would be ∓1, which
    `denominator_core` (using ¬IsSquare d) refutes. -/
theorem completeness {x1 y1 x2 y2 : Fp} (h1 : OnCurve x1 y1) (h2 : OnCurve x2 y2) :
    1 + edD * x1 * x2 * y1 * y2 ≠ 0 ∧ 1 - edD * x1 * x2 * y1 * y2 ≠ 0 := by
  constructor
  · intro hbad
    exact denominator_core h1 h2 (-1) (by norm_num) (by linear_combination hbad)
  · intro hbad
    exact denominator_core h1 h2 1 (by norm_num) (by linear_combination -hbad)

/-! ## The mechanical laws -/

/- MATH: (0, 1) lies on the curve: −0² + 1² = 1 = 1 + d·0²·1².
   WHY NEEDED: the neutral element must be a point for `edAdd_id`/`edAdd_neg`
   to be statements about curve points. -/
theorem onCurve_id : OnCurve 0 1 := by
  unfold OnCurve
  norm_num

/- MATH: (x, y) on the curve ⇒ (−x, y) on the curve ((−x)² = x²).
   WHY NEEDED: `edNeg` maps points to points; feeds `edAdd_neg`. -/
theorem onCurve_neg {x y : Fp} (h : OnCurve x y) : OnCurve (-x) y := by
  unfold OnCurve at h ⊢
  linear_combination h

/- MATH: (x,y) + (0,1) = (x,y) — right identity.  At q = (0,1) the
   denominators are LITERALLY 1 (no completeness needed): the components
   reduce to (x·1 + 0·y)/1 and (y·1 + x·0)/1. -/
theorem edAdd_id {x y : Fp} (_h : OnCurve x y) : edAdd (x, y) edId = (x, y) := by
  unfold edAdd edId
  simp

/- MATH: p + q = q + p — the formula is literally symmetric in p, q (both
   numerators and both denominators are, up to commuting products/sums).
   WHY NEEDED: with `edAdd_id` it gives the LEFT identity for free, and it
   is half of the abelian-group structure (Tier 2). -/
theorem edAdd_comm (p q : Fp × Fp) : edAdd p q = edAdd q p := by
  unfold edAdd
  rw [Prod.mk.injEq]
  constructor
  · rw [show q.1*p.2 + p.1*q.2 = p.1*q.2 + q.1*p.2 from by ring,
        show edD*q.1*p.1*q.2*p.2 = edD*p.1*q.1*p.2*q.2 from by ring]
  · rw [show q.2*p.2 + q.1*p.1 = p.2*q.2 + p.1*q.1 from by ring,
        show edD*q.1*p.1*q.2*p.2 = edD*p.1*q.1*p.2*q.2 from by ring]

/- MATH: (x,y) + (−x,y) = (0,1) — every point has an inverse.
   The x-component's numerator is x·y + (−x)·y = 0 (no completeness needed:
   0/z = 0 for ANY z).  The y-component is (y² − x²)/(1 + d·x²y²); the curve
   equation says numerator = denominator, and completeness (at the point and
   its negation, where the "−" denominator of `edAdd` is 1 + d·x²y²)
   guarantees the denominator is a unit, so the quotient is 1.
   WHY NEEDED: inverses — another quarter of the group structure. -/
theorem edAdd_neg {x y : Fp} (h : OnCurve x y) : edAdd (x, y) (edNeg (x, y)) = edId := by
  -- the "−" denominator at ((x,y), (−x,y)) is 1 − d·x·(−x)·y·y = 1 + d·x²y² ≠ 0
  have hm := (completeness h (onCurve_neg h)).2
  unfold OnCurve at h
  show ( (x*y + -x*y) / (1 + edD * x * -x * y * y),
         (y*y + x * -x) / (1 - edD * x * -x * y * y) ) = (0, 1)
  rw [Prod.mk.injEq]
  constructor
  · rw [show x*y + -x*y = (0 : Fp) from by ring, zero_div]
  · rw [div_eq_iff hm, one_mul]
    linear_combination h

/- MATH: the sum of two curve points is a curve point — `edAdd` is CLOSED on
   the curve.  With x₃ = T/(1+D), y₃ = N/(1−D) (T = x₁y₂+x₂y₁, N = y₁y₂+x₁x₂,
   D = d·x₁x₂y₁y₂), multiplying the target curve equation by the unit
   (1+D)²(1−D)² turns it into the polynomial identity

     −T²(1−D)² + N²(1+D)² = (1+D)²(1−D)² + d·T²·N²,

   which is an explicit combination of the two input curve equations: the
   two big cofactor polynomials in the `linear_combination` below were
   computed offline by a Gröbner-basis reduction of the identity modulo the
   curve ideal, and are re-verified from scratch by `ring` here (the `hT`/
   `hN` summands merely re-relate u = x₃, v = y₃ to their numerators).
   WHY NEEDED: well-definedness of the group operation — the final quarter
   of the Tier-1 group-law package (associativity is Tier 2). -/
theorem edAdd_closure {x1 y1 x2 y2 : Fp} (h1 : OnCurve x1 y1) (h2 : OnCurve x2 y2) :
    OnCurve (edAdd (x1, y1) (x2, y2)).1 (edAdd (x1, y1) (x2, y2)).2 := by
  obtain ⟨hp, hm⟩ := completeness h1 h2
  unfold OnCurve at h1 h2
  show -(((x1*y2 + x2*y1) / (1 + edD*x1*x2*y1*y2))^2)
        + ((y1*y2 + x1*x2) / (1 - edD*x1*x2*y1*y2))^2
      = 1 + edD * ((x1*y2 + x2*y1) / (1 + edD*x1*x2*y1*y2))^2
              * ((y1*y2 + x1*x2) / (1 - edD*x1*x2*y1*y2))^2
  -- name the two components and recover their defining equations
  have hT : (x1*y2 + x2*y1) / (1 + edD*x1*x2*y1*y2) * (1 + edD*x1*x2*y1*y2)
      = x1*y2 + x2*y1 := div_mul_cancel₀ _ hp
  have hN : (y1*y2 + x1*x2) / (1 - edD*x1*x2*y1*y2) * (1 - edD*x1*x2*y1*y2)
      = y1*y2 + x1*x2 := div_mul_cancel₀ _ hm
  set u := (x1*y2 + x2*y1) / (1 + edD*x1*x2*y1*y2) with hu
  set v := (y1*y2 + x1*x2) / (1 - edD*x1*x2*y1*y2) with hv
  -- clear the (unit) denominators: multiply both sides by (1+D)²(1−D)²
  apply mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 2 hp) (pow_ne_zero 2 hm))
  -- …and certify the resulting polynomial identity from the curve equations
  linear_combination
    (edD^3*x1^2*y1^2*x2^4*y2^4 - edD^2*x1^2*x2^4*y2^4 + edD^2*y1^2*x2^4*y2^4
      - edD^2*x2^4*y2^4 - edD*x1^2*x2^4*y2^2 + edD*y1^2*x2^4*y2^2
      + edD*x1^2*x2^2*y2^4 - edD*y1^2*x2^2*y2^4 - 2*edD*x2^4*y2^4
      - 2*x2^4*y2^2 + 2*x2^2*y2^4 - 2*edD*x2^2*y2^2 + x2^4 - 4*x2^2*y2^2
      + y2^4) * h1
    + (edD*x1^4*x2^2*y2^2 + edD*y1^4*x2^2*y2^2 + 2*edD*x1^2*x2^2*y2^2
      - 2*edD*y1^2*x2^2*y2^2 + 2*x1^2*x2^2*y2^2 - 2*y1^2*x2^2*y2^2
      + edD*x2^2*y2^2 - x1^2*x2^2 + y1^2*x2^2 + x1^2*y2^2 - y1^2*y2^2
      + 2*x2^2*y2^2 - x2^2 + y2^2 + 1) * h2
    + (-(1 - edD*x1*x2*y1*y2)^2 * (u*(1 + edD*x1*x2*y1*y2) + (x1*y2 + x2*y1))
       - edD*(y1*y2 + x1*x2)
         * (u*v*(1 + edD*x1*x2*y1*y2)*(1 - edD*x1*x2*y1*y2)
            + (x1*y2 + x2*y1)*(y1*y2 + x1*x2))) * hT
    + ((1 + edD*x1*x2*y1*y2)^2 * (v*(1 - edD*x1*x2*y1*y2) + (y1*y2 + x1*x2))
       - edD*u*(1 + edD*x1*x2*y1*y2)
         * (u*v*(1 + edD*x1*x2*y1*y2)*(1 - edD*x1*x2*y1*y2)
            + (x1*y2 + x2*y1)*(y1*y2 + x1*x2))) * hN

end CurveFieldProofs
