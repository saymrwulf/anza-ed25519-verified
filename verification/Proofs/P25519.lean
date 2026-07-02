/-
═══════════════════════════════════════════════════════════════════════════════
Proofs/P25519.lean — primality of the Curve25519 base-field modulus
                     p = 2^255 − 19, via Lucas/Pratt certificates
═══════════════════════════════════════════════════════════════════════════════

WHAT THIS FILE PROVES
  `p25519_prime : Nat.Prime (2 ^ 255 - 19)` — the 255-bit modulus of the field
  F_p implemented by the Rust crate is a prime number.  Axiom-free, with no
  `native_decide`: every numeric fact is checked by the Lean KERNEL (`decide`)
  through a purpose-built binary modular-exponentiation function (`powMod`).

WHY THE FIELD VERIFICATION NEEDS THIS FILE
  * Mathlib only provides the `Field (ZMod P)` instance — i.e. "F_p really is a
    field, with all field axioms" — from `Fact (Nat.Prime P)`.  The main theorem
    (Proofs/FieldMain.lean, `fieldImplementation`) states that the transpiled
    Rust code implements exactly that field, so primality is a prerequisite for
    even *stating* the result.  Proofs/Field.lean consumes `p25519_prime` to
    build `P_prime : Nat.Prime P` and the `Fact`/`NeZero` instances.
  * Rust analog (indirect — this file contains no transpiled code):
    `FieldElement::invert`, curve25519/solana-ed25519/src/field.rs:239-248,
    computes x^(p−2) and its doc comment justifies this with
    "x^(p-2)·x = x^(p-1) = 1 (mod p)" — Fermat's little theorem, which is
    only valid because p is prime.  Proofs/InvertSpec.lean formalizes exactly
    that argument and needs the primality proved here.

PLACE IN THE IMPORT GRAPH
  Leaf: imports only mathlib (LucasPrimality, ZMod, norm_num-prime).
  Imported by Proofs/Field.lean, and through it by Proofs/InvertSpec.lean and
  Proofs/FieldMain.lean.

THE PROOF TECHNIQUE, FOR THE LAY READER (Lucas test / Pratt certificates)
  How do you convince a proof CHECKER that a 255-bit number n is prime without
  trial division up to 2^127?  Use the classical Lucas test (the basis of
  "Pratt certificates", the textbook proof that PRIMES ∈ NP):

      if some witness g satisfies
        (1)  g^(n−1) ≡ 1 (mod n)                          (Fermat condition)
        (2)  g^((n−1)/q) ≢ 1 (mod n)  for EVERY prime q dividing n−1,
      then n is prime.

  Why this works: (1) says the multiplicative order of g modulo n divides n−1;
  if that order were a PROPER divisor of n−1 it would divide (n−1)/q for some
  prime q | n−1, contradicting (2).  So g has order exactly n−1 in the unit
  group of Z/n.  But that group has only φ(n) ≤ n−1 elements, so an element of
  order n−1 can exist only if φ(n) = n−1 — which happens precisely when n is
  prime.  Mathlib packages this as `lucas_primality`.

  The catch: condition (2) needs the COMPLETE prime factorization of n−1, and
  each prime factor q must itself be certified prime — recursively, by the
  same test.  The recursion bottoms out at factors small enough for mathlib's
  `norm_num` prime checker.  The published factor tree used below (any
  factoring tool reproduces it; the kernel re-verifies every product):

    p − 1 = 2^2 · 3 · 65147 · q1,             p = 2^255 − 19
      q1 = 740582127325613583022312264370627\
           88676166966415465897661863160754340907                  (236 bits)
      q1 − 1 = 2 · 3 · 353 · 57467 · 132049 · 1923133 · q2 · q3
        q2 = 31757755568855353
        q2 − 1 = 2^3 · 3 · 31 · 107 · 223 · 4153 · 430751   (all small)
        q3 = 75445702479781427272750846543864801
        q3 − 1 = 2^5 · 3^2 · 5^2 · 75707 · q4 · q5
          q4 = 72106336199
          q4 − 1 = 2 · 13 · q6
            q6 = 2773320623,   q6 − 1 = 2 · 2437 · 569003    (all small)
          q5 = 1919519569386763
          q5 − 1 = 2 · 3 · 7 · 19 · 47^2 · 127 · q7
            q7 = 8574133,      q7 − 1 = 2^2 · 3 · 7 · 103 · 991  (all small)

  The certificate theorems below appear leaves-first:
  q7, q6, q4, q5, q2, q3, q1, and finally p itself.

WHY `powMod` EXISTS
  Checking condition (1) for p means verifying a congruence with a 255-bit
  exponent.  `decide` on `(2 : ZMod n) ^ (n−1) = 1` directly is hopeless: `^`
  on `ZMod n` unfolds to n−1 ≈ 2^255 repeated multiplications.  Instead we
  define square-and-multiply on raw `Nat` (`powModAux`), prove ONCE that it
  computes `a ^ k % n` (`powModAux_eq`), and then every certificate condition
  becomes a closed equation `powMod a k n = 1` (or `≠ 1`) between `Nat`
  literals.  Lean's kernel evaluates `Nat` literal arithmetic (·, %, /) with
  GMP big-integer primitives, so each such `decide` costs ~256 squarings of
  ≤255-bit numbers — milliseconds, entirely inside the trusted kernel.
-/
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum.Prime

-- Elaborating `decide` on the huge decimal literals below builds deep numeral
-- terms; raise the elaborator's recursion limit so they go through.
set_option maxRecDepth 8000

-- All helpers and per-node certificates live in their own namespace; only the
-- final `p25519_prime` (stated about `2 ^ 255 - 19` itself) is exported at top
-- level for Proofs/Field.lean.
namespace P25519

-- ─────────────────────────────────────────────────────────────────────────────
-- Kernel-checkable modular exponentiation
-- ─────────────────────────────────────────────────────────────────────────────

/-- Fuel-based binary modular exponentiation, kernel-reducible (GMP-fast `decide`).

MATH (for sufficient fuel; made precise by `powModAux_eq`):
  `powModAux fuel a k n = a^k mod n`.
Algorithm: square-and-multiply, consuming the binary digits of `k` from the
low end —
  k = 0      ↦ 1 mod n
  k = 2m     ↦ (a² mod n)^m  mod n
  k = 2m+1   ↦ ((a² mod n)^m mod n) · a  mod n
Every intermediate is reduced mod n, so no value ever exceeds n² (≈510 bits
here) — this is what keeps kernel evaluation fast.

WHY THE `fuel` ARGUMENT: recursion is on `fuel` (plain structural recursion),
not on `k`.  Recursing on `k/2 < k` would be well-founded recursion, which
Lean compiles to `WellFounded.fix` — a fixpoint the kernel cannot unfold
during `decide`.  With fuel, the kernel just peels one constructor per step.

WHY NEEDED: this is the workhorse that lets the kernel verify 255-bit
Fermat-witness congruences in milliseconds (see file header). -/
def powModAux : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, n => 1 % n
  | fuel + 1, a, k, n =>
    if k = 0 then 1 % n
    else if k % 2 = 1 then powModAux fuel (a * a % n) (k / 2) n * a % n
    else powModAux fuel (a * a % n) (k / 2) n

/- Correctness of `powModAux`.

   MATH (ASCII):  forall fuel a k n,  k < 2^fuel  ==>
                  powModAux fuel a k n = a^k mod n
   LaTeX: $\forall\,\mathit{fuel}\,a\,k\,n,\ k < 2^{\mathit{fuel}}
           \Rightarrow \mathrm{powModAux}\ \mathit{fuel}\ a\ k\ n = a^k \bmod n$
   The hypothesis `k < 2^fuel` says the fuel covers every binary digit of the
   exponent, so the recursion never runs dry.

   WHY NEEDED: turns each kernel computation `powMod a k n = …` into the
   mathematical statement `a^k % n = …` that `lucas_primality` needs.
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

/-- `powMod a k n = a ^ k % n` for all `k < 2 ^ 256`.

The fuel is fixed at 256: enough for any exponent below 2^256, in particular
for every exponent `(n−1)/q` appearing in the certificates (n ≤ p < 2^255).

WHY NEEDED: the single entry point all certificate side-conditions are stated
through, so each becomes one GMP-fast kernel `decide`. -/
def powMod (a k n : ℕ) : ℕ := powModAux 256 a k n

/- Bridge from the `Nat` computation into `ZMod n`, where `lucas_primality`
   lives.

   MATH:  k < 2^256  ==>  (a : ZMod n)^k = (powMod a k n : ZMod n)
   i.e. casting `a` to Z/n and exponentiating there agrees with computing
   `a^k mod n` over the naturals and casting the result.  Follows from
   `powModAux_eq` plus the fact that the cast Nat → ZMod n is a ring
   homomorphism that kills `% n`.

   WHY NEEDED: the two lemmas below (`pow_eq_one_of_powMod`,
   `pow_ne_one_of_powMod`) are corollaries of this one. -/
theorem cast_pow_eq (a k n : ℕ) (hk : k < 2 ^ 256) :
    (a : ZMod n) ^ k = ((powMod a k n : ℕ) : ZMod n) := by
  rw [powMod, powModAux_eq 256 a k n hk, ZMod.natCast_mod, Nat.cast_pow]

/- Positive direction — discharges the FERMAT condition (1) of the Lucas test.

   MATH:  k < 2^256  and  powMod a k n = 1   ==>   (a : ZMod n)^k = 1.
   The hypothesis `powMod a k n = 1` is a closed `Nat` equation the kernel
   checks by `decide`; this lemma lifts it to the `ZMod n` equation that
   `lucas_primality` consumes. -/
theorem pow_eq_one_of_powMod (a k n : ℕ) (hk : k < 2 ^ 256) (h : powMod a k n = 1) :
    (a : ZMod n) ^ k = 1 := by
  rw [cast_pow_eq a k n hk, h, Nat.cast_one]

/- Negative direction — discharges the ORDER condition (2) of the Lucas test.

   MATH:  k < 2^256, 1 < n, powMod a k n ≠ 1, powMod a k n < n
          ==>   (a : ZMod n)^k ≠ 1.
   Subtlety: distinct naturals can become EQUAL in Z/n (they may differ by a
   multiple of n), so `powMod a k n ≠ 1` alone is not enough.  The extra
   hypotheses pin both sides into the canonical range [0, n): the computed
   residue is < n (true by construction, but cheaper to re-`decide` than to
   prove generically) and 1 < n.  Within that range the cast Nat → ZMod n is
   injective (`ZMod.natCast_eq_natCast_iff'` + `Nat.mod_eq_of_lt`), so
   inequality transfers.

   WHY NEEDED: one application per prime factor q of n−1, with
   k = (n−1)/q — this is what forces the witness to have full order n−1. -/
theorem pow_ne_one_of_powMod (a k n : ℕ) (hk : k < 2 ^ 256) (hn : 1 < n)
    (h1 : powMod a k n ≠ 1) (h2 : powMod a k n < n) :
    (a : ZMod n) ^ k ≠ 1 := by
  -- replace the ZMod power by the cast of the computed Nat residue
  rw [cast_pow_eq a k n hk]
  intro hcon
  -- equality of casts in ZMod n means equality of the residues mod n…
  rw [show (1 : ZMod n) = ((1 : ℕ) : ZMod n) by rw [Nat.cast_one],
      ZMod.natCast_eq_natCast_iff'] at hcon
  -- …and both residues are already < n, so they are equal as naturals
  rw [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt hn] at hcon
  exact h1 hcon

-- ─────────────────────────────────────────────────────────────────────────────
-- The certificate chain, leaves first (factor tree in the file header).
--
-- Every theorem instantiates mathlib's
--   lucas_primality (n) (g : ZMod n) (h1) (h2) : Nat.Prime n
-- with a concrete witness g, discharging
--   h1 : g^(n−1) = 1 in ZMod n                via `pow_eq_one_of_powMod`
--        (its two `by decide`s check: n−1 < 2^256, and the powMod equation)
--   h2 : ∀ q prime, q ∣ n−1 → g^((n−1)/q) ≠ 1 via `pow_ne_one_of_powMod`
--        (its four `by decide`s check: (n−1)/q < 2^256, 1 < n,
--         powMod g ((n−1)/q) n ≠ 1, and powMod … < n).
--
-- For h2 the published factorization of n−1 is stated as a NESTED product
-- 2^e * (f1 * (f2 * (…))) and verified by one `decide` (a single big-number
-- multiplication).  `rcases (Nat.Prime.dvd_mul hq).mp` then peels the factors
-- left to right: a prime q dividing the product divides the head factor or
-- the tail.  Dividing the head pins q to a concrete prime via
-- `Nat.prime_dvd_prime_iff_eq` ("a prime divides a prime iff they are
-- equal"); for prime-power heads like 2^2 we first strip the exponent with
-- `hq.dvd_of_dvd_pow`.  Head factors small enough are certified prime by
-- `norm_num`; large ones by the earlier theorems of this chain — that
-- reference IS the recursion of the Pratt certificate.
-- ─────────────────────────────────────────────────────────────────────────────

/- Leaf q7 of the factor tree: 8574133 is prime (needed for q5 below).
   Witness g = 2;  8574133 − 1 = 2^2 · 3 · 7 · 103 · 991, all `norm_num`-small.
   This first certificate is annotated line by line; the six that follow are
   structurally identical. -/
theorem prime_8574133 : Nat.Prime 8574133 := by
  -- pick the witness g = 2 and split into the two Lucas obligations
  refine lucas_primality 8574133 ((2 : ℕ) : ZMod 8574133) ?_ ?_
  -- (1) Fermat: 2^(n−1) ≡ 1 (mod n) — one kernel powMod computation
  · exact pow_eq_one_of_powMod 2 (8574133 - 1) 8574133 (by decide) (by decide)
  -- (2) full order: any prime q | n−1 must leave 2^((n−1)/q) ≢ 1 (mod n)
  · intro q hq hqd
    -- kernel-verified factorization of n−1, nested for left-to-right peeling
    have hfac : (8574133 : ℕ) - 1 = 2 ^ 2 * (3 * (7 * (103 * (991)))) := by decide
    rw [hfac] at hqd
    -- q | 2^2 · rest: either q | 2^2 (then q = 2) or q divides the rest
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h)
      subst he
      -- 2^((n−1)/2) ≢ 1 (mod n), checked by the kernel
      exact pow_ne_one_of_powMod 2 ((8574133 - 1) / 2) 8574133 (by decide) (by decide) (by decide) (by decide)
    -- q | 3 · rest: peel the factor 3
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((8574133 - 1) / 3) 8574133 (by decide) (by decide) (by decide) (by decide)
    -- peel the factor 7
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 7 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((8574133 - 1) / 7) 8574133 (by decide) (by decide) (by decide) (by decide)
    -- peel the factor 103
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 103 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((8574133 - 1) / 103) 8574133 (by decide) (by decide) (by decide) (by decide)
    -- only the last factor 991 remains
    have he : q = 991 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp hqd
    subst he
    exact pow_ne_one_of_powMod 2 ((8574133 - 1) / 991) 8574133 (by decide) (by decide) (by decide) (by decide)

/- Leaf q6 of the factor tree: 2773320623 is prime (needed for q4 below).
   Witness g = 5;  2773320623 − 1 = 2 · 2437 · 569003, all `norm_num`-small.
   (g = 2 would fail here: 2 is a quadratic residue mod this prime, so
   2^((n−1)/2) ≡ 1 and the q = 2 order check breaks; hence the witness 5.) -/
theorem prime_2773320623 : Nat.Prime 2773320623 := by
  refine lucas_primality 2773320623 ((5 : ℕ) : ZMod 2773320623) ?_ ?_
  -- Fermat condition, then one order check per prime factor of n−1
  · exact pow_eq_one_of_powMod 5 (2773320623 - 1) 2773320623 (by decide) (by decide)
  · intro q hq hqd
    have hfac : (2773320623 : ℕ) - 1 = 2 * (2437 * (569003)) := by decide
    rw [hfac] at hqd
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 5 ((2773320623 - 1) / 2) 2773320623 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 2437 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 5 ((2773320623 - 1) / 2437) 2773320623 (by decide) (by decide) (by decide) (by decide)
    have he : q = 569003 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp hqd
    subst he
    exact pow_ne_one_of_powMod 5 ((2773320623 - 1) / 569003) 2773320623 (by decide) (by decide) (by decide) (by decide)

/- Node q4 of the factor tree: 72106336199 is prime (needed for q3 below).
   Witness g = 7;  72106336199 − 1 = 2 · 13 · 2773320623.
   First RECURSIVE step of the Pratt certificate: the large factor q6 is
   certified by `prime_2773320623` above instead of `norm_num`. -/
theorem prime_72106336199 : Nat.Prime 72106336199 := by
  refine lucas_primality 72106336199 ((7 : ℕ) : ZMod 72106336199) ?_ ?_
  · exact pow_eq_one_of_powMod 7 (72106336199 - 1) 72106336199 (by decide) (by decide)
  · intro q hq hqd
    have hfac : (72106336199 : ℕ) - 1 = 2 * (13 * (2773320623)) := by decide
    rw [hfac] at hqd
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 7 ((72106336199 - 1) / 2) 72106336199 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 13 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 7 ((72106336199 - 1) / 13) 72106336199 (by decide) (by decide) (by decide) (by decide)
    -- last factor: q6 = 2773320623, prime by the recursive certificate above
    have he : q = 2773320623 := (Nat.prime_dvd_prime_iff_eq hq prime_2773320623).mp hqd
    subst he
    exact pow_ne_one_of_powMod 7 ((72106336199 - 1) / 2773320623) 72106336199 (by decide) (by decide) (by decide) (by decide)

/- Node q5 of the factor tree: 1919519569386763 is prime (needed for q3 below).
   Witness g = 2;  q5 − 1 = 2 · 3 · 7 · 19 · 47^2 · 127 · 8574133.
   Note the prime-power factor 47^2: only ONE order check is needed per
   distinct prime (the test divides n−1 by q once), so the branch for 47
   strips the square with `hq.dvd_of_dvd_pow` first.  The large factor
   q7 = 8574133 is certified by `prime_8574133`. -/
theorem prime_1919519569386763 : Nat.Prime 1919519569386763 := by
  refine lucas_primality 1919519569386763 ((2 : ℕ) : ZMod 1919519569386763) ?_ ?_
  · exact pow_eq_one_of_powMod 2 (1919519569386763 - 1) 1919519569386763 (by decide) (by decide)
  · intro q hq hqd
    have hfac : (1919519569386763 : ℕ) - 1 = 2 * (3 * (7 * (19 * (47 ^ 2 * (127 * (8574133)))))) := by decide
    rw [hfac] at hqd
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((1919519569386763 - 1) / 2) 1919519569386763 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((1919519569386763 - 1) / 3) 1919519569386763 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 7 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((1919519569386763 - 1) / 7) 1919519569386763 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 19 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((1919519569386763 - 1) / 19) 1919519569386763 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 47 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h)
      subst he
      exact pow_ne_one_of_powMod 2 ((1919519569386763 - 1) / 47) 1919519569386763 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 127 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((1919519569386763 - 1) / 127) 1919519569386763 (by decide) (by decide) (by decide) (by decide)
    -- last factor: q7 = 8574133, prime by the recursive certificate above
    have he : q = 8574133 := (Nat.prime_dvd_prime_iff_eq hq prime_8574133).mp hqd
    subst he
    exact pow_ne_one_of_powMod 2 ((1919519569386763 - 1) / 8574133) 1919519569386763 (by decide) (by decide) (by decide) (by decide)

/- Leaf q2 of the factor tree: 31757755568855353 is prime (needed for q1).
   Witness g = 10;  q2 − 1 = 2^3 · 3 · 31 · 107 · 223 · 4153 · 430751,
   all `norm_num`-small — no recursion needed for this node. -/
theorem prime_31757755568855353 : Nat.Prime 31757755568855353 := by
  refine lucas_primality 31757755568855353 ((10 : ℕ) : ZMod 31757755568855353) ?_ ?_
  · exact pow_eq_one_of_powMod 10 (31757755568855353 - 1) 31757755568855353 (by decide) (by decide)
  · intro q hq hqd
    have hfac : (31757755568855353 : ℕ) - 1 = 2 ^ 3 * (3 * (31 * (107 * (223 * (4153 * (430751)))))) := by decide
    rw [hfac] at hqd
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h)
      subst he
      exact pow_ne_one_of_powMod 10 ((31757755568855353 - 1) / 2) 31757755568855353 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 10 ((31757755568855353 - 1) / 3) 31757755568855353 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 31 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 10 ((31757755568855353 - 1) / 31) 31757755568855353 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 107 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 10 ((31757755568855353 - 1) / 107) 31757755568855353 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 223 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 10 ((31757755568855353 - 1) / 223) 31757755568855353 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 4153 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 10 ((31757755568855353 - 1) / 4153) 31757755568855353 (by decide) (by decide) (by decide) (by decide)
    have he : q = 430751 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp hqd
    subst he
    exact pow_ne_one_of_powMod 10 ((31757755568855353 - 1) / 430751) 31757755568855353 (by decide) (by decide) (by decide) (by decide)

/- Node q3 of the factor tree: the 116-bit 75445702479781427272750846543864801
   is prime (needed for q1).  Witness g = 7;
   q3 − 1 = 2^5 · 3^2 · 5^2 · 75707 · q4 · q5  with the two large factors
   q4 = 72106336199 and q5 = 1919519569386763 certified recursively above. -/
theorem prime_75445702479781427272750846543864801 : Nat.Prime 75445702479781427272750846543864801 := by
  refine lucas_primality 75445702479781427272750846543864801 ((7 : ℕ) : ZMod 75445702479781427272750846543864801) ?_ ?_
  · exact pow_eq_one_of_powMod 7 (75445702479781427272750846543864801 - 1) 75445702479781427272750846543864801 (by decide) (by decide)
  · intro q hq hqd
    have hfac : (75445702479781427272750846543864801 : ℕ) - 1 = 2 ^ 5 * (3 ^ 2 * (5 ^ 2 * (75707 * (72106336199 * (1919519569386763))))) := by decide
    rw [hfac] at hqd
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h)
      subst he
      exact pow_ne_one_of_powMod 7 ((75445702479781427272750846543864801 - 1) / 2) 75445702479781427272750846543864801 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h)
      subst he
      exact pow_ne_one_of_powMod 7 ((75445702479781427272750846543864801 - 1) / 3) 75445702479781427272750846543864801 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 5 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h)
      subst he
      exact pow_ne_one_of_powMod 7 ((75445702479781427272750846543864801 - 1) / 5) 75445702479781427272750846543864801 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 75707 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 7 ((75445702479781427272750846543864801 - 1) / 75707) 75445702479781427272750846543864801 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    -- factor q4 = 72106336199: prime by the recursive certificate above
    · have he : q = 72106336199 := (Nat.prime_dvd_prime_iff_eq hq prime_72106336199).mp h
      subst he
      exact pow_ne_one_of_powMod 7 ((75445702479781427272750846543864801 - 1) / 72106336199) 75445702479781427272750846543864801 (by decide) (by decide) (by decide) (by decide)
    -- last factor q5 = 1919519569386763: prime by the recursive certificate
    have he : q = 1919519569386763 := (Nat.prime_dvd_prime_iff_eq hq prime_1919519569386763).mp hqd
    subst he
    exact pow_ne_one_of_powMod 7 ((75445702479781427272750846543864801 - 1) / 1919519569386763) 75445702479781427272750846543864801 (by decide) (by decide) (by decide) (by decide)

/- Node q1 of the factor tree: the 236-bit cofactor of p − 1 is prime.
   Witness g = 2;
   q1 − 1 = 2 · 3 · 353 · 57467 · 132049 · 1923133 · q2 · q3,
   with q2 = 31757755568855353 and q3 = 75445702479781427272750846543864801
   certified recursively above.  This is the last node below the root. -/
theorem prime_74058212732561358302231226437062788676166966415465897661863160754340907 : Nat.Prime 74058212732561358302231226437062788676166966415465897661863160754340907 := by
  refine lucas_primality 74058212732561358302231226437062788676166966415465897661863160754340907 ((2 : ℕ) : ZMod 74058212732561358302231226437062788676166966415465897661863160754340907) ?_ ?_
  · exact pow_eq_one_of_powMod 2 (74058212732561358302231226437062788676166966415465897661863160754340907 - 1) 74058212732561358302231226437062788676166966415465897661863160754340907 (by decide) (by decide)
  · intro q hq hqd
    have hfac : (74058212732561358302231226437062788676166966415465897661863160754340907 : ℕ) - 1 = 2 * (3 * (353 * (57467 * (132049 * (1923133 * (31757755568855353 * (75445702479781427272750846543864801))))))) := by decide
    rw [hfac] at hqd
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((74058212732561358302231226437062788676166966415465897661863160754340907 - 1) / 2) 74058212732561358302231226437062788676166966415465897661863160754340907 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((74058212732561358302231226437062788676166966415465897661863160754340907 - 1) / 3) 74058212732561358302231226437062788676166966415465897661863160754340907 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 353 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((74058212732561358302231226437062788676166966415465897661863160754340907 - 1) / 353) 74058212732561358302231226437062788676166966415465897661863160754340907 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 57467 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((74058212732561358302231226437062788676166966415465897661863160754340907 - 1) / 57467) 74058212732561358302231226437062788676166966415465897661863160754340907 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 132049 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((74058212732561358302231226437062788676166966415465897661863160754340907 - 1) / 132049) 74058212732561358302231226437062788676166966415465897661863160754340907 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 1923133 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((74058212732561358302231226437062788676166966415465897661863160754340907 - 1) / 1923133) 74058212732561358302231226437062788676166966415465897661863160754340907 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    -- factor q2: prime by the recursive certificate above
    · have he : q = 31757755568855353 := (Nat.prime_dvd_prime_iff_eq hq prime_31757755568855353).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((74058212732561358302231226437062788676166966415465897661863160754340907 - 1) / 31757755568855353) 74058212732561358302231226437062788676166966415465897661863160754340907 (by decide) (by decide) (by decide) (by decide)
    -- last factor q3: prime by the recursive certificate above
    have he : q = 75445702479781427272750846543864801 := (Nat.prime_dvd_prime_iff_eq hq prime_75445702479781427272750846543864801).mp hqd
    subst he
    exact pow_ne_one_of_powMod 2 ((74058212732561358302231226437062788676166966415465897661863160754340907 - 1) / 75445702479781427272750846543864801) 74058212732561358302231226437062788676166966415465897661863160754340907 (by decide) (by decide) (by decide) (by decide)

/- ROOT of the factor tree: p = 2^255 − 19 itself, written out in decimal
   (57896044618658097711785492504343953926634992332820282019728792003956564819949).
   Witness g = 2 (2 is in fact a primitive root mod p);
   p − 1 = 2^2 · 3 · 65147 · q1, with the 236-bit q1 certified just above.
   Each `powMod` check here exponentiates with a ~255-bit exponent modulo the
   255-bit p — still milliseconds thanks to GMP-backed kernel `Nat` arithmetic. -/
theorem prime_57896044618658097711785492504343953926634992332820282019728792003956564819949 : Nat.Prime 57896044618658097711785492504343953926634992332820282019728792003956564819949 := by
  refine lucas_primality 57896044618658097711785492504343953926634992332820282019728792003956564819949 ((2 : ℕ) : ZMod 57896044618658097711785492504343953926634992332820282019728792003956564819949) ?_ ?_
  · exact pow_eq_one_of_powMod 2 (57896044618658097711785492504343953926634992332820282019728792003956564819949 - 1) 57896044618658097711785492504343953926634992332820282019728792003956564819949 (by decide) (by decide)
  · intro q hq hqd
    have hfac : (57896044618658097711785492504343953926634992332820282019728792003956564819949 : ℕ) - 1 = 2 ^ 2 * (3 * (65147 * (74058212732561358302231226437062788676166966415465897661863160754340907))) := by decide
    rw [hfac] at hqd
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h)
      subst he
      exact pow_ne_one_of_powMod 2 ((57896044618658097711785492504343953926634992332820282019728792003956564819949 - 1) / 2) 57896044618658097711785492504343953926634992332820282019728792003956564819949 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((57896044618658097711785492504343953926634992332820282019728792003956564819949 - 1) / 3) 57896044618658097711785492504343953926634992332820282019728792003956564819949 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 65147 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((57896044618658097711785492504343953926634992332820282019728792003956564819949 - 1) / 65147) 57896044618658097711785492504343953926634992332820282019728792003956564819949 (by decide) (by decide) (by decide) (by decide)
    -- last factor q1: prime by the recursive certificate above
    have he : q = 74058212732561358302231226437062788676166966415465897661863160754340907 := (Nat.prime_dvd_prime_iff_eq hq prime_74058212732561358302231226437062788676166966415465897661863160754340907).mp hqd
    subst he
    exact pow_ne_one_of_powMod 2 ((57896044618658097711785492504343953926634992332820282019728792003956564819949 - 1) / 74058212732561358302231226437062788676166966415465897661863160754340907) 57896044618658097711785492504343953926634992332820282019728792003956564819949 (by decide) (by decide) (by decide) (by decide)

end P25519

-- ─────────────────────────────────────────────────────────────────────────────
-- Exported result
-- ─────────────────────────────────────────────────────────────────────────────

/-- The Curve25519 field prime `2 ^ 255 - 19` is prime.

MATH (ASCII):  Nat.Prime (2^255 - 19)
LaTeX:  $2^{255} - 19$ is prime.

This is the only theorem of this file used downstream: Proofs/Field.lean turns
it into `P_prime : Nat.Prime P` (where `P` abbreviates the same number) and the
`Fact (Nat.Prime P)` instance, which activates mathlib's `Field (ZMod P)` —
the target structure of the main theorem `fieldImplementation`
(Proofs/FieldMain.lean) — and feeds Fermat's little theorem to the inverse
spec (Proofs/InvertSpec.lean), mirroring the comment on
`FieldElement::invert` in curve25519/solana-ed25519/src/field.rs:239-248. -/
theorem p25519_prime : Nat.Prime (2 ^ 255 - 19) := by
  -- rewrite 2^255 − 19 into the decimal literal the root certificate is about
  have h : (2 : ℕ) ^ 255 - 19 = 57896044618658097711785492504343953926634992332820282019728792003956564819949 := by decide
  rw [h]
  exact P25519.prime_57896044618658097711785492504343953926634992332820282019728792003956564819949
