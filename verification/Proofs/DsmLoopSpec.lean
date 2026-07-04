/- ──────────────────────────────────────────────────────────────────────────────
   Proofs/DsmLoopSpec.lean — double-scalar-mul campaign, brick 3:
   the 256-iteration Straus/NAF loop, by genuine induction (no unrolling).

   dsm_loop seeds r = identity, j = top+1 and runs
       while j > 0 { idx = j-1; t = r.double();
                     t = dsm_step_p(t, table_a, a_naf[idx]);
                     t = dsm_step_b(t, table_b, b_naf[idx]);
                     r = t.as_projective(); j = idx; }

   ABSTRACTION: `dsmFold aD bD pA pB P j` — process digits j−1 … 0 onto the
   accumulator P over the abstract Edwards addition: each iteration doubles
   and applies the two digits through `edDigit` (DsmStepSpec). The loop
   invariant is
       ProjValid r ∧ OnCurve (projPt r) ∧ result = dsmFold … (projPt r) j
   proven by induction on j.val, one symbolic body-walk per induction step:
   proj_double_law → dsm_step_p_law → dsm_step_b_law → compl_as_projective_law.

   Digit hypotheses (odd-or-zero, |d| < 16, for all 256 positions of both
   arrays) are exactly what the NAF spec will provide (layering). Table
   hypotheses are naf_table_spec's post for both tables.
   ────────────────────────────────────────────────────────────────────────────── -/
import Proofs.DsmStepSpec
open Aeneas Aeneas.Std Result ControlFlow
open curve25519

set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000

namespace CurveFieldProofs

open Aeneas.Std.WP

/-! ### The abstract double-and-add fold -/

/-- The k-th NAF digit of an extracted digit array, as an integer. -/
def nafDigit (a : Std.Array Std.I8 256#usize) (k : ℕ) : ℤ := (a.val[k]!).val

/-- `dsmFold aD bD pA pB P j`: apply digits j−1, j−2, …, 0 to accumulator P —
    per digit: double, add aD's digit-multiple of pA, add bD's digit-multiple
    of pB (all through `edDigit`, over the abstract `edAdd`). -/
noncomputable def dsmFold (aD bD : ℕ → ℤ) (pA pB : Fp × Fp) :
    (Fp × Fp) → ℕ → Fp × Fp
  | P, 0 => P
  | P, j + 1 => dsmFold aD bD pA pB
      (edDigit pB (bD j) (edDigit pA (aD j) (edAdd P P))) j

@[simp] theorem dsmFold_zero (aD bD : ℕ → ℤ) (pA pB P : Fp × Fp) :
    dsmFold aD bD pA pB P 0 = P := rfl

theorem dsmFold_succ (aD bD : ℕ → ℤ) (pA pB P : Fp × Fp) (j : ℕ) :
    dsmFold aD bD pA pB P (j + 1) = dsmFold aD bD pA pB
      (edDigit pB (bD j) (edDigit pA (aD j) (edAdd P P))) j := rfl

/- The neutral point is on the curve: `onCurve_id` (EdCurve.lean). -/

/-- Digit-array contract: every position is a NAF digit — odd or zero,
    magnitude below 16. (The NAF spec provides this; layering.) -/
def NafDigits (a : Std.Array Std.I8 256#usize) : Prop :=
  ∀ k : ℕ, k < 256 →
    (nafDigit a k = 0 ∨ nafDigit a k % 2 = 1) ∧
    -16 < nafDigit a k ∧ nafDigit a k < 16

/-- Table contract: the 8 entries are proven caches of the odd multiples
    of A (naf_table_spec's post, bundled). -/
def NafTableOf
    (tbl : window.NafLookupTable5 backend.serial.curve_models.ProjectiveNielsPoint)
    (A : EdPoint) : Prop :=
  ∃ e0 e1 e2 e3 e4 e5 e6 e7,
    tblEntries tbl = [e0, e1, e2, e3, e4, e5, e6, e7] ∧
    NafEntryOf e0 A 0 ∧ NafEntryOf e1 A 1 ∧ NafEntryOf e2 A 2 ∧
    NafEntryOf e3 A 3 ∧ NafEntryOf e4 A 4 ∧ NafEntryOf e5 A 5 ∧
    NafEntryOf e6 A 6 ∧ NafEntryOf e7 A 7

/-! ### The loop induction -/

/-- **The Straus loop body, by induction on the counter.** From any valid
    on-curve accumulator r at counter j ≤ 256, the loop returns a valid
    on-curve point denoting `dsmFold` of the remaining digits applied to
    (projX r, projY r). One symbolic walk per induction step. -/
theorem dsm_loop_loop_spec
    (a_naf b_naf : Std.Array Std.I8 256#usize)
    (ta tb : window.NafLookupTable5 backend.serial.curve_models.ProjectiveNielsPoint)
    (A B : EdPoint)
    (hta : NafTableOf ta A) (htb : NafTableOf tb B)
    (hda : NafDigits a_naf) (hdb : NafDigits b_naf)
    (n : ℕ) :
    ∀ (j : Usize) (r : ProjPoint), j.val = n → n ≤ 256 →
    ProjValid r → OnCurve (projX r) (projY r) →
    backend.serial.scalar_mul.vartime_double_base.dsm_loop_loop
      a_naf b_naf ta tb r j ⦃ res =>
        ProjValid res ∧ OnCurve (projX res) (projY res) ∧
        (projX res, projY res) = dsmFold (nafDigit a_naf) (nafDigit b_naf)
          (edPt A) (edPt B) (projX r, projY r) n ⦄ := by
  obtain ⟨eA0, eA1, eA2, eA3, eA4, eA5, eA6, eA7, hlA,
    hA0, hA1, hA2, hA3, hA4, hA5, hA6, hA7⟩ := hta
  obtain ⟨eB0, eB1, eB2, eB3, eB4, eB5, eB6, eB7, hlB,
    hB0, hB1, hB2, hB3, hB4, hB5, hB6, hB7⟩ := htb
  induction n with
  | zero =>
    intro j r hj hle hv hc
    unfold backend.serial.scalar_mul.vartime_double_base.dsm_loop_loop
    apply loop_step
    simp only [backend.serial.scalar_mul.vartime_double_base.dsm_loop_loop.body]
    have hj0 : ¬ (j > 0#usize) := by clear * - hj; scalar_tac
    rw [if_neg hj0]
    try simp only [spec_ok]
    exact ⟨hv, hc, rfl⟩
  | succ n ih =>
    intro j r hj hle hv hc
    unfold backend.serial.scalar_mul.vartime_double_base.dsm_loop_loop
    apply loop_step
    simp only [backend.serial.scalar_mul.vartime_double_base.dsm_loop_loop.body]
    have hjpos : j > 0#usize := by clear * - hj; scalar_tac
    rw [if_pos hjpos]
    -- idx ← j − 1
    step as ⟨idx, hidx⟩
    have hidxv : idx.val = n := by clear * - hidx hj; scalar_tac
    -- t0 ← r.double()   (the projective doubling law)
    step with (proj_double_law r hv hc) as
      ⟨t0, t0bX, t0bY, t0bZ, t0bT, t0z, t0t, t0x, t0y⟩
    have hct0 : OnCurve (complX t0) (complY t0) := by
      rw [t0x, t0y]
      exact edAdd_closure hc hc
    -- da ← a_naf[idx]
    step as ⟨da, hdav⟩
    have hban : n < (↑a_naf : List Std.I8).length := by
      clear * - hle; scalar_tac
    have hdaq : da.val = nafDigit a_naf n := by
      rw [hdav]
      simp only [nafDigit, hidxv, getElem!_pos (↑a_naf : List Std.I8) n hban]
    obtain ⟨hdA1, hdA2, hdA3⟩ := hda n (by omega)
    -- t1 ← dsm_step_p t0 ta da
    step with (dsm_step_p_law t0 ta da A eA0 eA1 eA2 eA3 eA4 eA5 eA6 eA7 hlA
      hA0 hA1 hA2 hA3 hA4 hA5 hA6 hA7 t0bX t0bY t0bZ t0bT t0z t0t hct0
      (by clear * - hdA1 hdaq; omega)
      (by clear * - hdA2 hdaq; omega) (by clear * - hdA3 hdaq; omega)) as
      ⟨t1, t1bX, t1bY, t1bZ, t1bT, t1z, t1t, hct1, ht1⟩
    -- db ← b_naf[idx]
    step as ⟨db, hdbv⟩
    have hbbn : n < (↑b_naf : List Std.I8).length := by
      clear * - hle; scalar_tac
    have hdbq : db.val = nafDigit b_naf n := by
      rw [hdbv]
      simp only [nafDigit, hidxv, getElem!_pos (↑b_naf : List Std.I8) n hbbn]
    obtain ⟨hdB1, hdB2, hdB3⟩ := hdb n (by omega)
    -- t2 ← dsm_step_b t1 tb db
    step with (dsm_step_b_law t1 tb db B eB0 eB1 eB2 eB3 eB4 eB5 eB6 eB7 hlB
      hB0 hB1 hB2 hB3 hB4 hB5 hB6 hB7 t1bX t1bY t1bZ t1bT t1z t1t hct1
      (by clear * - hdB1 hdbq; omega) (by clear * - hdB2 hdbq; omega)
      (by clear * - hdB3 hdbq; omega)) as
      ⟨t2, t2bX, t2bY, t2bZ, t2bT, t2z, t2t, hct2, ht2⟩
    -- r1 ← t2.as_projective()
    step with (compl_as_projective_law t2 t2bX t2bY t2bZ t2bT t2z t2t) as
      ⟨r1, hr1v, hr1x, hr1y⟩
    have hcr1 : OnCurve (projX r1) (projY r1) := by
      rw [hr1x, hr1y]; exact hct2
    -- the digit chain: (projPt r1) = edDigit_B (edDigit_A (edAdd P P))
    have hchain : (projX r1, projY r1)
        = edDigit (edPt B) (nafDigit b_naf n)
            (edDigit (edPt A) (nafDigit a_naf n)
              (edAdd (projX r, projY r) (projX r, projY r))) := by
      have e1 : (complX t0, complY t0)
          = edAdd (projX r, projY r) (projX r, projY r) := by
        rw [Prod.ext_iff]; exact ⟨t0x, t0y⟩
      have e2 : (projX r1, projY r1) = (complX t2, complY t2) := by
        rw [Prod.ext_iff]; exact ⟨hr1x, hr1y⟩
      rw [e2, ht2, hdbq, ht1, hdaq, e1]
    try simp only [spec_ok]
    -- close with the induction hypothesis at counter idx (= n)
    apply spec_mono (ih idx r1 hidxv (by omega) hr1v hcr1)
    intro res ⟨hv', hc', heq⟩
    refine ⟨hv', hc', ?_⟩
    rw [heq, hchain, dsmFold_succ]

/-! ### The top-index constant and the public loop wrapper -/

/-- `dsm_top_index` is the constant 255 (leading zero digits are identity
    doublings — the source patch starts every walk at bit 255). -/
theorem dsm_top_index_spec (a b : Std.Array Std.I8 256#usize) :
    backend.serial.scalar_mul.vartime_double_base.dsm_top_index a b
      ⦃ r => r = 255#usize ⦄ := by
  unfold backend.serial.scalar_mul.vartime_double_base.dsm_top_index
  simp [spec_ok]

/-- **The full Straus loop**: from the identity, process all 256 digit
    positions — the result denotes `dsmFold … edId 256`. -/
theorem dsm_loop_spec (i : Usize) (hi : i.val = 255)
    (a_naf b_naf : Std.Array Std.I8 256#usize)
    (ta tb : window.NafLookupTable5 backend.serial.curve_models.ProjectiveNielsPoint)
    (A B : EdPoint)
    (hta : NafTableOf ta A) (htb : NafTableOf tb B)
    (hda : NafDigits a_naf) (hdb : NafDigits b_naf) :
    backend.serial.scalar_mul.vartime_double_base.dsm_loop
      i a_naf b_naf ta tb ⦃ res =>
        ProjValid res ∧ OnCurve (projX res) (projY res) ∧
        (projX res, projY res) = dsmFold (nafDigit a_naf) (nafDigit b_naf)
          (edPt A) (edPt B) edId 256 ⦄ := by
  obtain ⟨P0, hP0ok, hP0v, hP0x, hP0y⟩ := run_projective_identity
  unfold backend.serial.scalar_mul.vartime_double_base.dsm_loop
  rw [hP0ok]
  simp only [bind_tc_ok]
  have hcP0 : OnCurve (projX P0) (projY P0) := by
    rw [hP0x, hP0y]; exact onCurve_id
  -- j ← i + 1  (= 256)
  step as ⟨j, hj⟩
  have hjv : j.val = 256 := by clear * - hj hi; scalar_tac
  apply spec_mono (dsm_loop_loop_spec a_naf b_naf ta tb A B hta htb hda hdb
    256 j P0 hjv (by omega) hP0v hcP0)
  intro res ⟨hv, hc, heq⟩
  refine ⟨hv, hc, ?_⟩
  rw [heq, hP0x, hP0y]
  rfl

end CurveFieldProofs
