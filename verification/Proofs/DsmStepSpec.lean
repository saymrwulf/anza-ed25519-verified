/- ──────────────────────────────────────────────────────────────────────────────
   Proofs/DsmStepSpec.lean — double-scalar-mul campaign, brick 2:
   the per-digit step of the Straus/NAF loop.

   vartime_double_base's loop body is
       t = r.double();  t = dsm_step_p(t, table_a, a_naf[i]);
       t = dsm_step_b(t, table_b, b_naf[i]);  r = t.as_projective();
   This file proves the three non-loop ingredients as LAWS over the abstract
   Edwards addition (computational layering, no associativity):

   · `proj_double_law`      — ProjectivePoint::double denotes edAdd P P
                              (lift of the coordinate-level proj_double_spec,
                              same Z²-scaled linear_combination discipline as
                              edwards_double_law's Z⁴ one).
   · `compl_as_projective_law` — CompletedPoint::as_projective preserves the
                              denoted affine point ((X:Z),(Y:T)) ↦ (XT:YZ:ZT).
   · `naf_select_entry`     — select on a table with proven entries returns
                              THE entry for the digit: NafEntryOf r A ((x−1)/2).
   · `dsm_step_p_law`/`dsm_step_b_law` — the three-way digit step denotes
                              `edDigit`: add the (+d)-th odd multiple, add the
                              negation of the (−d)-th, or pass through.

   The digit hypotheses (odd-or-zero, |d| < 16) are exactly what the NAF
   digit spec will provide; they are taken as hypotheses here (layering).
   ────────────────────────────────────────────────────────────────────────────── -/
import Proofs.DsmTableSpec
open Aeneas Aeneas.Std Result ControlFlow
open curve25519

set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000

namespace CurveFieldProofs

open Aeneas.Std.WP

/-! ### Projective coordinate plumbing -/

/-- ⟪X⟫ = x·⟪Z⟫ for a projective point with ⟪Z⟫ ≠ 0 (x := projX). -/
theorem proj_X_eq (p : ProjPoint) (hZ0 : ⟪p.Z⟫ ≠ 0) : ⟪p.X⟫ = projX p * ⟪p.Z⟫ := by
  unfold projX
  field_simp

/-- ⟪Y⟫ = y·⟪Z⟫ for a projective point with ⟪Z⟫ ≠ 0 (y := projY). -/
theorem proj_Y_eq (p : ProjPoint) (hZ0 : ⟪p.Z⟫ ≠ 0) : ⟪p.Y⟫ = projY p * ⟪p.Z⟫ := by
  unfold projY
  field_simp

/-- **ProjectivePoint::double denotes the Edwards doubling law.**

    MATH: for a valid projective point P on the curve, `double` returns a
    completed point t with 2⁵⁴-bounded limbs, unit denominators, and
        (complX t, complY t) = edAdd (projX P, projY P) (projX P, projY P).
    Same derivation as `edwards_double_law` with Z² in place of Z⁴:
    the curve equation turns Y²−X² into Z²·(1+D) and 2Z²−(Y²−X²) into
    Z²·(1−D), both nonzero by completeness at the diagonal. -/
theorem proj_double_law (p : ProjPoint) (hp : ProjValid p)
    (hcp : OnCurve (projX p) (projY p)) :
    backend.serial.curve_models.ProjectivePoint.double p ⦃ t =>
      Bnd t.X (2^54) ∧ Bnd t.Y (2^54) ∧ Bnd t.Z (2^54) ∧ Bnd t.T (2^54) ∧
      ⟪t.Z⟫ ≠ 0 ∧ ⟪t.T⟫ ≠ 0 ∧
      complX t = (edAdd (projX p, projY p) (projX p, projY p)).1 ∧
      complY t = (edAdd (projX p, projY p) (projX p, projY p)).2 ⦄ := by
  apply spec_mono (proj_double_spec p hp)
  rintro t ⟨hbX, hbY, hbZ, hbT, hvX, hvY, hvZ, hvT⟩
  obtain ⟨-, -, -, hZ0⟩ := hp
  obtain ⟨hp1, hm1⟩ := completeness hcp hcp
  have hX := proj_X_eq p hZ0
  have hY := proj_Y_eq p hZ0
  have hZ2 : ⟪p.Z⟫^2 ≠ 0 := pow_ne_zero 2 hZ0
  -- the curve equation in doubling-friendly form
  have hcur : projY p ^ 2 - projX p ^ 2
      = 1 + edD * projX p * projX p * projY p * projY p := by
    have h := hcp
    unfold OnCurve at h
    linear_combination h
  -- the four coordinates, Z²-scaled
  have eX : ⟪t.X⟫ = ⟪p.Z⟫^2 * (projX p * projY p + projX p * projY p) := by
    rw [hvX, hX, hY]; ring
  have eY : ⟪t.Y⟫ = ⟪p.Z⟫^2 * (projY p * projY p + projX p * projX p) := by
    rw [hvY, hX, hY]; ring
  have eZ : ⟪t.Z⟫ = ⟪p.Z⟫^2 *
      (1 + edD * projX p * projX p * projY p * projY p) := by
    rw [hvZ, hX, hY]
    linear_combination ⟪p.Z⟫^2 * hcur
  have eT : ⟪t.T⟫ = ⟪p.Z⟫^2 *
      (1 - edD * projX p * projX p * projY p * projY p) := by
    rw [hvT, hX, hY]
    linear_combination (-(⟪p.Z⟫^2)) * hcur
  have hZne : ⟪t.Z⟫ ≠ 0 := by rw [eZ]; exact mul_ne_zero hZ2 hp1
  have hTne : ⟪t.T⟫ ≠ 0 := by rw [eT]; exact mul_ne_zero hZ2 hm1
  refine ⟨hbX.mono (by norm_num), hbY.mono (by norm_num),
          hbZ.mono (by norm_num), hbT.mono (by norm_num), hZne, hTne, ?_, ?_⟩
  · show ⟪t.X⟫ / ⟪t.Z⟫ = (projX p * projY p + projX p * projY p) /
      (1 + edD * projX p * projX p * projY p * projY p)
    rw [fp_div_eq_div_iff hZne hp1, eX, eZ]
    ring
  · show ⟪t.Y⟫ / ⟪t.T⟫ = (projY p * projY p + projX p * projX p) /
      (1 - edD * projX p * projX p * projY p * projY p)
    rw [fp_div_eq_div_iff hTne hm1, eY, eT]
    ring

/-- **CompletedPoint::as_projective preserves the denoted point.**

    MATH: ((X:Z),(Y:T)) ↦ (XT : YZ : ZT) — with ⟪Z⟫,⟪T⟫ ≠ 0 the new
    denominator ZT is a unit and XT/ZT = X/Z, YZ/ZT = Y/T. -/
theorem compl_as_projective_law (p : ComplPoint)
    (hbX : Bnd p.X (2^54)) (hbY : Bnd p.Y (2^54))
    (hbZ : Bnd p.Z (2^54)) (hbT : Bnd p.T (2^54))
    (hZ0 : ⟪p.Z⟫ ≠ 0) (hT0 : ⟪p.T⟫ ≠ 0) :
    backend.serial.curve_models.CompletedPoint.as_projective p ⦃ r =>
      ProjValid r ∧ projX r = complX p ∧ projY r = complY p ⦄ := by
  unfold backend.serial.curve_models.CompletedPoint.as_projective
  step with (mul_spec' _ _ hbX hbT) as ⟨fe, feb, fev⟩
  step with (mul_spec' _ _ hbY hbZ) as ⟨fe1, fe1b, fe1v⟩
  step with (mul_spec' _ _ hbZ hbT) as ⟨fe2, fe2b, fe2v⟩
  try simp only [spec_ok]
  refine ⟨⟨feb.mono (by norm_num), fe1b.mono (by norm_num),
           fe2b.mono (by norm_num), ?_⟩, ?_, ?_⟩
  · show ⟪fe2⟫ ≠ 0
    rw [fe2v]; exact mul_ne_zero hZ0 hT0
  · show ⟪fe⟫ / ⟪fe2⟫ = ⟪p.X⟫ / ⟪p.Z⟫
    rw [fev, fe2v, mul_div_mul_right _ _ hT0]
  · show ⟪fe1⟫ / ⟪fe2⟫ = ⟪p.Y⟫ / ⟪p.T⟫
    rw [fe1v, fe2v, mul_comm ⟪p.Z⟫ ⟪p.T⟫, mul_div_mul_right _ _ hZ0]

/-! ### Digit-indexed table lookup -/

/-- select on a table with proven entries returns THE entry for the digit:
    for odd x < 16, the result is a valid cache of the ((x−1)/2)-th odd
    multiple of A. -/
theorem naf_select_entry
    (tbl : window.NafLookupTable5 backend.serial.curve_models.ProjectiveNielsPoint)
    (x : Usize) (A : EdPoint)
    (e0 e1 e2 e3 e4 e5 e6 e7 : backend.serial.curve_models.ProjectiveNielsPoint)
    (hl : tblEntries tbl = [e0, e1, e2, e3, e4, e5, e6, e7])
    (h0 : NafEntryOf e0 A 0) (h1 : NafEntryOf e1 A 1) (h2 : NafEntryOf e2 A 2)
    (h3 : NafEntryOf e3 A 3) (h4 : NafEntryOf e4 A 4) (h5 : NafEntryOf e5 A 5)
    (h6 : NafEntryOf e6 A 6) (h7 : NafEntryOf e7 A 7)
    (hodd : x.val % 2 = 1) (hlt : x.val < 16) :
    window.NafLookupTable5.select
      backend.serial.curve_models.ProjectiveNielsPoint.Insts.CoreMarkerCopy tbl x
      ⦃ r => NafEntryOf r A ((x.val - 1) / 2) ⦄ := by
  apply spec_mono (naf_select_spec tbl x e0 e1 e2 e3 e4 e5 e6 e7 hl hodd hlt)
  rintro r ⟨i1, i3, i5, i7, i9, i11, i13, i15⟩
  have hx : x.val = 1 ∨ x.val = 3 ∨ x.val = 5 ∨ x.val = 7 ∨ x.val = 9 ∨
      x.val = 11 ∨ x.val = 13 ∨ x.val = 15 := by omega
  rcases hx with hx | hx | hx | hx | hx | hx | hx | hx
  · rw [i1 hx, hx]; exact h0
  · rw [i3 hx, hx]; exact h1
  · rw [i5 hx, hx]; exact h2
  · rw [i7 hx, hx]; exact h3
  · rw [i9 hx, hx]; exact h4
  · rw [i11 hx, hx]; exact h5
  · rw [i13 hx, hx]; exact h6
  · rw [i15 hx, hx]; exact h7

/-! ### The abstract digit step -/

/-- One NAF digit's action on the accumulator: add the d-th odd multiple of
    the base (d > 0), add its negation (d < 0), or pass through (d = 0) —
    over the abstract `edAdd`, no associativity. -/
noncomputable def edDigit (aPt : Fp × Fp) (d : ℤ) (P : Fp × Fp) : Fp × Fp :=
  if 0 < d then edAdd P (edOdd ((d.toNat - 1) / 2) aPt)
  else if d < 0 then edAdd P (edNeg (edOdd (((-d).toNat - 1) / 2) aPt))
  else P

/-- **The digit step denotes `edDigit`.**

    Given a bounded, unit-denominator completed accumulator t denoting an
    on-curve point, a table whose entries are proven caches of odd multiples
    of A, and a NAF digit (odd or zero, |d| < 16): `dsm_step_p` returns a
    completed point with the same validity shape denoting
    `edDigit (edPt A) d.val (complX t, complY t)`. The `select` masserts
    (panic freedom) are discharged, not assumed. -/
theorem dsm_step_p_law (t : ComplPoint)
    (tbl : window.NafLookupTable5 backend.serial.curve_models.ProjectiveNielsPoint)
    (d : Std.I8) (A : EdPoint)
    (e0 e1 e2 e3 e4 e5 e6 e7 : backend.serial.curve_models.ProjectiveNielsPoint)
    (hl : tblEntries tbl = [e0, e1, e2, e3, e4, e5, e6, e7])
    (h0 : NafEntryOf e0 A 0) (h1 : NafEntryOf e1 A 1) (h2 : NafEntryOf e2 A 2)
    (h3 : NafEntryOf e3 A 3) (h4 : NafEntryOf e4 A 4) (h5 : NafEntryOf e5 A 5)
    (h6 : NafEntryOf e6 A 6) (h7 : NafEntryOf e7 A 7)
    (hbX : Bnd t.X (2^54)) (hbY : Bnd t.Y (2^54))
    (hbZ : Bnd t.Z (2^54)) (hbT : Bnd t.T (2^54))
    (hZ0 : ⟪t.Z⟫ ≠ 0) (hT0 : ⟪t.T⟫ ≠ 0)
    (hct : OnCurve (complX t) (complY t))
    (hd : d.val = 0 ∨ d.val % 2 = 1) (hdlo : -16 < d.val) (hdhi : d.val < 16) :
    backend.serial.scalar_mul.vartime_double_base.dsm_step_p t tbl d ⦃ r =>
      Bnd r.X (2^54) ∧ Bnd r.Y (2^54) ∧ Bnd r.Z (2^54) ∧ Bnd r.T (2^54) ∧
      ⟪r.Z⟫ ≠ 0 ∧ ⟪r.T⟫ ≠ 0 ∧
      OnCurve (complX r) (complY r) ∧
      (complX r, complY r) = edDigit (edPt A) d.val (complX t, complY t) ⦄ := by
  unfold backend.serial.scalar_mul.vartime_double_base.dsm_step_p
  split
  · -- d > 0: add the d-th odd multiple
    rename_i hdpos
    have hdposv : (0:ℤ) < d.val := by clear * - hdpos; scalar_tac
    -- ep ← t.as_extended
    step with (compl_as_extended_law t hbX hbY hbZ hbT hZ0 hT0) as ⟨ep, hepv, hepx, hepy⟩
    have hepc : OnCurveExt ep := by
      show OnCurve (edX ep) (edY ep)
      rw [hepx, hepy]; exact hct
    have hept : edPt ep = (complX t, complY t) := by
      calc edPt ep = (edX ep, edY ep) := rfl
        _ = (complX t, complY t) := by rw [hepx, hepy]
    -- i ← d as usize  (in-bounds: 0 < d < 16)
    step with (IScalar.hcast_inBounds_spec .Usize d
      (by clear * - hdposv hdhi; scalar_tac)) as ⟨i, hi⟩
    have hiv : i.val = d.val.toNat := by clear * - hi hdposv; omega
    have hiodd : i.val % 2 = 1 := by clear * - hiv hd hdposv; omega
    have hilt : i.val < 16 := by clear * - hiv hdhi hdposv; omega
    -- pnp ← select tbl i  (the ((i−1)/2)-th odd multiple's cache)
    step with (naf_select_entry tbl i A e0 e1 e2 e3 e4 e5 e6 e7 hl
      h0 h1 h2 h3 h4 h5 h6 h7 hiodd hilt) as ⟨pnp, hpnp⟩
    obtain ⟨hpv, Q, hpn, hQv, hQc, hQpt⟩ := hpnp
    -- r ← ep + pnp  (the mixed-add kernel law)
    apply spec_mono (add_projniels_law ep pnp hpn hepv hQv hepc hQc hpv)
    rintro r ⟨rbX, rbY, rbZ, rbT, rz, rt, rx, ry⟩
    have hcr : OnCurve (complX r) (complY r) := by
      rw [rx, ry]
      exact edAdd_closure (show OnCurve (edX ep) (edY ep) from hepc)
        (show OnCurve (edX Q) (edY Q) from hQc)
    refine ⟨rbX.mono (by norm_num), rbY.mono (by norm_num), rbZ,
            rbT.mono (by norm_num), rz, rt, hcr, ?_⟩
    have hk : (i.val - 1) / 2 = (d.val.toNat - 1) / 2 := by
      clear * - hiv; omega
    simp only [edDigit, if_pos hdposv]
    calc (complX r, complY r)
        = ((edAdd (edPt ep) (edPt Q)).1, (edAdd (edPt ep) (edPt Q)).2) := by
          rw [rx, ry]
      _ = edAdd (edPt ep) (edPt Q) := rfl
      _ = edAdd (complX t, complY t) (edOdd ((d.val.toNat - 1) / 2) (edPt A)) := by
          rw [hept, hQpt, hk]
  · -- d < 0 or d = 0
    split
    · -- d < 0: add the negation of the (−d)-th odd multiple
      rename_i hdneg
      have hdnegv : d.val < 0 := by clear * - hdneg; scalar_tac
      -- ep ← t.as_extended
      step with (compl_as_extended_law t hbX hbY hbZ hbT hZ0 hT0) as ⟨ep, hepv, hepx, hepy⟩
      have hepc : OnCurveExt ep := by
        show OnCurve (edX ep) (edY ep)
        rw [hepx, hepy]; exact hct
      have hept : edPt ep = (complX t, complY t) := by
        calc edPt ep = (edX ep, edY ep) := rfl
          _ = (complX t, complY t) := by rw [hepx, hepy]
      -- i ← −d;  i1 ← i as usize
      step as ⟨i, hi⟩
      have hiv : i.val = -d.val := by clear * - hi hdnegv hdlo; scalar_tac
      step with (IScalar.hcast_inBounds_spec .Usize i
        (by clear * - hiv hdnegv hdlo; scalar_tac)) as ⟨i1, hi1⟩
      have hi1v : i1.val = (-d.val).toNat := by clear * - hi1 hiv hdnegv; omega
      have hiodd : i1.val % 2 = 1 := by clear * - hi1v hd hdnegv; omega
      have hilt : i1.val < 16 := by clear * - hi1v hdlo hdnegv; omega
      -- pnp ← select tbl i1
      step with (naf_select_entry tbl i1 A e0 e1 e2 e3 e4 e5 e6 e7 hl
        h0 h1 h2 h3 h4 h5 h6 h7 hiodd hilt) as ⟨pnp, hpnp⟩
      obtain ⟨hpv, Q, hpn, hQv, hQc, hQpt⟩ := hpnp
      -- r ← ep − pnp  (the mixed-sub kernel law)
      apply spec_mono (sub_projniels_law ep pnp hpn hepv hQv hepc hQc hpv)
      rintro r ⟨rbX, rbY, rbZ, rbT, rz, rt, rx, ry⟩
      have hcr : OnCurve (complX r) (complY r) := by
        rw [rx, ry]
        exact edAdd_closure (show OnCurve (edX ep) (edY ep) from hepc)
          (onCurve_neg (show OnCurve (edX Q) (edY Q) from hQc))
      refine ⟨rbX.mono (by norm_num), rbY.mono (by norm_num),
              rbZ.mono (by norm_num), rbT, rz, rt, hcr, ?_⟩
      have hk : (i1.val - 1) / 2 = ((-d.val).toNat - 1) / 2 := by
        clear * - hi1v; omega
      have hnpos : ¬ ((0:ℤ) < d.val) := by clear * - hdnegv; omega
      simp only [edDigit, if_neg hnpos, if_pos hdnegv]
      calc (complX r, complY r)
          = ((edAdd (edPt ep) (edNeg (edPt Q))).1,
             (edAdd (edPt ep) (edNeg (edPt Q))).2) := by
            rw [rx, ry]
        _ = edAdd (edPt ep) (edNeg (edPt Q)) := rfl
        _ = edAdd (complX t, complY t)
              (edNeg (edOdd (((-d.val).toNat - 1) / 2) (edPt A))) := by
            rw [hept, hQpt, hk]
    · -- d = 0: pass through
      rename_i hnpos hnneg
      have h0v : d.val = 0 := by clear * - hnpos hnneg; scalar_tac
      try simp only [spec_ok]
      have hzero : ¬ ((0:ℤ) < d.val) ∧ ¬ (d.val < 0) := by
        clear * - h0v; omega
      refine ⟨hbX, hbY, hbZ, hbT, hZ0, hT0, hct, ?_⟩
      simp only [edDigit, if_neg hzero.1, if_neg hzero.2]

/-- `dsm_step_b` delegates to `dsm_step_p` (both tables are runtime
    `NafLookupTable5<ProjectiveNielsPoint>` in this extraction). -/
theorem dsm_step_b_law (t : ComplPoint)
    (tbl : window.NafLookupTable5 backend.serial.curve_models.ProjectiveNielsPoint)
    (d : Std.I8) (A : EdPoint)
    (e0 e1 e2 e3 e4 e5 e6 e7 : backend.serial.curve_models.ProjectiveNielsPoint)
    (hl : tblEntries tbl = [e0, e1, e2, e3, e4, e5, e6, e7])
    (h0 : NafEntryOf e0 A 0) (h1 : NafEntryOf e1 A 1) (h2 : NafEntryOf e2 A 2)
    (h3 : NafEntryOf e3 A 3) (h4 : NafEntryOf e4 A 4) (h5 : NafEntryOf e5 A 5)
    (h6 : NafEntryOf e6 A 6) (h7 : NafEntryOf e7 A 7)
    (hbX : Bnd t.X (2^54)) (hbY : Bnd t.Y (2^54))
    (hbZ : Bnd t.Z (2^54)) (hbT : Bnd t.T (2^54))
    (hZ0 : ⟪t.Z⟫ ≠ 0) (hT0 : ⟪t.T⟫ ≠ 0)
    (hct : OnCurve (complX t) (complY t))
    (hd : d.val = 0 ∨ d.val % 2 = 1) (hdlo : -16 < d.val) (hdhi : d.val < 16) :
    backend.serial.scalar_mul.vartime_double_base.dsm_step_b t tbl d ⦃ r =>
      Bnd r.X (2^54) ∧ Bnd r.Y (2^54) ∧ Bnd r.Z (2^54) ∧ Bnd r.T (2^54) ∧
      ⟪r.Z⟫ ≠ 0 ∧ ⟪r.T⟫ ≠ 0 ∧
      OnCurve (complX r) (complY r) ∧
      (complX r, complY r) = edDigit (edPt A) d.val (complX t, complY t) ⦄ := by
  unfold backend.serial.scalar_mul.vartime_double_base.dsm_step_b
  exact dsm_step_p_law t tbl d A e0 e1 e2 e3 e4 e5 e6 e7 hl
    h0 h1 h2 h3 h4 h5 h6 h7 hbX hbY hbZ hbT hZ0 hT0 hct hd hdlo hdhi

end CurveFieldProofs
