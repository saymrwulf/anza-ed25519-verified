/- ──────────────────────────────────────────────────────────────────────────────
   Proofs/DsmTableSpec.lean — double-scalar-mul campaign, brick 1:
   the NAF lookup-table construction  `NafLookupTable5::from(&A)`.

   window.rs builds the odd-multiples table  [A, 3A, 5A, 7A, 9A, 11A, 13A, 15A]
   (as ProjectiveNielsPoint caches):
       Ai[0] = A.as_projective_niels();  A2 = A.double();
       for i in 0..7 { Ai[i+1] = (A2 + Ai[i]).as_extended().as_projective_niels() }

   SPEC (relational, computational layering — no associativity assumed):
   entry k is a VALID niels cache of a valid on-curve point Q_k with
       edPt Q_k = edOdd k (edPt A)
   where `edOdd` is the abstract double-and-add recursion
       edOdd 0 p = p,   edOdd (k+1) p = edAdd (edAdd p p) (edOdd k p)
   — i.e. exactly the (2k+1)-fold sum the code computes, expressed over the
   proven abstract Edwards addition `edAdd` (EdCurve). Composes the proven
   group-layer laws: edwards_as_projective_niels_spec, edwards_double_law,
   add_projniels_law, compl_as_extended_law (EdMain / EdConvert).

   Loop-peel machinery (loop_step / range_next_*_spec) is the field layer's
   (AddSpec.lean, same namespace) — this file imports only the CurveField
   extraction tree.
   ────────────────────────────────────────────────────────────────────────────── -/
import Proofs.EdMain
open Aeneas Aeneas.Std Result ControlFlow
open curve25519

set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000

namespace CurveFieldProofs

open Aeneas.Std.WP

/- Loop-peel machinery (loop_step / range_next_*_spec) comes from the
   field layer's AddSpec.lean — already in this namespace via Proofs.EdMain. -/

/-! ### The abstract odd-multiple recursion -/

/-- `edOdd k p` is the double-and-add recursion the table loop computes:
    p, then 2p+p, 2p+(3p), … — abstractly, the (2k+1)-th odd multiple,
    expressed over `edAdd` WITHOUT assuming associativity (computational
    layering; the group-semantics reading is phase 2 of the campaign). -/
noncomputable def edOdd : ℕ → Fp × Fp → Fp × Fp
  | 0, p => p
  | k + 1, p => edAdd (edAdd p p) (edOdd k p)

@[simp] theorem edOdd_zero (p : Fp × Fp) : edOdd 0 p = p := rfl

theorem edOdd_succ (k : ℕ) (p : Fp × Fp) :
    edOdd (k + 1) p = edAdd (edAdd p p) (edOdd k p) := rfl

/-- Entry contract of the NAF table: a valid niels cache of a valid,
    on-curve point denoting the k-th odd multiple of A. -/
def NafEntryOf (e : backend.serial.curve_models.ProjectiveNielsPoint) (A : EdPoint) (k : ℕ) : Prop :=
  ProjNielsValid e ∧ ∃ Q : EdPoint, IsNielsOf e Q ∧ ExtValid Q ∧
    OnCurveExt Q ∧ edPt Q = edOdd k (edPt A)

/-- The entry list of a `NafLookupTable5` (the type is a transparent
    synonym for `Array ProjectiveNielsPoint 8`). -/
def tblEntries
    (tbl : window.NafLookupTable5 backend.serial.curve_models.ProjectiveNielsPoint) : List backend.serial.curve_models.ProjectiveNielsPoint :=
  Subtype.val (tbl : Std.Array backend.serial.curve_models.ProjectiveNielsPoint 8#usize)

/-! ### The table-construction loop: 7 concrete peels -/

/-- The `from` loop: starting from `[cache(A)]*8`, after 7 iterations entry k
    holds a valid cache of the k-th odd multiple, for every k ≤ 7. -/
theorem naf_table_loop_spec (A A2 : EdPoint)
    (Ai : Std.Array backend.serial.curve_models.ProjectiveNielsPoint 8#usize) (n0 : backend.serial.curve_models.ProjectiveNielsPoint)
    (hl0 : (↑Ai : List backend.serial.curve_models.ProjectiveNielsPoint) = [n0, n0, n0, n0, n0, n0, n0, n0])
    (hn0v : ProjNielsValid n0) (hn0n : IsNielsOf n0 A)
    (hAv : ExtValid A) (hAc : OnCurveExt A)
    (hA2v : ExtValid A2) (hA2c : OnCurveExt A2)
    (hA2pt : edPt A2 = edAdd (edPt A) (edPt A)) :
    window.NafLookupTable5ProjectiveNielsPoint.Insts.CoreConvertFromSharedAEdwardsPoint.from_loop
      { start := 0#usize, «end» := 7#usize } Ai A2
      ⦃ arr => ∃ e0 e1 e2 e3 e4 e5 e6 e7,
          (↑arr : List backend.serial.curve_models.ProjectiveNielsPoint) = [e0, e1, e2, e3, e4, e5, e6, e7] ∧
          NafEntryOf e0 A 0 ∧ NafEntryOf e1 A 1 ∧ NafEntryOf e2 A 2 ∧
          NafEntryOf e3 A 3 ∧ NafEntryOf e4 A 4 ∧ NafEntryOf e5 A 5 ∧
          NafEntryOf e6 A 6 ∧ NafEntryOf e7 A 7 ⦄ := by
  have hq0pt : edPt A = edOdd 0 (edPt A) := rfl
  unfold window.NafLookupTable5ProjectiveNielsPoint.Insts.CoreConvertFromSharedAEdwardsPoint.from_loop
  -- ── iteration 0: read entry 0 (cache of q0), write entry 1 = cache of 2A + q0
  apply loop_step
  simp only [window.NafLookupTable5ProjectiveNielsPoint.Insts.CoreConvertFromSharedAEdwardsPoint.from_loop.body]
  step with range_next_lt_spec as ⟨o0, iter0, ho0, hs0, he0⟩
  simp only [ho0]
  have hsv0 : iter0.start.val = 1 := by clear * - hs0; omega
  have hev0 : iter0.«end».val = 7 := by clear * - he0; scalar_tac
  -- entry 0 out of the array
  step as ⟨e0x, he0x⟩
  simp [hl0] at he0x
  rw [he0x]
  -- cp ← A2 + n0   (the mixed-add kernel law)
  step with (add_projniels_law A2 n0 hn0n hA2v hAv hA2c hAc hn0v) as
    ⟨cp0, cb0X, cb0Y, cb0Z, cb0T, cz0, ct0, cx0, cy0⟩
  -- q1 ← cp.as_extended   (valid extended point denoting the sum)
  step with (compl_as_extended_law cp0 (cb0X.mono (by norm_num))
    (cb0Y.mono (by norm_num)) cb0Z (cb0T.mono (by norm_num)) cz0 ct0) as
    ⟨q1, hq1v, hq1x, hq1y⟩
  have hq1c : OnCurveExt q1 := by
    show OnCurve (edX q1) (edY q1)
    rw [hq1x, cx0, hq1y, cy0]
    exact edAdd_closure (show OnCurve (edX A2) (edY A2) from hA2c)
      (show OnCurve (edX A) (edY A) from hAc)
  have hq1pt : edPt q1 = edOdd 1 (edPt A) := by
    have h : edPt q1 = edAdd (edPt A2) (edPt A) := by
      calc edPt q1 = (edX q1, edY q1) := rfl
        _ = ((edAdd (edPt A2) (edPt A)).1, (edAdd (edPt A2) (edPt A)).2) := by
            rw [hq1x, cx0, hq1y, cy0]
        _ = edAdd (edPt A2) (edPt A) := rfl
    rw [h, hA2pt, hq0pt]
    rfl
  -- n1 ← q1.as_projective_niels   (the new table entry)
  step with (edwards_as_projective_niels_spec q1 hq1v) as ⟨n1, hn1v, hn1n⟩
  -- write it at index 1
  step as ⟨j0, hj0⟩
  have hj0v : j0 = 1#usize := by clear * - hj0; scalar_tac
  rw [hj0v]
  step as ⟨Ai1, hA1⟩
  have hl1 : (↑Ai1 : List backend.serial.curve_models.ProjectiveNielsPoint)
      = [n0, n1, n0, n0, n0, n0, n0, n0] := by
    simp only [hA1, Array.set_val_eq, hl0]
    rfl
  try simp only [spec_ok]
  -- ── iteration 1: read entry 1 (cache of q1), write entry 2 = cache of 2A + q1
  apply loop_step
  simp only [window.NafLookupTable5ProjectiveNielsPoint.Insts.CoreConvertFromSharedAEdwardsPoint.from_loop.body]
  step with (range_next_lt_spec iter0 (by clear * - hsv0 hev0; scalar_tac)) as ⟨o1, iter1, ho1, hs1, he1⟩
  simp only [ho1]
  have hsv1 : iter1.start.val = 2 := by clear * - hs1 hsv0; omega
  have hev1 : iter1.«end».val = 7 := by clear * - he1 hev0; scalar_tac
  have hidx1 : iter0.start = 1#usize := by clear * - hsv0; scalar_tac
  rw [hidx1]
  -- entry 1 out of the array
  step as ⟨e1x, he1x⟩
  simp [hl1] at he1x
  rw [he1x]
  -- cp ← A2 + n1   (the mixed-add kernel law)
  step with (add_projniels_law A2 n1 hn1n hA2v hq1v hA2c hq1c hn1v) as
    ⟨cp1, cb1X, cb1Y, cb1Z, cb1T, cz1, ct1, cx1, cy1⟩
  -- q2 ← cp.as_extended   (valid extended point denoting the sum)
  step with (compl_as_extended_law cp1 (cb1X.mono (by norm_num))
    (cb1Y.mono (by norm_num)) cb1Z (cb1T.mono (by norm_num)) cz1 ct1) as
    ⟨q2, hq2v, hq2x, hq2y⟩
  have hq2c : OnCurveExt q2 := by
    show OnCurve (edX q2) (edY q2)
    rw [hq2x, cx1, hq2y, cy1]
    exact edAdd_closure (show OnCurve (edX A2) (edY A2) from hA2c)
      (show OnCurve (edX q1) (edY q1) from hq1c)
  have hq2pt : edPt q2 = edOdd 2 (edPt A) := by
    have h : edPt q2 = edAdd (edPt A2) (edPt q1) := by
      calc edPt q2 = (edX q2, edY q2) := rfl
        _ = ((edAdd (edPt A2) (edPt q1)).1, (edAdd (edPt A2) (edPt q1)).2) := by
            rw [hq2x, cx1, hq2y, cy1]
        _ = edAdd (edPt A2) (edPt q1) := rfl
    rw [h, hA2pt, hq1pt]
    rfl
  -- n2 ← q2.as_projective_niels   (the new table entry)
  step with (edwards_as_projective_niels_spec q2 hq2v) as ⟨n2, hn2v, hn2n⟩
  -- write it at index 2
  step as ⟨j1, hj1⟩
  have hj1v : j1 = 2#usize := by clear * - hj1; scalar_tac
  rw [hj1v]
  step as ⟨Ai2, hA2⟩
  have hl2 : (↑Ai2 : List backend.serial.curve_models.ProjectiveNielsPoint)
      = [n0, n1, n2, n0, n0, n0, n0, n0] := by
    simp only [hA2, Array.set_val_eq, hl1]
    rfl
  try simp only [spec_ok]
  -- ── iteration 2: read entry 2 (cache of q2), write entry 3 = cache of 2A + q2
  apply loop_step
  simp only [window.NafLookupTable5ProjectiveNielsPoint.Insts.CoreConvertFromSharedAEdwardsPoint.from_loop.body]
  step with (range_next_lt_spec iter1 (by clear * - hsv1 hev1; scalar_tac)) as ⟨o2, iter2, ho2, hs2, he2⟩
  simp only [ho2]
  have hsv2 : iter2.start.val = 3 := by clear * - hs2 hsv1; omega
  have hev2 : iter2.«end».val = 7 := by clear * - he2 hev1; scalar_tac
  have hidx2 : iter1.start = 2#usize := by clear * - hsv1; scalar_tac
  rw [hidx2]
  -- entry 2 out of the array
  step as ⟨e2x, he2x⟩
  simp [hl2] at he2x
  rw [he2x]
  -- cp ← A2 + n2   (the mixed-add kernel law)
  step with (add_projniels_law A2 n2 hn2n hA2v hq2v hA2c hq2c hn2v) as
    ⟨cp2, cb2X, cb2Y, cb2Z, cb2T, cz2, ct2, cx2, cy2⟩
  -- q3 ← cp.as_extended   (valid extended point denoting the sum)
  step with (compl_as_extended_law cp2 (cb2X.mono (by norm_num))
    (cb2Y.mono (by norm_num)) cb2Z (cb2T.mono (by norm_num)) cz2 ct2) as
    ⟨q3, hq3v, hq3x, hq3y⟩
  have hq3c : OnCurveExt q3 := by
    show OnCurve (edX q3) (edY q3)
    rw [hq3x, cx2, hq3y, cy2]
    exact edAdd_closure (show OnCurve (edX A2) (edY A2) from hA2c)
      (show OnCurve (edX q2) (edY q2) from hq2c)
  have hq3pt : edPt q3 = edOdd 3 (edPt A) := by
    have h : edPt q3 = edAdd (edPt A2) (edPt q2) := by
      calc edPt q3 = (edX q3, edY q3) := rfl
        _ = ((edAdd (edPt A2) (edPt q2)).1, (edAdd (edPt A2) (edPt q2)).2) := by
            rw [hq3x, cx2, hq3y, cy2]
        _ = edAdd (edPt A2) (edPt q2) := rfl
    rw [h, hA2pt, hq2pt]
    rfl
  -- n3 ← q3.as_projective_niels   (the new table entry)
  step with (edwards_as_projective_niels_spec q3 hq3v) as ⟨n3, hn3v, hn3n⟩
  -- write it at index 3
  step as ⟨j2, hj2⟩
  have hj2v : j2 = 3#usize := by clear * - hj2; scalar_tac
  rw [hj2v]
  step as ⟨Ai3, hA3⟩
  have hl3 : (↑Ai3 : List backend.serial.curve_models.ProjectiveNielsPoint)
      = [n0, n1, n2, n3, n0, n0, n0, n0] := by
    simp only [hA3, Array.set_val_eq, hl2]
    rfl
  try simp only [spec_ok]
  -- ── iteration 3: read entry 3 (cache of q3), write entry 4 = cache of 2A + q3
  apply loop_step
  simp only [window.NafLookupTable5ProjectiveNielsPoint.Insts.CoreConvertFromSharedAEdwardsPoint.from_loop.body]
  step with (range_next_lt_spec iter2 (by clear * - hsv2 hev2; scalar_tac)) as ⟨o3, iter3, ho3, hs3, he3⟩
  simp only [ho3]
  have hsv3 : iter3.start.val = 4 := by clear * - hs3 hsv2; omega
  have hev3 : iter3.«end».val = 7 := by clear * - he3 hev2; scalar_tac
  have hidx3 : iter2.start = 3#usize := by clear * - hsv2; scalar_tac
  rw [hidx3]
  -- entry 3 out of the array
  step as ⟨e3x, he3x⟩
  simp [hl3] at he3x
  rw [he3x]
  -- cp ← A2 + n3   (the mixed-add kernel law)
  step with (add_projniels_law A2 n3 hn3n hA2v hq3v hA2c hq3c hn3v) as
    ⟨cp3, cb3X, cb3Y, cb3Z, cb3T, cz3, ct3, cx3, cy3⟩
  -- q4 ← cp.as_extended   (valid extended point denoting the sum)
  step with (compl_as_extended_law cp3 (cb3X.mono (by norm_num))
    (cb3Y.mono (by norm_num)) cb3Z (cb3T.mono (by norm_num)) cz3 ct3) as
    ⟨q4, hq4v, hq4x, hq4y⟩
  have hq4c : OnCurveExt q4 := by
    show OnCurve (edX q4) (edY q4)
    rw [hq4x, cx3, hq4y, cy3]
    exact edAdd_closure (show OnCurve (edX A2) (edY A2) from hA2c)
      (show OnCurve (edX q3) (edY q3) from hq3c)
  have hq4pt : edPt q4 = edOdd 4 (edPt A) := by
    have h : edPt q4 = edAdd (edPt A2) (edPt q3) := by
      calc edPt q4 = (edX q4, edY q4) := rfl
        _ = ((edAdd (edPt A2) (edPt q3)).1, (edAdd (edPt A2) (edPt q3)).2) := by
            rw [hq4x, cx3, hq4y, cy3]
        _ = edAdd (edPt A2) (edPt q3) := rfl
    rw [h, hA2pt, hq3pt]
    rfl
  -- n4 ← q4.as_projective_niels   (the new table entry)
  step with (edwards_as_projective_niels_spec q4 hq4v) as ⟨n4, hn4v, hn4n⟩
  -- write it at index 4
  step as ⟨j3, hj3⟩
  have hj3v : j3 = 4#usize := by clear * - hj3; scalar_tac
  rw [hj3v]
  step as ⟨Ai4, hA4⟩
  have hl4 : (↑Ai4 : List backend.serial.curve_models.ProjectiveNielsPoint)
      = [n0, n1, n2, n3, n4, n0, n0, n0] := by
    simp only [hA4, Array.set_val_eq, hl3]
    rfl
  try simp only [spec_ok]
  -- ── iteration 4: read entry 4 (cache of q4), write entry 5 = cache of 2A + q4
  apply loop_step
  simp only [window.NafLookupTable5ProjectiveNielsPoint.Insts.CoreConvertFromSharedAEdwardsPoint.from_loop.body]
  step with (range_next_lt_spec iter3 (by clear * - hsv3 hev3; scalar_tac)) as ⟨o4, iter4, ho4, hs4, he4⟩
  simp only [ho4]
  have hsv4 : iter4.start.val = 5 := by clear * - hs4 hsv3; omega
  have hev4 : iter4.«end».val = 7 := by clear * - he4 hev3; scalar_tac
  have hidx4 : iter3.start = 4#usize := by clear * - hsv3; scalar_tac
  rw [hidx4]
  -- entry 4 out of the array
  step as ⟨e4x, he4x⟩
  simp [hl4] at he4x
  rw [he4x]
  -- cp ← A2 + n4   (the mixed-add kernel law)
  step with (add_projniels_law A2 n4 hn4n hA2v hq4v hA2c hq4c hn4v) as
    ⟨cp4, cb4X, cb4Y, cb4Z, cb4T, cz4, ct4, cx4, cy4⟩
  -- q5 ← cp.as_extended   (valid extended point denoting the sum)
  step with (compl_as_extended_law cp4 (cb4X.mono (by norm_num))
    (cb4Y.mono (by norm_num)) cb4Z (cb4T.mono (by norm_num)) cz4 ct4) as
    ⟨q5, hq5v, hq5x, hq5y⟩
  have hq5c : OnCurveExt q5 := by
    show OnCurve (edX q5) (edY q5)
    rw [hq5x, cx4, hq5y, cy4]
    exact edAdd_closure (show OnCurve (edX A2) (edY A2) from hA2c)
      (show OnCurve (edX q4) (edY q4) from hq4c)
  have hq5pt : edPt q5 = edOdd 5 (edPt A) := by
    have h : edPt q5 = edAdd (edPt A2) (edPt q4) := by
      calc edPt q5 = (edX q5, edY q5) := rfl
        _ = ((edAdd (edPt A2) (edPt q4)).1, (edAdd (edPt A2) (edPt q4)).2) := by
            rw [hq5x, cx4, hq5y, cy4]
        _ = edAdd (edPt A2) (edPt q4) := rfl
    rw [h, hA2pt, hq4pt]
    rfl
  -- n5 ← q5.as_projective_niels   (the new table entry)
  step with (edwards_as_projective_niels_spec q5 hq5v) as ⟨n5, hn5v, hn5n⟩
  -- write it at index 5
  step as ⟨j4, hj4⟩
  have hj4v : j4 = 5#usize := by clear * - hj4; scalar_tac
  rw [hj4v]
  step as ⟨Ai5, hA5⟩
  have hl5 : (↑Ai5 : List backend.serial.curve_models.ProjectiveNielsPoint)
      = [n0, n1, n2, n3, n4, n5, n0, n0] := by
    simp only [hA5, Array.set_val_eq, hl4]
    rfl
  try simp only [spec_ok]
  -- ── iteration 5: read entry 5 (cache of q5), write entry 6 = cache of 2A + q5
  apply loop_step
  simp only [window.NafLookupTable5ProjectiveNielsPoint.Insts.CoreConvertFromSharedAEdwardsPoint.from_loop.body]
  step with (range_next_lt_spec iter4 (by clear * - hsv4 hev4; scalar_tac)) as ⟨o5, iter5, ho5, hs5, he5⟩
  simp only [ho5]
  have hsv5 : iter5.start.val = 6 := by clear * - hs5 hsv4; omega
  have hev5 : iter5.«end».val = 7 := by clear * - he5 hev4; scalar_tac
  have hidx5 : iter4.start = 5#usize := by clear * - hsv4; scalar_tac
  rw [hidx5]
  -- entry 5 out of the array
  step as ⟨e5x, he5x⟩
  simp [hl5] at he5x
  rw [he5x]
  -- cp ← A2 + n5   (the mixed-add kernel law)
  step with (add_projniels_law A2 n5 hn5n hA2v hq5v hA2c hq5c hn5v) as
    ⟨cp5, cb5X, cb5Y, cb5Z, cb5T, cz5, ct5, cx5, cy5⟩
  -- q6 ← cp.as_extended   (valid extended point denoting the sum)
  step with (compl_as_extended_law cp5 (cb5X.mono (by norm_num))
    (cb5Y.mono (by norm_num)) cb5Z (cb5T.mono (by norm_num)) cz5 ct5) as
    ⟨q6, hq6v, hq6x, hq6y⟩
  have hq6c : OnCurveExt q6 := by
    show OnCurve (edX q6) (edY q6)
    rw [hq6x, cx5, hq6y, cy5]
    exact edAdd_closure (show OnCurve (edX A2) (edY A2) from hA2c)
      (show OnCurve (edX q5) (edY q5) from hq5c)
  have hq6pt : edPt q6 = edOdd 6 (edPt A) := by
    have h : edPt q6 = edAdd (edPt A2) (edPt q5) := by
      calc edPt q6 = (edX q6, edY q6) := rfl
        _ = ((edAdd (edPt A2) (edPt q5)).1, (edAdd (edPt A2) (edPt q5)).2) := by
            rw [hq6x, cx5, hq6y, cy5]
        _ = edAdd (edPt A2) (edPt q5) := rfl
    rw [h, hA2pt, hq5pt]
    rfl
  -- n6 ← q6.as_projective_niels   (the new table entry)
  step with (edwards_as_projective_niels_spec q6 hq6v) as ⟨n6, hn6v, hn6n⟩
  -- write it at index 6
  step as ⟨j5, hj5⟩
  have hj5v : j5 = 6#usize := by clear * - hj5; scalar_tac
  rw [hj5v]
  step as ⟨Ai6, hA6⟩
  have hl6 : (↑Ai6 : List backend.serial.curve_models.ProjectiveNielsPoint)
      = [n0, n1, n2, n3, n4, n5, n6, n0] := by
    simp only [hA6, Array.set_val_eq, hl5]
    rfl
  try simp only [spec_ok]
  -- ── iteration 6: read entry 6 (cache of q6), write entry 7 = cache of 2A + q6
  apply loop_step
  simp only [window.NafLookupTable5ProjectiveNielsPoint.Insts.CoreConvertFromSharedAEdwardsPoint.from_loop.body]
  step with (range_next_lt_spec iter5 (by clear * - hsv5 hev5; scalar_tac)) as ⟨o6, iter6, ho6, hs6, he6⟩
  simp only [ho6]
  have hsv6 : iter6.start.val = 7 := by clear * - hs6 hsv5; omega
  have hev6 : iter6.«end».val = 7 := by clear * - he6 hev5; scalar_tac
  have hidx6 : iter5.start = 6#usize := by clear * - hsv5; scalar_tac
  rw [hidx6]
  -- entry 6 out of the array
  step as ⟨e6x, he6x⟩
  simp [hl6] at he6x
  rw [he6x]
  -- cp ← A2 + n6   (the mixed-add kernel law)
  step with (add_projniels_law A2 n6 hn6n hA2v hq6v hA2c hq6c hn6v) as
    ⟨cp6, cb6X, cb6Y, cb6Z, cb6T, cz6, ct6, cx6, cy6⟩
  -- q7 ← cp.as_extended   (valid extended point denoting the sum)
  step with (compl_as_extended_law cp6 (cb6X.mono (by norm_num))
    (cb6Y.mono (by norm_num)) cb6Z (cb6T.mono (by norm_num)) cz6 ct6) as
    ⟨q7, hq7v, hq7x, hq7y⟩
  have hq7c : OnCurveExt q7 := by
    show OnCurve (edX q7) (edY q7)
    rw [hq7x, cx6, hq7y, cy6]
    exact edAdd_closure (show OnCurve (edX A2) (edY A2) from hA2c)
      (show OnCurve (edX q6) (edY q6) from hq6c)
  have hq7pt : edPt q7 = edOdd 7 (edPt A) := by
    have h : edPt q7 = edAdd (edPt A2) (edPt q6) := by
      calc edPt q7 = (edX q7, edY q7) := rfl
        _ = ((edAdd (edPt A2) (edPt q6)).1, (edAdd (edPt A2) (edPt q6)).2) := by
            rw [hq7x, cx6, hq7y, cy6]
        _ = edAdd (edPt A2) (edPt q6) := rfl
    rw [h, hA2pt, hq6pt]
    rfl
  -- n7 ← q7.as_projective_niels   (the new table entry)
  step with (edwards_as_projective_niels_spec q7 hq7v) as ⟨n7, hn7v, hn7n⟩
  -- write it at index 7
  step as ⟨j6, hj6⟩
  have hj6v : j6 = 7#usize := by clear * - hj6; scalar_tac
  rw [hj6v]
  step as ⟨Ai7, hA7⟩
  have hl7 : (↑Ai7 : List backend.serial.curve_models.ProjectiveNielsPoint)
      = [n0, n1, n2, n3, n4, n5, n6, n7] := by
    simp only [hA7, Array.set_val_eq, hl6]
    rfl
  try simp only [spec_ok]
  -- ── iteration 7: range exhausted (start = end = 7) — done
  apply loop_step
  simp only [window.NafLookupTable5ProjectiveNielsPoint.Insts.CoreConvertFromSharedAEdwardsPoint.from_loop.body]
  step with (range_next_ge_spec iter6 (by clear * - hsv6 hev6; scalar_tac)) as ⟨o7, iter7, ho7, hr7⟩
  simp only [ho7]
  try simp only [spec_ok]
  refine ⟨n0, n1, n2, n3, n4, n5, n6, n7, hl7, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨hn0v, A, hn0n, hAv, hAc, hq0pt⟩
  · exact ⟨hn1v, q1, hn1n, hq1v, hq1c, hq1pt⟩
  · exact ⟨hn2v, q2, hn2n, hq2v, hq2c, hq2pt⟩
  · exact ⟨hn3v, q3, hn3n, hq3v, hq3c, hq3pt⟩
  · exact ⟨hn4v, q4, hn4n, hq4v, hq4c, hq4pt⟩
  · exact ⟨hn5v, q5, hn5n, hq5v, hq5c, hq5pt⟩
  · exact ⟨hn6v, q6, hn6n, hq6v, hq6c, hq6pt⟩
  · exact ⟨hn7v, q7, hn7n, hq7v, hq7c, hq7pt⟩

/-! ### The public table-construction spec -/

/-- **NafLookupTable5::from(&A)**: for a valid on-curve A, the table's 8
    entries are valid niels caches of valid on-curve points denoting
    A, 3A, 5A, …, 15A — the odd multiples as `edOdd` values over the
    proven abstract Edwards addition. -/
theorem naf_table_spec (A : EdPoint) (hA : ExtValid A) (hcA : OnCurveExt A) :
    window.NafLookupTable5ProjectiveNielsPoint.Insts.CoreConvertFromSharedAEdwardsPoint.from A
      ⦃ tbl => ∃ e0 e1 e2 e3 e4 e5 e6 e7,
          tblEntries tbl = [e0, e1, e2, e3, e4, e5, e6, e7] ∧
          NafEntryOf e0 A 0 ∧ NafEntryOf e1 A 1 ∧ NafEntryOf e2 A 2 ∧
          NafEntryOf e3 A 3 ∧ NafEntryOf e4 A 4 ∧ NafEntryOf e5 A 5 ∧
          NafEntryOf e6 A 6 ∧ NafEntryOf e7 A 7 ⦄ := by
  unfold window.NafLookupTable5ProjectiveNielsPoint.Insts.CoreConvertFromSharedAEdwardsPoint.from
  step with (edwards_as_projective_niels_spec A hA) as ⟨pnp, hpv, hpn⟩
  step with (edwards_double_law A hA hcA) as ⟨A2, hA2v, hA2c, hA2pt⟩
  step with (naf_table_loop_spec A A2 (Array.repeat 8#usize pnp) pnp
      (by simp [List.replicate]) hpv hpn hA hcA hA2v hA2c hA2pt) as
    ⟨e0, e1, e2, e3, e4, e5, e6, e7, tblA, hl, h0, h1, h2, h3, h4, h5, h6, h7⟩
  try simp only [spec_ok]
  exact ⟨e0, e1, e2, e3, e4, e5, e6, e7, hl, h0, h1, h2, h3, h4, h5, h6, h7⟩


/-! ### The table lookup -/

/-- **NafLookupTable5::select(x)** for odd x < 16: returns entry x/2 —
    enumerated per digit so downstream digit case-splits use it directly.
    The two `massert`s (x odd, x < 16) are DISCHARGED, certifying the
    absence of the lookup panic paths. -/
theorem naf_select_spec
    (tbl : window.NafLookupTable5 backend.serial.curve_models.ProjectiveNielsPoint)
    (x : Usize)
    (e0 e1 e2 e3 e4 e5 e6 e7 : backend.serial.curve_models.ProjectiveNielsPoint)
    (hl : tblEntries tbl = [e0, e1, e2, e3, e4, e5, e6, e7])
    (hodd : x.val % 2 = 1) (hlt : x.val < 16) :
    window.NafLookupTable5.select
      backend.serial.curve_models.ProjectiveNielsPoint.Insts.CoreMarkerCopy tbl x
      ⦃ r => (x.val = 1 → r = e0) ∧ (x.val = 3 → r = e1) ∧ (x.val = 5 → r = e2) ∧
             (x.val = 7 → r = e3) ∧ (x.val = 9 → r = e4) ∧ (x.val = 11 → r = e5) ∧
             (x.val = 13 → r = e6) ∧ (x.val = 15 → r = e7) ⦄ := by
  unfold window.NafLookupTable5.select
  step as ⟨lv, hlv⟩
  have hlv1 : lv = 1#usize := by
    clear * - hlv hodd
    have h1 : x.val &&& 1 = 1 := by rw [Nat.and_one_is_mod, hodd]
    scalar_tac
  step with (massert_spec _ hlv1) as ⟨hu1⟩
  step with (massert_spec (x < 16#usize) (by clear * - hlt; scalar_tac)) as ⟨hu2⟩
  step as ⟨i, hi⟩
  step as ⟨r, hr⟩
  simp only [tblEntries] at hl
  simp [hl] at hr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro hx
  · have hik : i.val = 0 := by clear * - hi hx; omega
    rw [hr]; simp [hik]
  · have hik : i.val = 1 := by clear * - hi hx; omega
    rw [hr]; simp [hik]
  · have hik : i.val = 2 := by clear * - hi hx; omega
    rw [hr]; simp [hik]
  · have hik : i.val = 3 := by clear * - hi hx; omega
    rw [hr]; simp [hik]
  · have hik : i.val = 4 := by clear * - hi hx; omega
    rw [hr]; simp [hik]
  · have hik : i.val = 5 := by clear * - hi hx; omega
    rw [hr]; simp [hik]
  · have hik : i.val = 6 := by clear * - hi hx; omega
    rw [hr]; simp [hik]
  · have hik : i.val = 7 := by clear * - hi hx; omega
    rw [hr]; simp [hik]

end CurveFieldProofs
