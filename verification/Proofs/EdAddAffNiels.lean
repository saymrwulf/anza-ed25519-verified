/- ───────────────────────────────────────────────────────────────────────────
   Proofs/EdAddAffNiels.lean — coordinate-level specs for the MIXED addition
   kernels  EdwardsPoint ± AffineNielsPoint -> CompletedPoint  and for the
   negation of an AffineNielsPoint.

   CONTEXT.  The Rust crate curve25519/solana-ed25519 adds an extended point
   P = (X₁:Y₁:Z₁:T₁) and a PRECOMPUTED affine cache N = (y+x, y−x, 2dxy)
   (an `AffineNielsPoint`, implicit Z = 1 — see Proofs/EdDenote.lean) with
   the Hisil–Wong–Carter–Dawson mixed formulas
   (src/backend/serial/curve_models.rs:458-472 for `add`, 479-493 for `sub`):

       PP    = (Y₁+X₁)·(y+x)          MM = (Y₁−X₁)·(y−x)
       Txy2d = T₁·(2dxy)              Z2 = Z₁+Z₁
       add:  (X, Y, Z, T) = (PP−MM, PP+MM, Z2+Txy2d, Z2−Txy2d)
       sub:  mirrored — multiply CROSSWISE (PM = (Y₁+X₁)(y−x),
             MP = (Y₁−X₁)(y+x)) and FLIP the sign of Txy2d in Z/T:
             (X, Y, Z, T) = (PM−MP, PM+MP, Z2−Txy2d, Z2+Txy2d)

   (3 muls, 3 unreduced adds, 3 reduced subs each — one mul fewer than the
   projective-Niels kernels because the affine cache has no Z field).
   `neg` (curve_models.rs:516-522) negates the cached point by SWAPPING the
   y+x / y−x fields and negating 2dxy:  −(x, y) = (−x, y), so
   y+(−x) = y−x, y−(−x) = y+x, 2d(−x)y = −2dxy.

   THIS FILE proves, in the STATEMENT POLICY of the point-spec phase
   (coordinate level ONLY — no curve constants, no division, no OnCurve;
   the algebra-law packaging happens in a later file):

     * `add_affniels_spec` / `sub_affniels_spec` — under `ExtValid Pt` and
       `AffNielsValid N` (the limb-bound + Z ≠ 0 validity predicates of
       Proofs/EdDenote.lean) the kernels run PANIC-FREE, every output field
       carries the exact bound its producing field op guarantees
       (sub: 2⁵², single unreduced add of two reduced/mul outputs: 2⁵³,
       unreduced add consuming another unreduced add: 2⁵⁴), and the four
       coordinates satisfy the formulas above, stated STRICTLY in terms of
       the input struct-field denotations ⟪Pt.X⟫ … ⟪N.xy2d⟫;
     * `affniels_neg_spec` — negation runs, preserves `AffNielsValid`, and
       denotes the field swap + negation.

   BOUND BOOKKEEPING (the entire panic-freedom argument).  Inputs carry
   Bnd 2⁵² (ExtValid) resp. Bnd 2⁵³/2⁵² (AffNielsValid); the field ops
   require Bnd 2⁵⁴ (mul/sub, MulSpec/SubNegSpec) resp. pairwise limb sums
   < 2⁶⁴ (the unreduced add, AddSpec).  Chasing the chain:

       Y₁+X₁, Z2 : add of two 2⁵² values            -> 2⁵³   (< 2⁵⁴ ✓)
       Y₁−X₁     : sub                              -> 2⁵²
       PP/MM/PM/MP/Txy2d : mul of ≤ 2⁵³/2⁵³ inputs  -> 2⁵¹+2¹³
       X-output  : sub of two mul outputs           -> 2⁵²
       Y-output  : add of two mul outputs           -> 2⁵³
       Z2 ± Txy2d: sub -> 2⁵²;  add of 2⁵³ + (2⁵¹+2¹³) values -> 2⁵⁴

   so every intermediate is a legal input for its consumer, and the output
   bounds exposed below (X: 2⁵², Y: 2⁵³, then add: Z 2⁵⁴ / T 2⁵²,
   sub: Z 2⁵² / T 2⁵⁴) are the TRUE per-field bounds of the chain.

   PROOF TECHNIQUE: the InvertSpec playbook — unfold the transpiled body,
   walk it with `let* ⟨x, posts…⟩ ← spec by edis` (one field op per line;
   `edis` discharges each op's Bnd side condition by hypothesis weakening;
   where the needed bound is verbatim in context the `let*` machinery
   discharges it itself and no `by` block is given).  The final `let*`
   also reduces the trailing `ok {…}` and collapses the constructor
   projections, so the four coordinate equations close by rewriting the
   recorded postconditions (plus `ring` where 2·Z appears as Z+Z).
   The three `aff_*`-prefixed wrappers re-state AddSpec's `add_spec` (whose
   hypotheses name all 10 limbs, so the `let*` machinery cannot apply it
   directly) and SubNegSpec's `sub_spec`/`neg_spec` in hypothesis-light form,
   exactly like `mul_spec'` (InvertSpec.lean); prefixed `aff_` to avoid name
   collisions with the sibling point-op spec files, which declare their own.

   Nothing in gen/ is modified; we only run the transpiled code.

   Imports: Proofs/EdDenote (validity predicates, mk_* lemmas, ⟪·⟫/Bnd via
   FieldMain) and Proofs/Square2Spec (uniform field-op spec environment of
   the point-op phase).  Imported by: the forthcoming Edwards algebra layer.
   ─────────────────────────────────────────────────────────────────────── -/
import Proofs.EdDenote
import Proofs.Square2Spec
open Aeneas Aeneas.Std Result
open curve25519

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace CurveFieldProofs

-- the weakest-precondition layer: spec_mono / spec_ok used below
open Aeneas.Std.WP

/-- Discharge: linear arithmetic, or a `Bnd` weakening from any hypothesis.

    Every field op consumed below needs its inputs bounded (mul/sub: 2⁵⁴,
    the add wrappers: 2⁵²/2⁵³), while the producing step only recorded a
    tighter bound (2⁵², 2⁵³ or 2⁵¹+2¹³); this side-condition tactic closes
    such goals either by `scalar_tac` or by weakening an existing `Bnd _ c`
    hypothesis with `Bnd.mono` and `c ≤ c'` by `norm_num`.  Passed as the
    discharger to every `let*` step.  (Local re-declaration of InvertSpec's
    `bnd` macro — macros are kept file-local in this development.)
    (`name :=` disambiguates the generated syntax-kind declaration from the
    sibling files' `edis` macros so they can all be imported together.) -/
macro (name := edisAffNiels) "edis" : tactic =>
  `(tactic| (first
      | scalar_tac
      | exact Bnd.mono (by assumption) (by norm_num)))

/-! ## Hypothesis-light wrappers for the unreduced add, sub and negate

    The base specs take the 5 limbs of every argument as explicit variables
    (their proofs compute limb by limb), so the `let*` machinery cannot
    apply them directly; each wrapper repackages the limbs existentially via
    `Fe.exists_limbs` — the `mul_spec'` pattern of Proofs/InvertSpec.lean.
    The unreduced `fe_add` needs TWO instances because its output bound is
    input-relative (`∀ c, Bnd a c → Bnd b c → Bnd r (2·c)`, AddSpec.lean):
    the kernels below add reduced values (2⁵² → 2⁵³) but also feed one add
    output into another add (2⁵³ → 2⁵⁴). -/

/-- RUST ANALOG: `impl Add for FieldElement51` (the `+` operator),
    curve25519/solana-ed25519/src/backend/serial/u64/field.rs:68-72 (limbwise
    `a[i] + b[i]`, no carry, no reduction) — verified in AddSpec.lean.

    MATH:  Bnd(a, 2⁵²) and Bnd(b, 2⁵²)  ==>  fe_add a b = ok r  with
           Bnd(r, 2⁵³)  and  ⟪r⟫ = ⟪a⟫ + ⟪b⟫.
    LaTeX: $\mathrm{Bnd}(a,2^{52}) \wedge \mathrm{Bnd}(b,2^{52}) \Rightarrow
           \llbracket r\rrbracket = \llbracket a\rrbracket+\llbracket b\rrbracket$.
    Totality: each limb sum is < 2⁵² + 2⁵² = 2⁵³ < 2⁶⁴ — no u64 overflow.
    WHY NEEDED: the Y₁+X₁ / Z₁+Z₁ / PP+MM additions below consume REDUCED
    (2⁵², or 2⁵¹+2¹³ mul-output) values; this instance records the tight
    2⁵³ output bound those sums actually satisfy. -/
theorem aff_add_spec53 (a b : Fe) (ha : Bnd a (2^52)) (hb : Bnd b (2^52)) :
    fe_add a b ⦃ r => Bnd r (2^53) ∧ ⟪r⟫ = ⟪a⟫ + ⟪b⟫ ⦄ := by
  obtain ⟨x0, x1, x2, x3, x4, hA⟩ := Fe.exists_limbs a   -- materialize a's limbs
  obtain ⟨y0, y1, y2, y3, y4, hB⟩ := Fe.exists_limbs b   -- materialize b's limbs
  -- per-limb inequalities for the pairwise-sum < 2⁶⁴ side condition
  have ha' := (Bnd_eq a x0 x1 x2 x3 x4 _ hA).mp ha
  have hb' := (Bnd_eq b y0 y1 y2 y3 y4 _ hB).mp hb
  apply spec_mono (add_spec a b x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 hA hB
    ⟨by omega, by omega, by omega, by omega, by omega⟩)
  rintro r ⟨-, hval, hbnd⟩
  -- bound: instantiate AddSpec's relative law at c = 2⁵², weaken 2·2⁵² ≤ 2⁵³
  refine ⟨(hbnd (2^52) ha hb).mono (by norm_num), ?_⟩
  -- value: feVal r = feVal a + feVal b over ℕ, cast once into 𝔽_p
  simp only [denote, hval, Nat.cast_add]

/-- RUST ANALOG: same operator as `aff_add_spec53`, at the next bound level.

    MATH:  Bnd(a, 2⁵³) and Bnd(b, 2⁵³)  ==>  fe_add a b = ok r  with
           Bnd(r, 2⁵⁴)  and  ⟪r⟫ = ⟪a⟫ + ⟪b⟫.
    Totality: limb sums < 2⁵³ + 2⁵³ = 2⁵⁴ < 2⁶⁴.
    WHY NEEDED: the Z-coordinate of the `add` kernel (resp. T of `sub`) is
    Z2 + Txy2d where Z2 = Z₁+Z₁ is itself an UNREDUCED add output (2⁵³) —
    one level above what `aff_add_spec53` admits.  Output 2⁵⁴ is still a
    legal input for every downstream field op (their invariant is < 2⁵⁴…
    consumers weaken via `Bnd.mono` where they need ≤). -/
@[step]
theorem aff_add_spec54 (a b : Fe) (ha : Bnd a (2^53)) (hb : Bnd b (2^53)) :
    fe_add a b ⦃ r => Bnd r (2^54) ∧ ⟪r⟫ = ⟪a⟫ + ⟪b⟫ ⦄ := by
  obtain ⟨x0, x1, x2, x3, x4, hA⟩ := Fe.exists_limbs a
  obtain ⟨y0, y1, y2, y3, y4, hB⟩ := Fe.exists_limbs b
  have ha' := (Bnd_eq a x0 x1 x2 x3 x4 _ hA).mp ha
  have hb' := (Bnd_eq b y0 y1 y2 y3 y4 _ hB).mp hb
  apply spec_mono (add_spec a b x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 hA hB
    ⟨by omega, by omega, by omega, by omega, by omega⟩)
  rintro r ⟨-, hval, hbnd⟩
  refine ⟨(hbnd (2^53) ha hb).mono (by norm_num), ?_⟩
  simp only [denote, hval, Nat.cast_add]

/-- RUST ANALOG: `impl Sub for FieldElement51` (the 16p-trick subtraction),
    field.rs:84-101 — verified in SubNegSpec.lean.

    MATH:  Bnd(a, 2⁵⁴) and Bnd(b, 2⁵⁴)  ==>  fe_sub a b = ok r  with
           Bnd(r, 2⁵²)  and  ⟪r⟫ = ⟪a⟫ − ⟪b⟫.
    WHY NEEDED: hypothesis-light restatement of `sub_spec` (which names all
    10 limbs) for the `let*` machinery — the Y₁−X₁, PP−MM and Z2−Txy2d
    steps below. -/
@[step]
theorem aff_sub_spec (a b : Fe) (ha : Bnd a (2^54)) (hb : Bnd b (2^54)) :
    fe_sub a b ⦃ r => Bnd r (2^52) ∧ ⟪r⟫ = ⟪a⟫ - ⟪b⟫ ⦄ := by
  obtain ⟨x0, x1, x2, x3, x4, hA⟩ := Fe.exists_limbs a
  obtain ⟨y0, y1, y2, y3, y4, hB⟩ := Fe.exists_limbs b
  exact sub_spec a b x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 hA hB ha hb

/-- RUST ANALOG: `FieldElement51::negate` (16p − a, then reduce),
    field.rs:276-286 — verified in SubNegSpec.lean.

    MATH:  Bnd(a, 2⁵⁴)  ==>  fe_neg a = ok r  with  Bnd(r, 2⁵²)  and
           ⟪r⟫ = −⟪a⟫.
    WHY NEEDED: hypothesis-light restatement of `neg_spec` for the single
    negate step of `affniels_neg_spec`. -/
@[step]
theorem aff_neg_spec (a : Fe) (ha : Bnd a (2^54)) :
    fe_neg a ⦃ r => Bnd r (2^52) ∧ ⟪r⟫ = -⟪a⟫ ⦄ := by
  obtain ⟨x0, x1, x2, x3, x4, hA⟩ := Fe.exists_limbs a
  exact neg_spec a x0 x1 x2 x3 x4 hA ha

/-! ## The two mixed-addition kernels -/

/-- Rust: `impl Add<&AffineNielsPoint, CompletedPoint> for &EdwardsPoint`,
    src/backend/serial/curve_models.rs:458-472; transpiled at
    gen/CurveField/Funs.lean:1604-1640 as
    `Shared0EdwardsPoint.Insts.CoreOpsArithAddSharedAAffineNielsPointCompletedPoint.add`.

    MATH (coordinate level; writing X₁ = ⟪Pt.X⟫ etc., y±x = ⟪N.y_plus_x⟫ /
    ⟪N.y_minus_x⟫, 2dxy = ⟪N.xy2d⟫):  under ExtValid Pt and AffNielsValid N
    the kernel runs panic-free and returns the completed point

        X = (Y₁+X₁)(y+x) − (Y₁−X₁)(y−x)        [= PP − MM]
        Y = (Y₁+X₁)(y+x) + (Y₁−X₁)(y−x)        [= PP + MM]
        Z = 2Z₁ + T₁·2dxy                       [= Z2 + Txy2d]
        T = 2Z₁ − T₁·2dxy                       [= Z2 − Txy2d]

    with the exact per-field bounds of the producing ops: X,T from `sub`
    (2⁵²), Y a single unreduced add of two mul outputs (2⁵³), Z an
    unreduced add consuming the unreduced Z2 (2⁵⁴) — all < 2⁵⁴+1, i.e.
    consumable by every field op.  NO curve constant and NO division
    appears: the equations are stated strictly over the input struct-field
    denotations; the later algebra layer combines them with `IsAffNielsOf`
    (which characterizes ⟪N.xy2d⟫ via 121666·⟪N.xy2d⟫ = −243330·(x·y)) and
    the curve equation to obtain the Edwards addition law.

    WHY NEEDED: this is THE workhorse of fixed-base scalar multiplication —
    `mul_base` adds table entries (AffineNielsPoint) to the accumulator with
    exactly this kernel. -/
theorem add_affniels_spec (Pt : EdPoint) (N : AffNiels)
    (hPt : ExtValid Pt) (hN : AffNielsValid N) :
    Shared0EdwardsPoint.Insts.CoreOpsArithAddSharedAAffineNielsPointCompletedPoint.add
      Pt N ⦃ r =>
      Bnd r.X (2^52) ∧ Bnd r.Y (2^53) ∧ Bnd r.Z (2^54) ∧ Bnd r.T (2^52) ∧
      ⟪r.X⟫ = (⟪Pt.Y⟫ + ⟪Pt.X⟫) * ⟪N.y_plus_x⟫
                - (⟪Pt.Y⟫ - ⟪Pt.X⟫) * ⟪N.y_minus_x⟫ ∧
      ⟪r.Y⟫ = (⟪Pt.Y⟫ + ⟪Pt.X⟫) * ⟪N.y_plus_x⟫
                + (⟪Pt.Y⟫ - ⟪Pt.X⟫) * ⟪N.y_minus_x⟫ ∧
      ⟪r.Z⟫ = 2 * ⟪Pt.Z⟫ + ⟪Pt.T⟫ * ⟪N.xy2d⟫ ∧
      ⟪r.T⟫ = 2 * ⟪Pt.Z⟫ - ⟪Pt.T⟫ * ⟪N.xy2d⟫ ⦄ := by
  -- unpack the validity predicates (Z≠0 and the Segre coherence are not
  -- needed at coordinate level — they ride along for the algebra layer)
  obtain ⟨hPX, hPY, hPZ, hPT, -, -⟩ := hPt
  obtain ⟨hNyp, hNym, hNxy⟩ := hN
  -- expose the transpiled 10-step monadic body
  unfold Shared0EdwardsPoint.Insts.CoreOpsArithAddSharedAAffineNielsPointCompletedPoint.add
  -- Y_plus_X = Y₁+X₁ (unreduced add of two 2⁵² coords -> 2⁵³;
  -- the 2⁵² side conditions are hypotheses verbatim — no discharger needed)
  let* ⟨ YpX, YpX_bnd, YpX_val ⟩ ← aff_add_spec53
  -- Y_minus_X = Y₁−X₁ (reduced sub -> 2⁵²)
  let* ⟨ YmX, YmX_bnd, YmX_val ⟩ ← aff_sub_spec by edis
  -- PP = (Y₁+X₁)·(y+x);  inputs 2⁵³ ≤ 2⁵⁴ -> 2⁵¹+2¹³
  let* ⟨ PP, PP_bnd, PP_val ⟩ ← mul_spec' by edis
  -- MM = (Y₁−X₁)·(y−x)
  let* ⟨ MM, MM_bnd, MM_val ⟩ ← mul_spec' by edis
  -- Txy2d = T₁·(2dxy)
  let* ⟨ Txy, Txy_bnd, Txy_val ⟩ ← mul_spec' by edis
  -- Z2 = Z₁+Z₁ (unreduced -> 2⁵³; side conditions verbatim in context)
  let* ⟨ Z2, Z2_bnd, Z2_val ⟩ ← aff_add_spec53
  -- X = PP − MM (sub -> 2⁵²)
  let* ⟨ rX, rX_bnd, rX_val ⟩ ← aff_sub_spec by edis
  -- Y = PP + MM (mul outputs ≤ 2⁵² -> 2⁵³)
  let* ⟨ rY, rY_bnd, rY_val ⟩ ← aff_add_spec53 by edis
  -- Z = Z2 + Txy2d (2⁵³ + mul output -> 2⁵⁴)
  let* ⟨ rZ, rZ_bnd, rZ_val ⟩ ← aff_add_spec54 by edis
  -- T = Z2 − Txy2d (sub -> 2⁵²)
  let* ⟨ rT, rT_bnd, rT_val ⟩ ← aff_sub_spec by edis
  -- the tail `ok { X := rX, Y := rY, Z := rZ, T := rT }` was already reduced
  -- by the final `let*` (it also collapsed the constructor projections);
  -- left: the four bounds + four coordinate equations.  Substitute the
  -- recorded step posts; X/Y close by rewriting alone, Z/T need `ring`
  -- for Z₁+Z₁ = 2·Z₁
  refine ⟨rX_bnd, rY_bnd, rZ_bnd, rT_bnd, ?_, ?_, ?_, ?_⟩
  · rw [rX_val, PP_val, MM_val, YpX_val, YmX_val]
  · rw [rY_val, PP_val, MM_val, YpX_val, YmX_val]
  · rw [rZ_val, Z2_val, Txy_val]; ring
  · rw [rT_val, Z2_val, Txy_val]; ring

/-- Rust: `impl Sub<&AffineNielsPoint, CompletedPoint> for &EdwardsPoint`,
    src/backend/serial/curve_models.rs:479-493; transpiled at
    gen/CurveField/Funs.lean:1657-1693 as
    `Shared0EdwardsPoint.Insts.CoreOpsArithSubSharedAAffineNielsPointCompletedPoint.sub`.

    MATH: the mirror image of `add_affniels_spec` — subtraction of the
    cached point is addition of its negation (−x, y), whose cache swaps
    y+x ↔ y−x and negates 2dxy (cf. `affniels_neg_spec` below); the Rust
    code inlines that swap by multiplying CROSSWISE and flipping the sign
    of Txy2d in the Z/T outputs.  Under ExtValid Pt and AffNielsValid N:

        X = (Y₁+X₁)(y−x) − (Y₁−X₁)(y+x)        [= PM − MP]
        Y = (Y₁+X₁)(y−x) + (Y₁−X₁)(y+x)        [= PM + MP]
        Z = 2Z₁ − T₁·2dxy                       [= Z2 − Txy2d]
        T = 2Z₁ + T₁·2dxy                       [= Z2 + Txy2d]

    with the per-field bounds of the producing ops — note Z/T trade places
    with `add`'s: here Z comes from `sub` (2⁵²) and T from the unreduced
    add (2⁵⁴).

    WHY NEEDED: scalar multiplication with signed digit recodings (NAF)
    subtracts table entries as often as it adds them. -/
theorem sub_affniels_spec (Pt : EdPoint) (N : AffNiels)
    (hPt : ExtValid Pt) (hN : AffNielsValid N) :
    Shared0EdwardsPoint.Insts.CoreOpsArithSubSharedAAffineNielsPointCompletedPoint.sub
      Pt N ⦃ r =>
      Bnd r.X (2^52) ∧ Bnd r.Y (2^53) ∧ Bnd r.Z (2^52) ∧ Bnd r.T (2^54) ∧
      ⟪r.X⟫ = (⟪Pt.Y⟫ + ⟪Pt.X⟫) * ⟪N.y_minus_x⟫
                - (⟪Pt.Y⟫ - ⟪Pt.X⟫) * ⟪N.y_plus_x⟫ ∧
      ⟪r.Y⟫ = (⟪Pt.Y⟫ + ⟪Pt.X⟫) * ⟪N.y_minus_x⟫
                + (⟪Pt.Y⟫ - ⟪Pt.X⟫) * ⟪N.y_plus_x⟫ ∧
      ⟪r.Z⟫ = 2 * ⟪Pt.Z⟫ - ⟪Pt.T⟫ * ⟪N.xy2d⟫ ∧
      ⟪r.T⟫ = 2 * ⟪Pt.Z⟫ + ⟪Pt.T⟫ * ⟪N.xy2d⟫ ⦄ := by
  obtain ⟨hPX, hPY, hPZ, hPT, -, -⟩ := hPt
  obtain ⟨hNyp, hNym, hNxy⟩ := hN
  unfold Shared0EdwardsPoint.Insts.CoreOpsArithSubSharedAAffineNielsPointCompletedPoint.sub
  -- Y_plus_X = Y₁+X₁ -> 2⁵³ (side conditions verbatim in context);
  -- Y_minus_X = Y₁−X₁ -> 2⁵²
  let* ⟨ YpX, YpX_bnd, YpX_val ⟩ ← aff_add_spec53
  let* ⟨ YmX, YmX_bnd, YmX_val ⟩ ← aff_sub_spec by edis
  -- the crosswise products:  PM = (Y₁+X₁)(y−x),  MP = (Y₁−X₁)(y+x)
  let* ⟨ PM, PM_bnd, PM_val ⟩ ← mul_spec' by edis
  let* ⟨ MP, MP_bnd, MP_val ⟩ ← mul_spec' by edis
  -- Txy2d = T₁·(2dxy);  Z2 = Z₁+Z₁ (side conditions verbatim in context)
  let* ⟨ Txy, Txy_bnd, Txy_val ⟩ ← mul_spec' by edis
  let* ⟨ Z2, Z2_bnd, Z2_val ⟩ ← aff_add_spec53
  -- X = PM − MP;  Y = PM + MP;  Z = Z2 − Txy2d;  T = Z2 + Txy2d
  let* ⟨ rX, rX_bnd, rX_val ⟩ ← aff_sub_spec by edis
  let* ⟨ rY, rY_bnd, rY_val ⟩ ← aff_add_spec53 by edis
  let* ⟨ rZ, rZ_bnd, rZ_val ⟩ ← aff_sub_spec by edis
  let* ⟨ rT, rT_bnd, rT_val ⟩ ← aff_add_spec54 by edis
  -- bounds + equations (the final `let*` reduced the trailing `ok {…}`)
  refine ⟨rX_bnd, rY_bnd, rZ_bnd, rT_bnd, ?_, ?_, ?_, ?_⟩
  · rw [rX_val, PM_val, MP_val, YpX_val, YmX_val]
  · rw [rY_val, PM_val, MP_val, YpX_val, YmX_val]
  · rw [rZ_val, Z2_val, Txy_val]; ring
  · rw [rT_val, Z2_val, Txy_val]; ring

/-! ## Negation of an affine-Niels cache point -/

/-- Rust: `impl Neg for &AffineNielsPoint`,
    src/backend/serial/curve_models.rs:516-522; transpiled at
    gen/CurveField/Funs.lean:1767-1773 as
    `Shared0AffineNielsPoint.Insts.CoreOpsArithNegAffineNielsPoint.neg`
    (the single field negation goes through the operator wrapper
    `Shared0FieldElement51.Insts.CoreOpsArithNegFieldElement51.neg`,
    Funs.lean:1732, which is definitionally `FieldElement51::negate`).

    MATH:  AffNielsValid N  ==>  neg N = ok r  with  AffNielsValid r  and

        ⟪r.y_plus_x⟫  = ⟪N.y_minus_x⟫,
        ⟪r.y_minus_x⟫ = ⟪N.y_plus_x⟫,
        ⟪r.xy2d⟫      = −⟪N.xy2d⟫.

    On denotations this IS the cache of the negated affine point: if N
    caches (x, y) then r caches (−x, y), since y+(−x) = y−x, y−(−x) = y+x
    and 2d(−x)y = −(2dxy) — the algebra layer derives
    `IsAffNielsOf N x y → IsAffNielsOf r (−x) y` from these three equations
    by ring reasoning on the 121666-characterization of `IsAffNielsOf`.
    Validity is PRESERVED (not just some bound): the swapped fields keep
    their 2⁵³ bounds verbatim, and `negate` REDUCES, returning 2⁵² — so r
    can re-enter the add/sub kernels above.  (The y±x swap is pure data
    movement — the two equations hold by `rfl`; only xy2d runs code.)

    WHY NEEDED: signed-digit lookup tables (`NafLookupTable`/`select`)
    produce −N for negative digits with exactly this function. -/
theorem affniels_neg_spec (N : AffNiels) (hN : AffNielsValid N) :
    Shared0AffineNielsPoint.Insts.CoreOpsArithNegAffineNielsPoint.neg N ⦃ r =>
      AffNielsValid r ∧
      ⟪r.y_plus_x⟫ = ⟪N.y_minus_x⟫ ∧
      ⟪r.y_minus_x⟫ = ⟪N.y_plus_x⟫ ∧
      ⟪r.xy2d⟫ = -⟪N.xy2d⟫ ⦄ := by
  obtain ⟨hNyp, hNym, hNxy⟩ := hN
  -- expose the body and the operator wrapper around `negate`
  unfold Shared0AffineNielsPoint.Insts.CoreOpsArithNegAffineNielsPoint.neg
    Shared0FieldElement51.Insts.CoreOpsArithNegFieldElement51.neg
  -- the one field op: xy2d' = −xy2d (input 2⁵² ≤ 2⁵⁴, output reduced 2⁵²)
  let* ⟨ nx, nx_bnd, nx_val ⟩ ← aff_neg_spec by edis
  -- the final `let*` reduced the tail `ok { y_plus_x := N.y_minus_x,
  -- y_minus_x := N.y_plus_x, xy2d := nx }` and already closed the two
  -- pure-data-movement equations (they are `rfl` after the projections
  -- collapse); left: validity — the swap preserves the 2⁵³ bounds and
  -- negate's reduced output is the required 2⁵² — and the xy2d equation
  exact ⟨⟨hNym, hNyp, nx_bnd⟩, nx_val⟩

end CurveFieldProofs
