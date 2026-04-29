/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

/-!
# Embedding the upper half-plane into the projective line
-/

@[expose] public noncomputable section

open UpperHalfPlane
open Matrix GeneralLinearGroup

lemma toOnePoint_smul {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) (τ : ℍ) :
    (↑(g • τ) : OnePoint ℂ) = (g.map Complex.ofRealHom) • τ := by
  have : g 1 0 * (τ : ℂ) + g 1 1 ≠ 0 := UpperHalfPlane.denom_ne_zero g τ
  simp [OnePoint.smul_some_eq_ite, this, UpperHalfPlane.coe_smul_of_det_pos hg, num, denom]

/-- If `g` is parabolic, then `g` has no fixed points in `ℍ`. -/
lemma UpperHalfPlane.smul_ne_self_of_isParabolic {g : GL (Fin 2) ℝ} (hg : g.IsParabolic) (τ : ℍ) :
    g • τ ≠ τ := by
  rw [Ne, UpperHalfPlane.ext_iff, ← OnePoint.coe_eq_coe, toOnePoint_smul hg.val_det_pos,
    (hg.map _ <| RingHom.injective _).smul_eq_self_iff]
  intro hτ
  apply τ.im_ne_zero
  simp only [parabolicFixedPoint, Fin.isValue, GeneralLinearGroup.map_apply,
    Complex.ofRealHom_eq_coe, Complex.ofReal_eq_zero] at hτ
  split_ifs at hτ
  · exact (OnePoint.infty_ne_coe _ hτ.symm).elim
  · simp only [Fin.isValue, OnePoint.some_eq_iff] at hτ
    simp [← coe_im, hτ, Complex.div_im]

/-- If `g` is hyperbolic, then `g` has no fixed points in `ℍ`. -/
lemma UpperHalfPlane.smul_ne_self_of_isHyperbolic {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val)
    (hgh : g.IsHyperbolic) (τ : ℍ) :
    g • τ ≠ τ := by
  rcases τ with ⟨τ, hτ⟩
  suffices g 1 0 * τ ^ 2 + (g 1 1 - g 0 0) * τ - g 0 1 ≠ 0 by
    rw [Ne, UpperHalfPlane.ext_iff, ← OnePoint.coe_eq_coe]
    simpa [toOnePoint_smul hg, ← fixpointPolynomial_aeval_eq_zero_iff, fixpointPolynomial]
  contrapose! hτ
  by_cases hc : g 1 0 = 0
  · -- silly case : c = 0
    simp only [Fin.isValue, hc, Complex.ofReal_zero, zero_mul, zero_add] at hτ
    by_cases hd : g 1 1 = g 0 0
    · contrapose! hgh
      simp only [GeneralLinearGroup.IsHyperbolic, Matrix.IsHyperbolic, discr_fin_two, trace_fin_two,
        det_fin_two, hc, hd]
      grind
    rw [sub_eq_zero, mul_comm, ← div_eq_iff_mul_eq] at hτ
    · simp [← hτ, Complex.div_im]
    · norm_cast
      grind
  have := Real.sq_sqrt hgh.le
  rw [sq, ← Complex.ofReal_inj, Complex.ofReal_mul] at this
  rw [sq, sub_eq_add_neg, quadratic_eq_zero_iff (mod_cast hc) (s := ↑√g.val.discr)] at hτ
  · rcases hτ with hτ | hτ <;> simp [hτ, Complex.div_im]
  · convert this.symm
    simp [discrim, discr_fin_two, trace_fin_two, det_fin_two]
    ring

/-- The unique fixed point in the upper half-plane of an elliptic matrix.
(Junk if `g` is not elliptic.) -/
def Matrix.GeneralLinearGroup.ellipticFixedPoint (g : GL (Fin 2) ℝ) : ℍ :=
  .ofComplex ( (g 0 0 - g 1 1) / (2 * g 1 0)
      + .I * Real.sqrt ( -( (g 0 0 - g 1 1) ^ 2 + 4 * g 1 0 * g 0 1) / (4 * g 1 0 ^ 2) ))

lemma Matrix.GeneralLinearGroup.IsElliptic.coe_ellipticFixedPoint {g : GL (Fin 2) ℝ}
    (hg : g.IsElliptic) : (g.ellipticFixedPoint : ℂ) = ( (g 0 0 - g 1 1) / (2 * g 1 0)
      + .I * Real.sqrt ( -((g 0 0 - g 1 1) ^ 2 + 4 * g 1 0 * g 0 1) / (4 * g 1 0 ^ 2) )) := by
  rw [ellipticFixedPoint, ofComplex_apply_of_im_pos]
  suffices 0 < -((g 0 0 - g 1 1) ^ 2 + 4 * g 1 0 * g 0 1) / (4 * g 1 0 ^ 2) by
    simpa [Complex.div_im]
  have := hg.c_ne_zero
  simp only [IsElliptic, Matrix.IsElliptic, discr_fin_two, trace_fin_two, det_fin_two] at hg
  apply div_pos
  · grind
  · positivity

/-- Characterization of `ellipticFixedPoint` as the unique root of `g.fixpointPolynomial` lying
in the upper half-plane. -/
private lemma Matrix.GeneralLinearGroup.IsElliptic.fixpointPolynomial_aeval_eq_zero_iff'
    {g : GL (Fin 2) ℝ} (hg : g.IsElliptic) (τ : ℍ) :
    g.fixpointPolynomial.aeval (τ : ℂ) = 0 ↔ τ = g.ellipticFixedPoint := by
  -- This is a very annoying computation using the quadratic formula.
  -- First reduce to the case `0 < c`, by replacing `g` with `-g` if necessary.
  suffices ∀ {g : GL (Fin 2) ℝ} (hg : g.IsElliptic) (hc : 0 < g 1 0) (τ : ℍ),
      g.fixpointPolynomial.aeval (τ : ℂ) = 0 ↔ τ = g.ellipticFixedPoint by
    rcases hg.c_ne_zero.gt_or_lt with hc | hc
    · exact this hg hc τ
    · convert this (g := -g) ?_ (by simpa using hc) τ using 1
      · simp [fixpointPolynomial]
        grind
      · simp [ellipticFixedPoint]
        grind
      · simpa [IsElliptic, Matrix.IsElliptic, discr_fin_two, det_neg] using hg
  intro g hg hc τ
  let D := -((g 0 0 - g 1 1) ^ 2 + 4 * g 1 0 * g 0 1)
  have hD : 0 < D := by
    simp [IsElliptic, Matrix.IsElliptic, discr_fin_two, det_fin_two, trace_fin_two] at hg
    grind
  have : g.val.discr = -D := by grind [discr_fin_two, trace_fin_two, det_fin_two]
  -- Now apply `quadratic_eq_zero_iff` to `g.fixpointPolynomial`.
  have := quadratic_eq_zero_iff (a := (g 1 0 : ℂ)) (b := (g 1 1 - g 0 0 : ℂ)) (c := -g 0 1)
      (s := .I * Real.sqrt D) (mod_cast hg.c_ne_zero) ?_ τ
  · -- After some massaging, one of the roots is precisely `g.ellipticFixedPoint`.
    rw [← pow_two, ← sub_eq_add_neg] at this
    simp only [fixpointPolynomial, Fin.isValue, map_sub, map_add, map_mul, UpperHalfPlane.ext_iff,
      Polynomial.aeval_C, Complex.coe_algebraMap, map_pow, Polynomial.aeval_X, this, neg_sub,
      hg.coe_ellipticFixedPoint, add_div]
    change _ ↔ (τ : ℂ) = _ + _ * ↑√(D / _)
    simp_rw [Real.sqrt_div hD.le, Complex.ofReal_div, Real.sqrt_mul (show 0 ≤ 4 by norm_num),
      (show (4 : ℝ) = 2 ^ 2 by norm_num), Real.sqrt_sq hc.le, mul_div_assoc,
      Complex.ofReal_mul, Real.sqrt_sq two_pos.le, Complex.ofReal_ofNat]
    -- Need to show that the other root is not in `ℍ`.
    refine or_iff_left <| ne_of_apply_ne _ (lt_of_le_of_lt ?_ τ.im_pos).ne'
    suffices -(√D * (2 * g 1 0)) / (2 * 2 * g 1 0 ^ 2) ≤ 0 by simpa [Complex.div_im, pow_two]
    rw [neg_div, neg_nonpos]
    positivity
  · transitivity (-D)
    · simp [discrim, D]
      ring_nf
    · conv_lhs => rw [← Real.sq_sqrt hD.le]
      ring_nf
      norm_num

/-- If `g` is elliptic, then `g` has exactly one fixed point in `ℍ`, equal to
`g.ellipticFixedPoint`. -/
lemma Matrix.GeneralLinearGroup.IsElliptic.smul_eq_self_iff
    {g : GL (Fin 2) ℝ} (hg : g.IsElliptic) (τ : ℍ) :
    g • τ = τ ↔ τ = g.ellipticFixedPoint := by
  rw [UpperHalfPlane.ext_iff, ← OnePoint.coe_eq_coe, toOnePoint_smul hg.det_pos,
    ← fixpointPolynomial_aeval_eq_zero_iff, ← hg.fixpointPolynomial_aeval_eq_zero_iff']
  simp [fixpointPolynomial]

namespace UpperHalfPlane
/-!
## Stabilizers and fixed points
-/

/-- The pointwise stabilizer of the vertical line `ℝ₊ • I` in `GL(2, ℝ)₊` is the scalar multiples
of the identity. -/
lemma forall_smul_pos_mul_I_eq_iff_of_det_pos {g : GL (Fin 2) ℝ} (hdet : 0 < g.det.val) :
    (∀ (t : ℝ) (ht : 0 < t), g • (⟨t * .I, by simpa⟩ : ℍ) = ⟨t * .I, by simpa⟩)
      ↔ ∃ r : ℝˣ, g = r • 1 where
  mp hg := by
    have hg1 : g • I = I := by simpa using hg 1 (by norm_num)
    have hp : ¬g.IsParabolic := fun h ↦ I.smul_ne_self_of_isParabolic h hg1
    have hh : ¬g.IsHyperbolic := fun h ↦ I.smul_ne_self_of_isHyperbolic hdet h hg1
    have he : ¬g.IsElliptic := fun he ↦ by
      have hI := (he.smul_eq_self_iff _).1 hg1
      have h2I := (he.smul_eq_self_iff _).1 <| hg 2 (by norm_num)
      simpa [UpperHalfPlane.ext_iff] using hI.trans h2I.symm
    obtain ⟨r, hr⟩ : g.val ∈ Set.range (Matrix.scalar (Fin 2)) := by
      simp only [Matrix.IsParabolic] at hp
      grind [eq_of_ge_of_le (not_lt.mp he) (not_lt.mp hh)]
    have := Units.mul_inv g
    rw [← hr] at this
    use .mkOfMulEqOne r _ (by simpa using congr_arg (· 0 0) this)
    simp [Units.ext_iff, Units.smul_def, ← hr, Matrix.smul_one_eq_diagonal]
  mpr := by
    rintro ⟨r, rfl⟩ t ht
    ext
    simp [coe_smul_of_det_pos hdet, num, denom, Units.smul_def]

/-- The pointwise stabilizer of the vertical line `ℝ₊ • I` in `GL(2, ℝ)` consists of the scalar
multiples of the identity and of `J = [-1, 0; 0, 1]`. -/
lemma forall_smul_pos_mul_I_eq_iff {g : GL (Fin 2) ℝ} :
    (∀ (t : ℝ) (ht : 0 < t), g • (⟨t * .I, by simpa⟩ : ℍ) = ⟨t * .I, by simpa⟩) ↔
      (∃ r : ℝˣ, g = r • 1) ∨ (∃ r : ℝˣ, g = r • J) := by
  by_cases h : 0 < g.det.val
  · rw [forall_smul_pos_mul_I_eq_iff_of_det_pos h]
    suffices ¬∃ r, g = r • J by tauto
    contrapose! h
    obtain ⟨r, rfl⟩ := h
    simp [Units.smul_def, mul_self_nonneg r.val]
  · -- If `det g < 0`, we show that `g * J⁻¹` also fixes the vertical line
    have : ¬∃ r : ℝˣ, g = r • 1 := by
      contrapose! h
      rcases h with ⟨r, rfl⟩
      refine lt_of_le_of_ne' ?_ (Units.ne_zero _)
      simp [Units.smul_def, sq_nonneg]
    rw [eq_false_intro this, false_or]
    conv => enter [1, t, ht, 1]; rw [← J_smul_pos_mul_I ht, ← SemigroupAction.mul_smul, ← inv_J]
    rw [forall_smul_pos_mul_I_eq_iff_of_det_pos]
    · simp only [mul_inv_eq_iff_eq_mul (a := g), smul_one_mul]
    · rw [map_mul, map_inv, det_J, inv_neg_one, mul_neg_one, Units.val_neg]
      grind [g.det_ne_zero.lt_or_gt, Matrix.GeneralLinearGroup.val_det_apply]

/-- The only elements of `GL(2, ℝ)` that act trivially on the whole upper half-plane are the
scalar matrices. -/
lemma forall_smul_eq_iff {g : GL (Fin 2) ℝ} : (∀ τ : ℍ, g • τ = τ) ↔ (∃ r : ℝˣ, g = r • 1) where
  mp h := by
    refine (forall_smul_pos_mul_I_eq_iff.mp (fun t ht ↦ h _)).resolve_right fun ⟨r, hr⟩ ↦ ?_
    simpa [hr, UpperHalfPlane.ext_iff, coe_smul, σ, Units.smul_def, (mul_self_nonneg r.val).not_gt,
      num, denom, div_eq_iff (Complex.ofReal_ne_zero.mpr r.ne_zero), Complex.ext_iff, neg_eq_self]
      using h ((1 : ℝ) +ᵥ I)
  mpr := fun ⟨r, hr⟩ τ ↦ UpperHalfPlane.ext <| by
    simp [hr, coe_smul, σ, Units.smul_def, sq_pos_of_ne_zero r.ne_zero, num, denom]

lemma forall_smul_eq_iff_of_det_eq_one {g : GL (Fin 2) ℝ} (hg : g.det = 1) :
    (∀ τ : ℍ, g • τ = τ) ↔ g = 1 ∨ g = -1 := by
  rw [UpperHalfPlane.forall_smul_eq_iff]
  constructor
  · rintro ⟨r, rfl⟩
    have : r ^ 2 • (1 : ℝ) = 1 := by simpa [Units.ext_iff] using hg
    have : r = 1 ∨ r = -1 := by simpa [Units.smul_def]
    aesop
  · rintro (rfl | rfl)
    · exact ⟨1, by ext; simp⟩
    · exact ⟨-1, by ext; simp⟩

end UpperHalfPlane

namespace ModularGroup

open scoped MatrixGroups

variable {g : SL(2, ℤ)}

/-- No element of `SL(2, ℤ)` except `±1` acts trivially on `ℍ`. -/
lemma forall_smul_eq_iff : (∀ τ : ℍ, g • τ = τ) ↔ g = 1 ∨ g = -1 := by
  simp only [sl_moeb, forall_smul_eq_iff_of_det_eq_one <| SpecialLinearGroup.coeToGL_det _,
    ← SpecialLinearGroup.mapGL_inj (S := ℝ), map_one]
  congr!
  ext
  simp

end ModularGroup

end
