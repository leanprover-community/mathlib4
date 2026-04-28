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
lemma UpperHalfPlane.smul_ne_self_of_isParabolic
    {g : GL (Fin 2) ℝ} (hg : g.IsParabolic) (τ : ℍ) :
    g • τ ≠ τ := by
  have hdet : 0 < g.det.val := hg.val_det_pos
  rw [Ne, UpperHalfPlane.ext_iff, ← OnePoint.coe_eq_coe, toOnePoint_smul hdet,
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

def Matrix.GeneralLinearGroup.ellipticFixedPoint (g : GL (Fin 2) ℝ) : ℍ :=
  .ofComplex ( (g 0 0 - g 1 1) / (2 * g 1 0)
      + I * Real.sqrt ( -( (g 0 0 - g 1 1) ^ 2 + 4 * g 1 0 * g 0 1) / (4 * g 1 0 ^ 2) ))

lemma Matrix.GeneralLinearGroup.IsElliptic.coe_ellipticFixedPoint {g : GL (Fin 2) ℝ}
    (hg : g.IsElliptic) : (g.ellipticFixedPoint : ℂ) = ( (g 0 0 - g 1 1) / (2 * g 1 0)
      + I * Real.sqrt ( -((g 0 0 - g 1 1) ^ 2 + 4 * g 1 0 * g 0 1) / (4 * g 1 0 ^ 2) )) := by
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
  suffices ∀ {g : GL (Fin 2) ℝ} (hg : g.IsElliptic) (hc : 0 < g 1 0) (τ : ℍ),
      g.fixpointPolynomial.aeval (τ : ℂ) = 0 ↔ τ = g.ellipticFixedPoint by
    rcases hg.c_ne_zero.gt_or_lt with hc | hc
    · exact this hg hc τ
    · convert this (g := -g) ?_ (by simpa using hc) τ using 1
      · simp [fixpointPolynomial]
        grind
      · simp only [ellipticFixedPoint, coe_I, Units.val_neg, neg_apply, Complex.ofReal_neg]
        grind
      · simpa [IsElliptic, Matrix.IsElliptic, discr_fin_two, det_neg] using hg
  intro g hg hc τ
  let D := -((g 0 0 - g 1 1) ^ 2 + 4 * g 1 0 * g 0 1)
  have hD : 0 < D := by
    simp [IsElliptic, Matrix.IsElliptic, discr_fin_two, det_fin_two, trace_fin_two] at hg
    grind
  have : g.val.discr = -D := by grind [discr_fin_two, trace_fin_two, det_fin_two]
  have := quadratic_eq_zero_iff (a := (g 1 0 : ℂ)) (b := (g 1 1 - g 0 0 : ℂ)) (c := -g 0 1)
    (s := I * Real.sqrt D) (by simpa using hg.c_ne_zero) ?_ (τ : ℂ)
  · rw [← pow_two, ← sub_eq_add_neg] at this
    simp only [fixpointPolynomial, Fin.isValue, map_sub, map_add, map_mul, UpperHalfPlane.ext_iff,
      Polynomial.aeval_C, Complex.coe_algebraMap, map_pow, Polynomial.aeval_X, this, neg_sub, coe_I,
      hg.coe_ellipticFixedPoint, add_div]
    change _ ↔ (τ : ℂ) = _ + _ * ↑(√(D / _))
    simp_rw [Real.sqrt_div hD.le, Complex.ofReal_div, Real.sqrt_mul (show 0 ≤ 4 by norm_num),
      (show (4 : ℝ) = 2 ^ 2 by norm_num), Real.sqrt_sq hc.le, mul_div_assoc,
      Complex.ofReal_mul, Real.sqrt_sq two_pos.le, Complex.ofReal_ofNat]
    apply or_iff_left
    apply_fun Complex.im
    refine (lt_of_le_of_lt ?_ τ.im_pos).ne'
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

end
