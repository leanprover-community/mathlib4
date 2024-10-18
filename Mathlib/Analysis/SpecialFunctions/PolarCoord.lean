/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Polar coordinates

We define polar coordinates, as a partial homeomorphism in `ℝ^2` between `ℝ^2 - (-∞, 0]` and
`(0, +∞) × (-π, π)`. Its inverse is given by `(r, θ) ↦ (r cos θ, r sin θ)`.

It satisfies the following change of variables formula (see `integral_comp_polarCoord_symm`):
`∫ p in polarCoord.target, p.1 • f (polarCoord.symm p) = ∫ p, f p`

-/

noncomputable section Real

open Real Set MeasureTheory

open scoped Real Topology

/-- The polar coordinates partial homeomorphism in `ℝ^2`, mapping `(r cos θ, r sin θ)` to `(r, θ)`.
It is a homeomorphism between `ℝ^2 - (-∞, 0]` and `(0, +∞) × (-π, π)`. -/
@[simps]
def polarCoord : PartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) where
  toFun q := (√(q.1 ^ 2 + q.2 ^ 2), Complex.arg (Complex.equivRealProd.symm q))
  invFun p := (p.1 * cos p.2, p.1 * sin p.2)
  source := {q | 0 < q.1} ∪ {q | q.2 ≠ 0}
  target := Ioi (0 : ℝ) ×ˢ Ioo (-π) π
  map_target' := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    dsimp at hr hθ
    rcases eq_or_ne θ 0 with (rfl | h'θ)
    · simpa using hr
    · right
      simp at hr
      simpa only [ne_of_gt hr, Ne, mem_setOf_eq, mul_eq_zero, false_or,
        sin_eq_zero_iff_of_lt_of_lt hθ.1 hθ.2] using h'θ
  map_source' := by
    rintro ⟨x, y⟩ hxy
    simp only [prod_mk_mem_set_prod_eq, mem_Ioi, sqrt_pos, mem_Ioo, Complex.neg_pi_lt_arg,
      true_and, Complex.arg_lt_pi_iff]
    constructor
    · cases' hxy with hxy hxy
      · dsimp at hxy; linarith [sq_pos_of_ne_zero hxy.ne', sq_nonneg y]
      · linarith [sq_nonneg x, sq_pos_of_ne_zero hxy]
    · cases' hxy with hxy hxy
      · exact Or.inl (le_of_lt hxy)
      · exact Or.inr hxy
  right_inv' := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    dsimp at hr hθ
    simp only [Prod.mk.inj_iff]
    constructor
    · conv_rhs => rw [← sqrt_sq (le_of_lt hr), ← one_mul (r ^ 2), ← sin_sq_add_cos_sq θ]
      congr 1
      ring
    · convert Complex.arg_mul_cos_add_sin_mul_I hr ⟨hθ.1, hθ.2.le⟩
      simp only [Complex.equivRealProd_symm_apply, Complex.ofReal_mul, Complex.ofReal_cos,
        Complex.ofReal_sin]
      ring
  left_inv' := by
    rintro ⟨x, y⟩ _
    have A : √(x ^ 2 + y ^ 2) = Complex.abs (x + y * Complex.I) := by
      rw [Complex.abs_apply, Complex.normSq_add_mul_I]
    have Z := Complex.abs_mul_cos_add_sin_mul_I (x + y * Complex.I)
    simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, mul_add, ← Complex.ofReal_mul, ←
      mul_assoc] at Z
    simp [A]
  open_target := isOpen_Ioi.prod isOpen_Ioo
  open_source :=
    (isOpen_lt continuous_const continuous_fst).union
      (isOpen_ne_fun continuous_snd continuous_const)
  continuousOn_invFun :=
    ((continuous_fst.mul (continuous_cos.comp continuous_snd)).prod_mk
        (continuous_fst.mul (continuous_sin.comp continuous_snd))).continuousOn
  continuousOn_toFun := by
    apply ((continuous_fst.pow 2).add (continuous_snd.pow 2)).sqrt.continuousOn.prod
    have A : MapsTo Complex.equivRealProd.symm ({q : ℝ × ℝ | 0 < q.1} ∪ {q : ℝ × ℝ | q.2 ≠ 0})
        Complex.slitPlane := by
      rintro ⟨x, y⟩ hxy; simpa only using hxy
    refine ContinuousOn.comp (f := Complex.equivRealProd.symm)
      (g := Complex.arg) (fun z hz => ?_) ?_ A
    · exact (Complex.continuousAt_arg hz).continuousWithinAt
    · exact Complex.equivRealProdCLM.symm.continuous.continuousOn

theorem measurable_polarCoord :
    Measurable (polarCoord) :=
  Measurable.prod_mk (by fun_prop) Complex.measurableEquivRealProd.symm.measurable.carg

theorem continuous_polarCoord_symm :
    Continuous (polarCoord.symm) :=
  Continuous.prod_mk (by fun_prop) (by fun_prop)

theorem hasFDerivAt_polarCoord_symm (p : ℝ × ℝ) :
    HasFDerivAt polarCoord.symm
      (LinearMap.toContinuousLinearMap (Matrix.toLin (Basis.finTwoProd ℝ) (Basis.finTwoProd ℝ)
        !![cos p.2, -p.1 * sin p.2; sin p.2, p.1 * cos p.2])) p := by
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  convert HasFDerivAt.prod (𝕜 := ℝ)
    (hasFDerivAt_fst.mul ((hasDerivAt_cos p.2).comp_hasFDerivAt p hasFDerivAt_snd))
    (hasFDerivAt_fst.mul ((hasDerivAt_sin p.2).comp_hasFDerivAt p hasFDerivAt_snd)) using 2 <;>
  simp [smul_smul, add_comm, neg_mul, smul_neg, neg_smul _ (ContinuousLinearMap.snd ℝ ℝ ℝ)]

theorem FDerivAt_polarCoord_symm_det (p : ℝ × ℝ) :
    (LinearMap.toContinuousLinearMap (Matrix.toLin (Basis.finTwoProd ℝ) (Basis.finTwoProd ℝ)
      !![cos p.2, -p.1 * sin p.2; sin p.2, p.1 * cos p.2])).det = p.1 := by
  conv_rhs => rw [← one_mul p.1, ← cos_sq_add_sin_sq p.2]
  simp only [neg_mul, LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin,
    Matrix.det_fin_two_of, sub_neg_eq_add]
  ring

-- Porting note: this instance is needed but not automatically synthesised
instance : Measure.IsAddHaarMeasure volume (G := ℝ × ℝ) :=
  Measure.prod.instIsAddHaarMeasure _ _

theorem polarCoord_source_ae_eq_univ : polarCoord.source =ᵐ[volume] univ := by
  have A : polarCoord.sourceᶜ ⊆ LinearMap.ker (LinearMap.snd ℝ ℝ ℝ) := by
    intro x hx
    simp only [polarCoord_source, compl_union, mem_inter_iff, mem_compl_iff, mem_setOf_eq, not_lt,
      Classical.not_not] at hx
    exact hx.2
  have B : volume (LinearMap.ker (LinearMap.snd ℝ ℝ ℝ) : Set (ℝ × ℝ)) = 0 := by
    apply Measure.addHaar_submodule
    rw [Ne, LinearMap.ker_eq_top]
    intro h
    have : (LinearMap.snd ℝ ℝ ℝ) (0, 1) = (0 : ℝ × ℝ →ₗ[ℝ] ℝ) (0, 1) := by rw [h]
    simp at this
  simp only [ae_eq_univ]
  exact le_antisymm ((measure_mono A).trans (le_of_eq B)) bot_le

theorem integral_comp_polarCoord_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ × ℝ → E) :
    (∫ p in polarCoord.target, p.1 • f (polarCoord.symm p)) = ∫ p, f p := by
  symm
  calc
    ∫ p, f p = ∫ p in polarCoord.source, f p := by
      rw [← setIntegral_univ]
      apply setIntegral_congr_set
      exact polarCoord_source_ae_eq_univ.symm
    _ = ∫ p in polarCoord.target, |p.1| • f (polarCoord.symm p) := by
      rw [← PartialHomeomorph.symm_target, integral_target_eq_integral_abs_det_fderiv_smul volume
        (fun p _ ↦ hasFDerivAt_polarCoord_symm p), PartialHomeomorph.symm_source]
      simp_rw [FDerivAt_polarCoord_symm_det]
    _ = ∫ p in polarCoord.target, p.1 • f (polarCoord.symm p) := by
      apply setIntegral_congr_fun polarCoord.open_target.measurableSet fun x hx => ?_
      rw [abs_of_pos]
      exact hx.1

theorem lintegral_comp_polarCoord_symm (f : ℝ × ℝ → ENNReal) :
    ∫⁻ (p : ℝ × ℝ) in polarCoord.target, (p.1).toNNReal • f (polarCoord.symm p) =
      ∫⁻ (p : ℝ × ℝ), f p := by
  symm
  calc
    _ = ∫⁻ p in polarCoord.symm '' polarCoord.target, f p := by
      rw [← setLIntegral_univ, setLIntegral_congr polarCoord_source_ae_eq_univ.symm,
        polarCoord.symm_image_target_eq_source ]
    _ = ∫⁻ (p : ℝ × ℝ) in polarCoord.target, |p.1|.toNNReal • f (polarCoord.symm p) := by
      rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume _
        (fun p _ ↦ (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt)]
      simp_rw [FDerivAt_polarCoord_symm_det]; rfl
      exacts [polarCoord.symm.injOn, measurableSet_Ioi.prod measurableSet_Ioo]
    _ = ∫⁻ (p : ℝ × ℝ) in polarCoord.target, (p.1).toNNReal • f (polarCoord.symm p) := by
      refine setLIntegral_congr_fun polarCoord.open_target.measurableSet ?_
      filter_upwards with _ hx using by rw [abs_of_pos (by convert hx.1)]

end Real

noncomputable section Complex

namespace Complex

open scoped Real

/-- The polar coordinates partial homeomorphism in `ℂ`, mapping `r (cos θ + I * sin θ)` to `(r, θ)`.
It is a homeomorphism between `ℂ - ℝ≤0` and `(0, +∞) × (-π, π)`. -/
protected noncomputable def polarCoord : PartialHomeomorph ℂ (ℝ × ℝ) :=
  equivRealProdCLM.toHomeomorph.transPartialHomeomorph polarCoord

protected theorem measurable_polarCoord :
    Measurable (Complex.polarCoord) :=
  measurable_polarCoord.comp Complex.measurableEquivRealProd.measurable

protected theorem continuous_polarCoord_symm :
    Continuous (Complex.polarCoord.symm) :=
  equivRealProdCLM.symm.continuous.comp continuous_polarCoord_symm

protected theorem polarCoord_apply (a : ℂ) :
    Complex.polarCoord a = (Complex.abs a, Complex.arg a) := by
  simp_rw [Complex.abs_def, Complex.normSq_apply, ← pow_two]
  rfl

protected theorem polarCoord_source : Complex.polarCoord.source = slitPlane := rfl

protected theorem polarCoord_target :
    Complex.polarCoord.target = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π := rfl

@[simp]
protected theorem polarCoord_symm_apply (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = p.1 * (Real.cos p.2 + Real.sin p.2 * Complex.I) := by
  simp [Complex.polarCoord, equivRealProdCLM_symm_apply, mul_add, mul_assoc]

theorem polarCoord_symm_abs (p : ℝ × ℝ) :
    Complex.abs (Complex.polarCoord.symm p) = |p.1| := by simp

open scoped ComplexOrder

theorem polarCoord_symm_mem_polarCoord_source (x : ℝ × ℝ) :
    Complex.polarCoord.symm x ∈ Complex.polarCoord.source ↔
        x.1 ≠ 0 ∧ (x.1 > 0 → ∀ k : ℤ, π + k * (2 * π) ≠ x.2) ∧
          (x.1 < 0 →  ∀ k : ℤ, k * (2 * π) ≠ x.2) := by
  simp_rw (config := {singlePass := true}) [← not_iff_not, Complex.polarCoord_symm_apply,
    Complex.polarCoord_source, mem_slitPlane_iff_arg, not_and_or, ne_eq, not_not, mul_eq_zero,
    not_and_or, Classical.not_imp, not_forall, not_not, ofReal_eq_zero, ofReal_cos, ofReal_sin,
    cos_add_sin_I, exp_ne_zero, or_false]
  obtain hx | hx | hx := lt_trichotomy x.1 0
  · simp_rw [hx, hx.ne, not_lt_of_gt hx, false_and, false_or, true_and, or_false]
    have : (x.1 * cexp (x.2 * I)).arg = π ↔ (cexp (x.2 * I)).arg = 0 := by
      simp_rw [arg_eq_pi_iff_lt_zero, arg_eq_zero_iff_zero_le, ofReal_mul_neg_iff, hx,
        not_lt_of_gt hx, true_and, false_and, or_false, lt_iff_le_and_ne, ne_eq, eq_comm,
        exp_ne_zero, not_false_eq_true, and_true]
    simp_rw [this, arg_exp_mul_I, toIocMod_eq_iff, zero_add, zsmul_eq_mul, eq_comm,
      and_iff_right_iff_imp]
    exact fun _ ↦ ⟨neg_neg_iff_pos.mpr Real.pi_pos, by ring_nf; positivity⟩
  · simp_rw [hx, true_or, or_true]
  · simp_rw [hx, hx.ne', not_lt_of_gt hx, false_and, or_false, true_and, false_or, arg_real_mul _
      hx, arg_exp_mul_I, toIocMod_eq_iff, zsmul_eq_mul, eq_comm, and_iff_right_iff_imp]
    exact fun _ ↦ ⟨Left.neg_lt_self Real.pi_pos, by linarith⟩

@[deprecated (since := "2024-07-15")] alias polardCoord_symm_abs := polarCoord_symm_abs

protected theorem integral_comp_polarCoord_symm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℂ → E) :
    (∫ p in polarCoord.target, p.1 • f (Complex.polarCoord.symm p)) = ∫ p, f p := by
  rw [← (Complex.volume_preserving_equiv_real_prod.symm).integral_comp
    measurableEquivRealProd.symm.measurableEmbedding, ← integral_comp_polarCoord_symm]
  rfl

protected theorem lintegral_comp_polarCoord_symm (f : ℂ → ENNReal) (hf : Measurable f) :
    (∫⁻ p in polarCoord.target, (p.1).toNNReal • f (Complex.polarCoord.symm p)) = ∫⁻ p, f p := by
  rw [← (Complex.volume_preserving_equiv_real_prod.symm).lintegral_comp hf,
    ← lintegral_comp_polarCoord_symm]
  rfl

end Complex
