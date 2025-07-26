/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.Probability.Distributions.Fernique
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.Moments.Covariance

/-!
# Fernique's theorem for Gaussian measures

## Main definitions

* `IsGaussian`

## Main statements

* `fooBar_unique`

## References

* [Martin Hairer, *An introduction to stochastic PDEs*][hairer2009introduction]

-/

open MeasureTheory ProbabilityTheory Complex NormedSpace
open scoped ENNReal NNReal Real Topology

section Aux

lemma two_mul_le_add_mul_sq {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {a b ε : R} (hε : 0 < ε) :
    2 * a * b ≤ ε * a ^ 2 + ε⁻¹ * b ^ 2 := by
  have h : 2 * (ε * a) * b ≤ (ε * a) ^ 2 + b ^ 2 := two_mul_le_add_sq (ε * a) b
  calc 2 * a * b
  _ = (2 * (ε * a) * b) / ε := by field_simp; ring
  _ ≤ ((ε * a) ^ 2 + b ^ 2) / ε := by gcongr
  _ = ε * a ^ 2 + ε⁻¹ * b ^ 2 := by field_simp; ring

end Aux

namespace ProbabilityTheory

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
  {μ : Measure E} [IsGaussian μ] {ν : Measure F} [IsGaussian ν]

section Prod

omit [BorelSpace F] in
lemma memLp_comp_inl_prod (L : Dual ℝ (E × F)) {p : ℝ≥0∞} (hp : p ≠ ∞) :
    MemLp (fun x ↦ (L.comp (.inl ℝ E F) x.1)) p (μ.prod ν) :=
  (IsGaussian.memLp_dual μ (L.comp (.inl ℝ E F)) p hp).comp_fst ν

omit [BorelSpace E] in
lemma memLp_comp_inr_prod (L : Dual ℝ (E × F)) {p : ℝ≥0∞} (hp : p ≠ ∞) :
    MemLp (fun x ↦ (L.comp (.inr ℝ E F) x.2)) p (μ.prod ν) :=
  (IsGaussian.memLp_dual ν (L.comp (.inr ℝ E F)) p hp).comp_snd μ

lemma memLp_dual_prod (L : Dual ℝ (E × F)) {p : ℝ≥0∞} (hp : p ≠ ∞) :
    MemLp L p (μ.prod ν) := by
  suffices MemLp (fun v ↦ L.comp (.inl ℝ E F) v.1 + L.comp (.inr ℝ E F) v.2) p (μ.prod ν) by
    simp_rw [L.comp_inl_add_comp_inr] at this
    exact this
  exact (memLp_comp_inl_prod L hp).add (memLp_comp_inr_prod L hp)

omit [BorelSpace F] in
lemma integrable_comp_inl_prod (L : Dual ℝ (E × F)) :
    Integrable (fun x ↦ (L.comp (.inl ℝ E F) x.1)) (μ.prod ν) :=
  memLp_one_iff_integrable.mp (memLp_comp_inl_prod L (by simp))

omit [BorelSpace E] in
lemma integrable_comp_inr_prod (L : Dual ℝ (E × F)) :
    Integrable (fun x ↦ (L.comp (.inr ℝ E F) x.2)) (μ.prod ν) :=
  memLp_one_iff_integrable.mp (memLp_comp_inr_prod L (by simp))

lemma integral_dual_prod (L : Dual ℝ (E × F)) :
    (μ.prod ν)[L] = μ[L.comp (.inl ℝ E F)] + ν[L.comp (.inr ℝ E F)] := by
  simp_rw [← L.comp_inl_add_comp_inr]
  rw [integral_add (integrable_comp_inl_prod L) (integrable_comp_inr_prod L),
    integral_prod _ (integrable_comp_inl_prod L), integral_prod _ (integrable_comp_inr_prod L)]
  simp

lemma variance_dual_prod (L : Dual ℝ (E × F)) :
    Var[L; μ.prod ν] = Var[L.comp (.inl ℝ E F); μ] + Var[L.comp (.inr ℝ E F); ν] := by
  rw [variance_def' (memLp_dual_prod L (by simp)), integral_dual_prod L,
    variance_def' (IsGaussian.memLp_dual _ _ _ (by simp)),
    variance_def' (IsGaussian.memLp_dual _ _ _ (by simp))]
  let L₁ := L.comp (.inl ℝ E F)
  let L₂ := L.comp (.inr ℝ E F)
  simp only [Pi.pow_apply]
  suffices h_sq : ∫ v, L v ^ 2 ∂(μ.prod ν)
      = ∫ x, L₁ x ^ 2 ∂μ + ∫ x, L₂ x ^ 2 ∂ν + 2 * μ[L₁] * ν[L₂] by rw [h_sq]; ring
  calc ∫ v, L v ^ 2 ∂μ.prod ν
  _ = ∫ v, (L₁ v.1 + L₂ v.2) ^ 2 ∂μ.prod ν := by simp_rw [← L.comp_inl_add_comp_inr]; simp [L₁, L₂]
  _ = ∫ v, L₁ v.1 ^ 2 + L₂ v.2 ^ 2 + 2 * L₁ v.1 * L₂ v.2 ∂μ.prod ν := by congr with v; ring
  _ = ∫ v, L₁ v.1 ^ 2 ∂μ.prod ν + ∫ v, L₂ v.2 ^ 2 ∂μ.prod ν
      + 2 * ∫ v, L₁ v.1 * L₂ v.2 ∂μ.prod ν := by
    have h_int1 : Integrable (fun a ↦ L₁ a.1 ^ 2) (μ.prod ν) :=
      (memLp_comp_inl_prod L (by simp)).integrable_sq
    have h_int2 : Integrable (fun a ↦ L₂ a.2 ^ 2) (μ.prod ν) :=
      (memLp_comp_inr_prod L (by simp)).integrable_sq
    rw [integral_add (h_int1.add'' h_int2), integral_add h_int1 h_int2]
    · simp_rw [mul_assoc]
      rw [integral_const_mul]
    · simp_rw [mul_assoc]
      refine Integrable.const_mul ?_ _
      exact (memLp_comp_inl_prod L (by simp)).integrable_mul (memLp_comp_inr_prod L (by simp))
        (p := 2) (q := 2)
  _ = ∫ x, L₁ x ^ 2 ∂μ + ∫ x, L₂ x ^ 2 ∂ν + 2 * μ[L₁] * ν[L₂] := by
    simp_rw [mul_assoc]
    congr
    · have : μ = (μ.prod ν).map (fun p ↦ p.1) := by simp
      conv_rhs => rw [this]
      rw [integral_map (by fun_prop) (by fun_prop)]
    · have : ν = (μ.prod ν).map (fun p ↦ p.2) := by simp
      conv_rhs => rw [this]
      rw [integral_map (by fun_prop) (by fun_prop)]
    · rw [integral_prod_mul]

/-- A product of Gaussian distributions is Gaussian. -/
instance [SecondCountableTopologyEither E F] : IsGaussian (μ.prod ν) := by
  refine isGaussian_of_charFunDual_eq fun L ↦ ?_
  rw [charFunDual_prod, IsGaussian.charFunDual_eq, IsGaussian.charFunDual_eq, ← Complex.exp_add]
  congr
  let L₁ := L.comp (.inl ℝ E F)
  let L₂ := L.comp (.inr ℝ E F)
  suffices μ[L₁] * I - Var[L₁; μ] / 2 + (ν[L₂] * I - Var[L₂; ν] / 2)
      = (μ.prod ν)[L] * I - Var[L; μ.prod ν] / 2 by convert this
  rw [sub_add_sub_comm, ← add_mul]
  congr
  · simp_rw [integral_complex_ofReal]
    rw [integral_dual_prod L]
    norm_cast
  · field_simp
    rw [variance_dual_prod]
    norm_cast

end Prod

section Rotation

/-- The hypothesis `∀ L : Dual ℝ E, μ[L] = 0` can be simplified to `μ[id] = 0`, but at this point
we don't know yet that `μ` has a first moment. -/
lemma IsGaussian.charFunDual_eq_of_isCentered (hμ : ∀ L : Dual ℝ E, μ[L] = 0) (L : Dual ℝ E) :
    charFunDual μ L = cexp (- Var[L; μ] / 2) := by
  rw [IsGaussian.charFunDual_eq L, integral_complex_ofReal, hμ L]
  simp [neg_div]

lemma IsGaussian.map_rotation_eq_self [SecondCountableTopology E] [CompleteSpace E]
    (hμ : ∀ L : Dual ℝ E, μ[L] = 0) (θ : ℝ) :
    (μ.prod μ).map (ContinuousLinearMap.rotation θ) = μ.prod μ := by
  refine Measure.ext_of_charFunDual ?_
  ext L
  rw [charFunDual_map, charFunDual_prod, IsGaussian.charFunDual_eq_of_isCentered hμ,
    IsGaussian.charFunDual_eq_of_isCentered hμ, ← Complex.exp_add, charFunDual_prod,
    IsGaussian.charFunDual_eq_of_isCentered hμ, IsGaussian.charFunDual_eq_of_isCentered hμ,
    ← Complex.exp_add]
  rw [← add_div, ← add_div, ← neg_add, ← neg_add]
  congr 3
  norm_cast
  change Var[(L.comp (.rotation θ)).comp (.inl ℝ E E); μ]
        + Var[(L.comp (.rotation θ)).comp (.inr ℝ E E); μ]
      = Var[L.comp (.inl ℝ E E); μ] + Var[L.comp (.inr ℝ E E); μ]
  have h1 : (L.comp (.rotation θ)).comp (.inl ℝ E E)
      = Real.cos θ • L.comp (.inl ℝ E E) - Real.sin θ • L.comp (.inr ℝ E E) := by
    ext x
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.rotation_apply, smul_zero, add_zero]
    rw [← L.comp_inl_add_comp_inr]
    simp [- neg_smul, sub_eq_add_neg]
  have h2 : (L.comp (.rotation θ)).comp (.inr ℝ E E)
      = Real.sin θ • L.comp (.inl ℝ E E) + Real.cos θ • L.comp (.inr ℝ E E) := by
    ext x
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.inr_apply,
      ContinuousLinearMap.rotation_apply, smul_zero, zero_add, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.inl_apply, smul_eq_mul]
    rw [← L.comp_inl_add_comp_inr]
    simp
  rw [h1, h2, ← covariance_self (by fun_prop), ← covariance_self (by fun_prop),
    ← covariance_self (by fun_prop), ← covariance_self (by fun_prop)]
  simp only [ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_add']
  rw [covariance_sub_left, covariance_sub_right, covariance_sub_right,
    covariance_add_left, covariance_add_right, covariance_add_right]
  rotate_left
  · exact IsGaussian.memLp_dual _ _ _ (by simp)
  · exact IsGaussian.memLp_dual _ _ _ (by simp)
  · exact IsGaussian.memLp_dual _ _ _ (by simp)
  · exact IsGaussian.memLp_dual _ _ _ (by simp)
  · exact IsGaussian.memLp_dual _ _ _ (by simp)
  · exact IsGaussian.memLp_dual _ _ _ (by simp)
  · exact IsGaussian.memLp_dual _ _ _ (by simp)
  · exact IsGaussian.memLp_dual _ _ _ (by simp)
  · exact (IsGaussian.memLp_dual _ _ _ (by simp)).add (IsGaussian.memLp_dual _ _ _ (by simp))
  · exact IsGaussian.memLp_dual _ _ _ (by simp)
  · exact IsGaussian.memLp_dual _ _ _ (by simp)
  · exact IsGaussian.memLp_dual _ _ _ (by simp)
  · exact IsGaussian.memLp_dual _ _ _ (by simp)
  · exact IsGaussian.memLp_dual _ _ _ (by simp)
  · exact IsGaussian.memLp_dual _ _ _ (by simp)
  · exact IsGaussian.memLp_dual _ _ _ (by simp)
  · exact IsGaussian.memLp_dual _ _ _ (by simp)
  · exact (IsGaussian.memLp_dual _ _ _ (by simp)).sub (IsGaussian.memLp_dual _ _ _ (by simp))
  simp only [ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp', covariance_smul_right,
    covariance_smul_left]
  have h := Real.cos_sq_add_sin_sq θ
  grind

end Rotation

section Fernique

variable [SecondCountableTopology E]

lemma integral_dual_conv_map_neg_eq_zero (L : Dual ℝ E) :
    (μ ∗ (μ.map (ContinuousLinearEquiv.neg ℝ)))[L] = 0 := by
  rw [integral_conv (by fun_prop)]
  simp only [map_add]
  calc ∫ x, ∫ y, L x + L y ∂μ.map (ContinuousLinearEquiv.neg ℝ) ∂μ
  _ = ∫ x, L x + ∫ y, L y ∂μ.map (ContinuousLinearEquiv.neg ℝ) ∂μ := by
    congr with x
    rw [integral_add (by fun_prop) (by fun_prop)]
    simp [- ContinuousLinearEquiv.coe_neg, integral_const, smul_eq_mul]
  _ = ∫ x, L x ∂μ + ∫ y, L y ∂μ.map (ContinuousLinearEquiv.neg ℝ) := by
    rw [integral_add (by fun_prop) (by fun_prop)]
    simp
  _ = 0 := by
    rw [integral_map (by fun_prop) (by fun_prop)]
    simp [integral_neg]

/-- **Fernique's theorem**: for a Gaussian measure, there exists `C > 0` such that the function
`x ↦ exp (C * ‖x‖ ^ 2)` is integrable. -/
theorem IsGaussian.exists_integrable_exp_sq [CompleteSpace E] (μ : Measure E) [IsGaussian μ] :
    ∃ C, 0 < C ∧ Integrable (fun x ↦ rexp (C * ‖x‖ ^ 2)) μ := by
  -- Since `μ ∗ μ.map (ContinuousLinearEquiv.neg ℝ)` is a centered Gaussian measure, it is invariant
  -- under rotation. We can thus apply a version of Fernique's theorem to it.
  obtain ⟨C, hC_pos, hC⟩ : ∃ C, 0 < C
      ∧ Integrable (fun x ↦ rexp (C * ‖x‖ ^ 2)) (μ ∗ μ.map (ContinuousLinearEquiv.neg ℝ)) :=
    exists_integrable_exp_sq_of_map_rotation_eq_self
      (map_rotation_eq_self (integral_dual_conv_map_neg_eq_zero (μ := μ)) _)
  -- We must now prove that the integrability with respect to
  -- `μ ∗ μ.map (ContinuousLinearEquiv.neg ℝ)` implies integrability with respect to `μ` for
  -- another constant `C' < C`.
  have h_int : ∀ᵐ y ∂μ, Integrable (fun x ↦ rexp (C * ‖x - y‖^2)) μ := by
    rw [integrable_conv_iff (by fun_prop)] at hC
    replace hC := hC.1
    simp only [ContinuousLinearEquiv.coe_neg] at hC
    filter_upwards [hC] with y hy
    rw [integrable_map_measure (by fun_prop) (by fun_prop)] at hy
    convert hy with x
    simp only [Function.comp_apply, Pi.neg_apply, id_eq, Real.exp_eq_exp, mul_eq_mul_left_iff,
      norm_nonneg, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_left_inj₀]
    left
    simp_rw [← sub_eq_add_neg, norm_sub_rev]
  obtain ⟨y, hy⟩ : ∃ y, Integrable (fun x ↦ rexp (C * ‖x - y‖ ^ 2)) μ := h_int.exists
  obtain ⟨C', hC'_pos, hC'_lt⟩ : ∃ C', 0 < C' ∧ C' < C := ⟨C / 2, by positivity, by simp [hC_pos]⟩
  refine ⟨C', hC'_pos, ?_⟩
  let ε := (C - C') / C'
  have hε : 0 < ε := div_pos (by rwa [sub_pos]) (by positivity)
  suffices ∀ x, rexp (C' * ‖x‖ ^ 2) ≤ rexp (C/ε * ‖y‖ ^ 2) * rexp (C * ‖x - y‖ ^ 2) by
    refine integrable_of_le_of_le (g₁ := 0)
      (g₂ := fun x ↦ rexp (C/ε * ‖y‖ ^ 2) * rexp (C * ‖x - y‖ ^ 2)) (by fun_prop) ?_ ?_
      (integrable_const _) (hy.const_mul _)
    · exact ae_of_all _ fun _ ↦ by positivity
    · exact ae_of_all _ this
  intro x
  rw [← Real.exp_add]
  gcongr -- `⊢ C' * ‖x‖ ^ 2 ≤ C / ε * ‖y‖ ^ 2 + C * ‖x - y‖ ^ 2`
  have h_le : ‖x‖ ^ 2 ≤ (1 + ε) * ‖x - y‖ ^ 2 + (1 + 1 / ε) * ‖y‖ ^ 2 := by
    calc ‖x‖ ^ 2
    _ = ‖x - y + y‖ ^ 2 := by simp
    _ ≤ (‖x - y‖  + ‖y‖) ^ 2 := by gcongr; exact norm_add_le (x - y) y
    _ = ‖x - y‖ ^ 2 + ‖y‖ ^ 2 + 2 * ‖x - y‖ * ‖y‖ := by ring
    _ ≤ ‖x - y‖ ^ 2 + ‖y‖ ^ 2 + ε * ‖x - y‖ ^ 2 + ε⁻¹ * ‖y‖ ^ 2 := by
      simp_rw [add_assoc]
      gcongr
      exact two_mul_le_add_mul_sq (by positivity)
    _ = (1 + ε) * ‖x - y‖ ^ 2 + (1 + 1 / ε) * ‖y‖ ^ 2 := by ring
  calc C' * ‖x‖ ^ 2
  _ ≤ C' * ((1 + ε) * ‖x - y‖ ^ 2 + (1 + 1 / ε) * ‖y‖ ^ 2) := by gcongr
  _ = (C' * (1 + 1 / ε)) * ‖y‖ ^ 2 + (C' * (1 + ε)) * ‖x - y‖ ^ 2 := by ring
  _ = C / ε * ‖y‖ ^ 2 + C * ‖x - y‖ ^ 2 := by
    unfold ε
    congr 2
    · simp only [one_div, inv_div]
      rw [one_add_div (by rw [sub_ne_zero]; exact hC'_lt.ne'), div_div_eq_mul_div]
      simp only [sub_add_cancel]
      ring
    · rw [one_add_div (by positivity)]
      simp only [add_sub_cancel]
      rw [mul_div_cancel₀ _ (by positivity)]

end Fernique

section FiniteMoments

variable [CompleteSpace E] [SecondCountableTopology E]

/-- A Gaussian measure has moments of all orders.
That is, the identity is in Lp for all finite `p`. -/
lemma IsGaussian.memLp_id (μ : Measure E) [IsGaussian μ] (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp id p μ := by
  suffices MemLp (fun x ↦ ‖x‖ ^ 2) (p / 2) μ by
    rw [← memLp_norm_rpow_iff (q := 2) _ (by simp) (by simp)]
    · simpa using this
    · fun_prop
  lift p to ℝ≥0 using hp
  convert memLp_of_mem_interior_integrableExpSet ?_ (p / 2)
  · simp
  obtain ⟨C, hC_pos, hC⟩ := exists_integrable_exp_sq μ
  have hC_neg : Integrable (fun x ↦ rexp (-C * ‖x‖ ^ 2)) μ := by -- `-C` could be any negative
    refine integrable_of_le_of_le (g₁ := 0) (g₂ := 1) (by fun_prop)
      (ae_of_all _ fun _ ↦ by positivity) ?_ (integrable_const _) (integrable_const _)
    refine ae_of_all _ fun x ↦ ?_
    simp only [neg_mul, Pi.one_apply, Real.exp_le_one_iff, Left.neg_nonpos_iff]
    positivity
  have h_subset : Set.Ioo (-C) C ⊆ interior (integrableExpSet (fun x ↦ ‖x‖ ^ 2) μ) := by
    rw [IsOpen.subset_interior_iff isOpen_Ioo]
    exact fun x hx ↦ integrable_exp_mul_of_le_of_le hC_neg hC hx.1.le hx.2.le
  exact h_subset ⟨by simp [hC_pos], hC_pos⟩

lemma IsGaussian.integral_dual (L : Dual ℝ E) : μ[L] = L (∫ x, x ∂μ) :=
  L.integral_comp_comm ((IsGaussian.memLp_id μ 1 (by simp)).integrable le_rfl)

lemma IsGaussian.eq_dirac_of_variance_eq_zero (h : ∀ L : Dual ℝ E, Var[L; μ] = 0) :
    μ = Measure.dirac (∫ x, x ∂μ) := by
  refine Measure.ext_of_charFunDual ?_
  ext L
  rw [charFunDual_dirac, IsGaussian.charFunDual_eq L, h L, integral_complex_ofReal,
    IsGaussian.integral_dual L]
  simp

lemma IsGaussian.noAtoms (h : ∀ x, μ ≠ Measure.dirac x) : NoAtoms μ where
  measure_singleton x := by
    obtain ⟨L, hL⟩ : ∃ L : Dual ℝ E, Var[L; μ] ≠ 0 := by
      contrapose! h
      exact ⟨_, eq_dirac_of_variance_eq_zero h⟩
    have hL_zero : μ.map L {L x} = 0 := by
      have : NoAtoms (μ.map L) := by
        rw [IsGaussian.map_eq_gaussianReal L]
        refine noAtoms_gaussianReal ?_
        simp only [ne_eq, Real.toNNReal_eq_zero, not_le]
        exact lt_of_le_of_ne (variance_nonneg _ _) hL.symm
      rw [measure_singleton]
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)] at hL_zero
    refine measure_mono_null ?_ hL_zero
    exact fun ⦃a⦄ ↦ congrArg ⇑L

end FiniteMoments

end ProbabilityTheory
