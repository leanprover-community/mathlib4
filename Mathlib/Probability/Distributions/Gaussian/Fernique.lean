/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Distributions.Fernique
public import Mathlib.Probability.Distributions.Gaussian.Basic

/-!
# Fernique's theorem for Gaussian measures

We show that the product of two identical Gaussian measures is invariant under rotation.
We then deduce Fernique's theorem, which states that for a Gaussian measure `μ`, there exists
`C > 0` such that the function `x ↦ exp (C * ‖x‖ ^ 2)` is integrable with respect to `μ`.
As a consequence, a Gaussian measure has finite moments of all orders.

## Main statements

* `IsGaussian.exists_integrable_exp_sq`: **Fernique's theorem**. For a Gaussian measure on a
  second-countable normed space, there exists `C > 0` such that the function
  `x ↦ exp (C * ‖x‖ ^ 2)` is integrable.
* `IsGaussian.memLp_id`: a Gaussian measure in a second-countable Banach space has finite moments
  of all orders.

## References

* [Martin Hairer, *An introduction to stochastic PDEs*][hairer2009introduction]

-/

public section

open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal NNReal Real Topology

namespace ProbabilityTheory.IsGaussian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsGaussian μ]

section Rotation

/-- Characteristic function of a centered Gaussian measure.
For a Gaussian measure, the hypothesis `∀ L : StrongDual ℝ E, μ[L] = 0` is equivalent to the simpler
`μ[id] = 0`, but at this point we don't know yet that `μ` has a first moment so we can't use it.
See `charFunDual_eq_of_integral_eq_zero` -/
lemma charFunDual_eq_of_forall_strongDual_eq_zero (hμ : ∀ L : StrongDual ℝ E, μ[L] = 0)
    (L : StrongDual ℝ E) :
    charFunDual μ L = exp (- Var[L; μ] / 2) := by
  simp [charFunDual_eq L, integral_complex_ofReal, hμ L, neg_div]

/-- For a centered Gaussian measure `μ`, the product measure `μ.prod μ` is invariant under rotation.
The hypothesis `∀ L : StrongDual ℝ E, μ[L] = 0` is equivalent to the simpler
`μ[id] = 0`, but at this point we don't know yet that `μ` has a first moment so we can't use it.
See `map_rotation_eq_self`. -/
lemma map_rotation_eq_self_of_forall_strongDual_eq_zero
    [SecondCountableTopology E] [CompleteSpace E]
    (hμ : ∀ L : StrongDual ℝ E, μ[L] = 0) (θ : ℝ) :
    (μ.prod μ).map (ContinuousLinearMap.rotation θ) = μ.prod μ := by
  refine Measure.ext_of_charFunDual ?_
  ext L
  simp_rw [charFunDual_map, charFunDual_prod, charFunDual_eq_of_forall_strongDual_eq_zero hμ,
    ← Complex.exp_add]
  rw [← add_div, ← add_div, ← neg_add, ← neg_add]
  congr 3
  norm_cast
  have h1 : (L.comp (.rotation θ)).comp (.inl ℝ E E)
      = Real.cos θ • L.comp (.inl ℝ E E) - Real.sin θ • L.comp (.inr ℝ E E) := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.rotation_apply, smul_zero, add_zero]
    rw [← L.comp_inl_add_comp_inr]
    simp [-neg_smul, sub_eq_add_neg]
  have h2 : (L.comp (.rotation θ)).comp (.inr ℝ E E)
      = Real.sin θ • L.comp (.inl ℝ E E) + Real.cos θ • L.comp (.inr ℝ E E) := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      ContinuousLinearMap.rotation_apply, smul_zero, zero_add, add_apply, smul_apply,
      ContinuousLinearMap.inl_apply, smul_eq_mul]
    rw [← L.comp_inl_add_comp_inr]
    simp
  rw [h1, h2]
  simp only [FunLike.coe_sub, FunLike.coe_smul,
    FunLike.coe_add]
  rw [variance_sub, variance_smul, variance_add, variance_smul, variance_smul, covariance_smul_left,
    covariance_smul_right, variance_smul, covariance_smul_left, covariance_smul_right]
  · have h := Real.cos_sq_add_sin_sq θ
    grind
  all_goals exact (memLp_dual _ _ _ two_ne_zero (by simp)).const_smul _

end Rotation

section Fernique

variable [SecondCountableTopology E]

/-- The convolution of a Gaussian measure `μ` and its map by `x ↦ -x` is centered. -/
lemma integral_dual_conv_map_neg_eq_zero (L : StrongDual ℝ E) :
    (μ ∗ (μ.map (ContinuousLinearEquiv.neg ℝ)))[L] = 0 := by
  rw [integral_conv (by fun_prop)]
  simp only [map_add]
  calc ∫ x, ∫ y, L x + L y ∂μ.map (ContinuousLinearEquiv.neg ℝ) ∂μ
  _ = ∫ x, L x + ∫ y, L y ∂μ.map (ContinuousLinearEquiv.neg ℝ) ∂μ := by
    congr with x
    rw [integral_add (by fun_prop) (by fun_prop)]
    simp [-ContinuousLinearEquiv.coe_neg, integral_const, smul_eq_mul]
  _ = ∫ x, L x ∂μ + ∫ y, L y ∂μ.map (ContinuousLinearEquiv.neg ℝ) := by
    rw [integral_add (by fun_prop) (by fun_prop)]
    simp
  _ = 0 := by
    rw [integral_map (by fun_prop) (by fun_prop)]
    simp [integral_neg]

/-- If `x ↦ exp (C * ‖x‖ ^ 2)` is integrable with respect to the centered Gaussian
`μ ∗ (μ.map (ContinuousLinearEquiv.neg ℝ))`, then for all `C' < C`, `x ↦ exp (C' * ‖x‖ ^ 2)`
is integrable with respect to `μ`. -/
lemma integrable_exp_sq_of_conv_neg (μ : Measure E) [IsGaussian μ] {C C' : ℝ}
    (hint : Integrable (fun x ↦ rexp (C * ‖x‖ ^ 2))
      (μ ∗ (μ.map (ContinuousLinearEquiv.neg ℝ))))
    (hC'_pos : 0 < C') (hC'_lt : C' < C) :
    Integrable (fun x ↦ rexp (C' * ‖x‖ ^ 2)) μ := by
  have h_int : ∀ᵐ y ∂μ, Integrable (fun x ↦ rexp (C * ‖x - y‖ ^ 2)) μ := by
    rw [integrable_conv_iff (by fun_prop)] at hint
    replace hC := hint.1
    simp only [ContinuousLinearEquiv.coe_neg] at hC
    filter_upwards [hC] with y hy
    rw [integrable_map_measure (by fun_prop) (by fun_prop)] at hy
    convert! hy with x
    simp only [Function.comp_apply, Pi.neg_apply, id_eq, Real.exp_eq_exp, mul_eq_mul_left_iff,
      norm_nonneg, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_left_inj₀]
    left
    simp_rw [← sub_eq_add_neg, norm_sub_rev]
  obtain ⟨y, hy⟩ : ∃ y, Integrable (fun x ↦ rexp (C * ‖x - y‖ ^ 2)) μ := h_int.exists
  let ε := (C - C') / C'
  have hε : 0 < ε := div_pos (by rwa [sub_pos]) (by positivity)
  suffices ∀ x, rexp (C' * ‖x‖ ^ 2) ≤ rexp (C / ε * ‖y‖ ^ 2) * rexp (C * ‖x - y‖ ^ 2) by
    refine integrable_of_le_of_le (g₁ := 0)
      (g₂ := fun x ↦ rexp (C / ε * ‖y‖ ^ 2) * rexp (C * ‖x - y‖ ^ 2)) (by fun_prop) ?_ ?_
      (integrable_const _) (hy.const_mul _)
    · exact ae_of_all _ fun _ ↦ by positivity
    · exact ae_of_all _ this
  intro x
  rw [← Real.exp_add]
  gcongr -- `⊢ C' * ‖x‖ ^ 2 ≤ C / ε * ‖y‖ ^ 2 + C * ‖x - y‖ ^ 2` with `ε = (C - C') / C'`
  have h_le : ‖x‖ ^ 2 ≤ (1 + ε) * ‖x - y‖ ^ 2 + (1 + 1 / ε) * ‖y‖ ^ 2 := by
    calc ‖x‖ ^ 2
    _ = ‖x - y + y‖ ^ 2 := by simp
    _ ≤ (‖x - y‖ + ‖y‖) ^ 2 := by grw [norm_add_le (x - y) y]
    _ = ‖x - y‖ ^ 2 + ‖y‖ ^ 2 + 2 * ‖x - y‖ * ‖y‖ := by ring
    _ ≤ ‖x - y‖ ^ 2 + ‖y‖ ^ 2 + ε * ‖x - y‖ ^ 2 + ε⁻¹ * ‖y‖ ^ 2 := by
      simp_rw [add_assoc]
      gcongr
      exact two_mul_le_add_mul_sq (by positivity)
    _ = (1 + ε) * ‖x - y‖ ^ 2 + (1 + 1 / ε) * ‖y‖ ^ 2 := by ring
  calc C' * ‖x‖ ^ 2
  _ ≤ C' * ((1 + ε) * ‖x - y‖ ^ 2 + (1 + 1 / ε) * ‖y‖ ^ 2) := by gcongr
  _ = C / ε * ‖y‖ ^ 2 + C * ‖x - y‖ ^ 2 := by grind

/-- **Fernique's theorem**: for a Gaussian measure, there exists `C > 0` such that the function
`x ↦ exp (C * ‖x‖ ^ 2)` is integrable. -/
theorem exists_integrable_exp_sq [CompleteSpace E] (μ : Measure E) [IsGaussian μ] :
    ∃ C, 0 < C ∧ Integrable (fun x ↦ rexp (C * ‖x‖ ^ 2)) μ := by
  -- Since `μ ∗ μ.map (ContinuousLinearEquiv.neg ℝ)` is a centered Gaussian measure, it is invariant
  -- under rotation. We can thus apply a version of Fernique's theorem to it.
  obtain ⟨C, hC_pos, hC⟩ : ∃ C, 0 < C
      ∧ Integrable (fun x ↦ rexp (C * ‖x‖ ^ 2)) (μ ∗ μ.map (ContinuousLinearEquiv.neg ℝ)) :=
    exists_integrable_exp_sq_of_map_rotation_eq_self
      (map_rotation_eq_self_of_forall_strongDual_eq_zero
        (integral_dual_conv_map_neg_eq_zero (μ := μ)) _)
  -- We must now prove that the integrability with respect to
  -- `μ ∗ μ.map (ContinuousLinearEquiv.neg ℝ)` implies integrability with respect to `μ` for
  -- another constant `C' < C`.
  refine ⟨C / 2, by positivity, ?_⟩
  exact integrable_exp_sq_of_conv_neg μ hC (by positivity) (by simp [hC_pos])

end Fernique

section FiniteMoments

variable [CompleteSpace E] [SecondCountableTopology E]

/-- A Gaussian measure has moments of all orders.
That is, the identity is in L^p for all finite `p`. -/
lemma memLp_id (μ : Measure E) [IsGaussian μ] (p : ℝ≥0∞) (hp0 : p ≠ 0) (hp : p ≠ ∞) :
    MemLp id p μ := by
  suffices MemLp (fun x ↦ ‖x‖ ^ 2) (p / 2) μ by
    rw [← memLp_norm_rpow_iff (q := 2) (by fun_prop) (by simp) (by simp)]
    simpa using this
  lift p to ℝ≥0 using hp
  have : p / 2 ≠ 0 := by simp [ENNReal.coe_ne_zero.mp hp0]
  convert! memLp_of_mem_interior_integrableExpSet ?_ this
  · simp
  obtain ⟨C, hC_pos, hC⟩ := exists_integrable_exp_sq μ
  have hC_neg : Integrable (fun x ↦ rexp (-C * ‖x‖ ^ 2)) μ := by -- `-C` could be any negative
    refine integrable_of_le_of_le (g₁ := 0) (g₂ := 1) (by fun_prop)
      (ae_of_all _ fun _ ↦ by positivity) ?_ (integrable_const _) (integrable_const _)
    filter_upwards with x
    simp only [neg_mul, Pi.one_apply, Real.exp_le_one_iff, Left.neg_nonpos_iff]
    positivity
  have h_subset : Set.Ioo (-C) C ⊆ interior (integrableExpSet (fun x ↦ ‖x‖ ^ 2) μ) := by
    rw [IsOpen.subset_interior_iff isOpen_Ioo]
    exact fun x hx ↦ integrable_exp_mul_of_le_of_le hC_neg hC hx.1.le hx.2.le
  exact h_subset ⟨by simp [hC_pos], hC_pos⟩

@[to_fun integrable_fun_id]
lemma integrable_id : Integrable id μ :=
  memLp_one_iff_integrable.1 <| memLp_id μ 1 one_ne_zero (by norm_num)

@[to_fun memLp_two_fun_id]
lemma memLp_two_id : MemLp id 2 μ := memLp_id μ 2 (by norm_num) (by norm_num)

lemma integral_dual (L : StrongDual ℝ E) : μ[L] = L (∫ x, x ∂μ) :=
  L.integral_comp_comm ((memLp_id μ 1 one_ne_zero (by simp)).integrable le_rfl)

/-- A Gaussian measure with variance zero is a Dirac. -/
lemma eq_dirac_of_variance_eq_zero (h : ∀ L : StrongDual ℝ E, Var[L; μ] = 0) :
    μ = Measure.dirac (∫ x, x ∂μ) := by
  refine Measure.ext_of_charFunDual ?_
  ext L
  rw [charFunDual_dirac, charFunDual_eq L, h L, integral_complex_ofReal, integral_dual L]
  simp

/-- If a Gaussian measure is not a Dirac, then it has no atoms. -/
lemma noAtoms (h : ∀ x, μ ≠ Measure.dirac x) : NoAtoms μ where
  measure_singleton x := by
    obtain ⟨L, hL⟩ : ∃ L : StrongDual ℝ E, Var[L; μ] ≠ 0 := by
      contrapose! h
      exact ⟨_, eq_dirac_of_variance_eq_zero h⟩
    have hL_zero : μ.map L {L x} = 0 := by
      have : NoAtoms (μ.map L) := by
        rw [map_eq_gaussianReal L]
        refine noAtoms_gaussianReal ?_
        simp only [ne_eq, Real.toNNReal_eq_zero, not_le]
        exact lt_of_le_of_ne (variance_nonneg _ _) hL.symm
      rw [measure_singleton]
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)] at hL_zero
    refine measure_mono_null ?_ hL_zero
    exact fun ⦃a⦄ ↦ congrArg ⇑L

/-- Characteristic function of a centered Gaussian measure. -/
lemma charFunDual_eq_of_integral_eq_zero (hμ : μ[id] = 0) (L : StrongDual ℝ E) :
    charFunDual μ L = exp (- Var[L; μ] / 2) := by
  refine charFunDual_eq_of_forall_strongDual_eq_zero (fun L ↦ ?_) L
  simp only [id_eq] at hμ
  simp [integral_dual, hμ]

/-- For a centered Gaussian measure `μ`, the product measure `μ.prod μ` is invariant under
rotation. -/
lemma map_rotation_eq_self (hμ : μ[id] = 0) (θ : ℝ) :
    (μ.prod μ).map (ContinuousLinearMap.rotation θ) = μ.prod μ := by
  refine map_rotation_eq_self_of_forall_strongDual_eq_zero (fun L ↦ ?_) θ
  simp only [id_eq] at hμ
  simp [integral_dual, hμ]

end FiniteMoments

end ProbabilityTheory.IsGaussian
