import Mathlib.Analysis.SpecialFunctions.Gaussian

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

open Filter MeasureTheory Complex

open scoped Real Topology FourierTransform RealInnerProductSpace BigOperators

variable {f : V → E}

local notation "e" => Real.fourierChar



lemma _root_.Filter.Tendsto.ofReal' {α : Type*} {l : Filter α} {f : α → ℝ} {x : ℝ}
    (hf : Tendsto f l (𝓝 x)) :
    Tendsto (fun x ↦ (f x : ℂ)) l (𝓝 (x : ℂ)) :=
  (Complex.continuous_ofReal.tendsto _).comp hf

namespace InnerFourier

lemma foot (hf : Integrable f) :
    Tendsto (fun (c : ℝ) ↦ (∫ v : V, Complex.exp (- c⁻¹ * ‖v‖^2) • f v))
      atTop (𝓝 (∫ v : V, f v)) := by
  apply tendsto_integral_filter_of_dominated_convergence _ _ _ hf.norm
  · apply eventually_of_forall (fun v ↦ ?_)
    nth_rewrite 2 [show f v = Complex.exp (- (0 : ℝ) * ‖v‖^2) • f v by simp]
    apply (Tendsto.cexp _).smul_const
    exact tendsto_inv_atTop_zero.ofReal'.neg.mul_const _
  · apply eventually_of_forall (fun c ↦ ?_)
    exact AEStronglyMeasurable.smul (Continuous.aestronglyMeasurable (by continuity)) hf.1
  · filter_upwards [Ici_mem_atTop (0 : ℝ)] with c (hc : 0 ≤ c)
    apply eventually_of_forall (fun v ↦ ?_)
    simp only [ofReal_inv, neg_mul, norm_smul, norm_eq_abs, abs_exp]
    norm_cast
    conv_rhs => rw [← one_mul (‖f v‖)]
    gcongr
    simp only [Real.exp_le_one_iff, Left.neg_nonpos_iff]
    positivity

lemma glou (hf : Integrable (𝓕ᵢ f)) (v : V) :
    Tendsto (fun (c : ℝ) ↦ (∫ w : V, cexp (- c⁻¹ * ‖w‖^2 + 2 * π * Complex.I * ⟪v, w⟫)
       • (𝓕ᵢ f) w)) atTop (𝓝 (𝓕ᵢ⁻ (𝓕ᵢ f) v)) := by
  have : Integrable (fun w ↦ e[⟪w, v⟫] • (𝓕ᵢ f) w) := by
    have B : Continuous fun p : V × V => (- innerₗ V) p.1 p.2 := continuous_inner.neg
    simpa using
      (VectorFourier.fourier_integral_convergent_iff Real.continuous_fourierChar B v).1 hf
  convert foot this using 4 with c w
  · rw [Real.fourierChar_apply, smul_smul, ← Complex.exp_add, real_inner_comm]
    congr 3
    simp
    ring
  · simp [fourierIntegralInv_eq]

variable [CompleteSpace E]

open FiniteDimensional

lemma glouglou (hf : Integrable f) (h'f : Integrable (𝓕ᵢ f)) (v : V) :
    Tendsto (fun (c : ℝ) ↦ (∫ w : V,
        𝓕ᵢ (fun w ↦ cexp (- c⁻¹ * ‖w‖^2 + 2 * π * Complex.I * ⟪v, w⟫)) w • f w)) atTop
      (𝓝 (𝓕ᵢ⁻ (𝓕ᵢ f) v)) := by
  apply (glou h'f v).congr'
  filter_upwards [Ioi_mem_atTop 0] with c (hc : 0 < c)
  have I : Integrable (fun w ↦ cexp (- c⁻¹ * ‖w‖^2 + 2 * π * Complex.I * ⟪v, w⟫)) :=
    GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (by simpa) _ _
  simpa using (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ V)
    Real.continuous_fourierChar continuous_inner I hf).symm

lemma glouglouglou (hf : Integrable f) (h'f : Integrable (𝓕ᵢ f)) (v : V) :
    Tendsto (fun (c : ℝ) ↦
      ∫ w : V, ((π * c) ^ (finrank ℝ V / 2 : ℂ) * cexp (-π ^ 2 * c * ‖v - w‖ ^ 2)) • f w)
    atTop (𝓝 (𝓕ᵢ⁻ (𝓕ᵢ f) v)) := by
  apply Tendsto.congr' _ (glouglou hf h'f v)
  filter_upwards [Ioi_mem_atTop 0] with c (hc : 0 < c)
  congr with w
  rw [GaussianFourier.fourierTransform_gaussian_innerProductSpace' (by simpa)]
  congr
  · simp
  · simp; ring

lemma zouguette (c : ℝ) (hc : 0 < c) :
    ∫ w : V, (π * c) ^ (finrank ℝ V / 2 : ℂ) * cexp (-(π ^ 2 * c) * ‖w‖ ^ 2) = 1 := by
  rw [integral_mul_left, GaussianFourier.integral_cexp_neg_mul_sq_norm]; swap
  · norm_cast; positivity
  rw [← ofReal_mul, ← ofReal_pow, ← ofReal_mul, ← ofReal_div,
    ← mul_cpow_ofReal_nonneg (by positivity) (by positivity), ← ofReal_mul]
  convert one_cpow _
  norm_cast
  field_simp
  ring

open Metric

lemma approx_id {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α] (μ : Measure α) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {ι : Type*} {l : Filter ι} {x₀ : α}
    {f : ι → α → ℝ} (hf : ∀ᶠ i in l, ∀ x, 0 ≤ f i x)
    (h'f : ∀ ε > 0, Tendsto (fun i ↦ ∫ x in closedBall x₀ ε, f i x ∂μ) l (𝓝 1))
    (h''f : ∀ ε > 0, ∀ δ > 0, ∀ᶠ i in l, ∀ x ∈ (closedBall x₀ ε)ᶜ, f i x ≤ δ)
    {g : α → E} (hg : ContinuousAt g x₀) (h'g : Integrable g μ) :
    Tendsto (fun i ↦ ∫ x, f i x • g x ∂μ) l (𝓝 (g x₀)) := sorry

lemma foufou (hf : Integrable f) (v : V) (h'f : ContinuousAt f v) :
    Tendsto (fun (c : ℝ) ↦
      ∫ w : V, ((π * c : ℂ) ^ (finrank ℝ V / 2 : ℂ) * cexp (-π ^ 2 * c * ‖v - w‖ ^ 2)) • f w)
    atTop (𝓝 (f v)) := sorry






end InnerFourier
