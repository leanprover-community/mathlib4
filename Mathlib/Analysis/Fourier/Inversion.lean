import Mathlib.Analysis.Fourier.FourierTransform

variable {f : V → E}


lemma _root_.Filter.Tendsto.ofReal' {α : Type*} {l : Filter α} {f : α → ℝ} {x : ℝ}
    (hf : Tendsto f l (𝓝 x)) :
    Tendsto (fun x ↦ (f x : ℂ)) l (𝓝 (x : ℂ)) :=
  (Complex.continuous_ofReal.tendsto _).comp hf

open Complex

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
    Tendsto (fun (c : ℝ) ↦ (∫ w : V, (cexp (- c⁻¹ * ‖w‖^2) * e[⟪w, v⟫]) • (𝓕ᵢ f) w)) atTop
      (𝓝 (𝓕ᵢ⁻ (𝓕ᵢ f) v)) := by
  have : Integrable (fun w ↦ e[⟪w, v⟫] • (𝓕ᵢ f) w) := by
    have B : Continuous fun p : V × V => (- innerₗ V) p.1 p.2 := continuous_inner.neg
    simpa using
      (VectorFourier.fourier_integral_convergent_iff Real.continuous_fourierChar B v).1 hf
  convert foot this using 4 with c w
  · simp [smul_smul]
  · simp [fourierIntegralInv_eq]

lemma glouglou [CompleteSpace E] (hf : Integrable f) (h'f : Integrable (𝓕ᵢ f)) (v : V) :
    Tendsto (fun (c : ℝ) ↦ (∫ w : V, 𝓕ᵢ (fun w ↦ cexp (- c⁻¹ * ‖w‖^2) * e[⟪w, v⟫]) w • f w)) atTop
      (𝓝 (𝓕ᵢ⁻ (𝓕ᵢ f) v)) := by
  apply (glou h'f v).congr'
  filter_upwards [Ioi_mem_atTop 0] with c (hc : 0 < c)
  have I : Integrable (fun w ↦ cexp (- c⁻¹ * ‖w‖^2) * e[⟪w, v⟫]) := by
    have A : Integrable (fun (w : V) ↦ cexp (- c⁻¹ * ‖w‖^2)) := by
    have B : Continuous fun p : V × V => (- innerₗ V) p.1 p.2 := continuous_inner.neg
    have Z := (VectorFourier.fourier_integral_convergent_iff Real.continuous_fourierChar B v).1 A
    convert Z using 2 with w
    simp [mul_comm]
  simpa using (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ V)
    Real.continuous_fourierChar continuous_inner I hf).symm
