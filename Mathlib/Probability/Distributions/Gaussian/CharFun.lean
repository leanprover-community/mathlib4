import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Moments.CovarianceBilin

/-!
# Facts about Gaussian characteristic function
-/

open Complex MeasureTheory WithLp NormedSpace ContinuousLinearMap

open scoped Matrix NNReal Real InnerProductSpace ProbabilityTheory

namespace ProbabilityTheory

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SecondCountableTopology E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

lemma isGaussian_iff_gaussian_charFunDual [IsFiniteMeasure μ] :
    IsGaussian μ ↔
    ∃ (m : E) (f : StrongDual ℝ E →L[ℝ] StrongDual ℝ E →L[ℝ] ℝ),
      f.toBilinForm.IsPosSemidef ∧ ∀ L, charFunDual μ L = exp (L m * I - f L L / 2) := by
  refine ⟨fun h ↦ ⟨μ[id], covarianceBilinDual μ, isPosSemidef_covarianceBilinDual, fun L ↦ ?_⟩,
    fun ⟨m, f, hf, h⟩ ↦ ⟨fun L ↦ ?_⟩⟩
  · rw [h.charFunDual_eq, covarianceBilinDual_self_eq_variance]
    · congr
      rw [← L.integral_comp_id_comm', integral_complex_ofReal]
      exact IsGaussian.integrable_id
    exact IsGaussian.memLp_two_id
  have : μ.map L = gaussianReal (L m) (f L L).toNNReal := by
    apply Measure.ext_of_charFun
    ext t
    simp_rw [charFun_map_eq_charFunDual_smul, h, charFun_gaussianReal,
      smul_apply, map_smul, smul_apply, smul_eq_mul]
    congr
    · norm_cast
    rw [Real.coe_toNNReal]
    · norm_cast
      ring
    exact hf.nonneg L
  rw [eq_gaussianReal_integral_variance this, integral_map (by fun_prop) (by fun_prop),
    variance_map aemeasurable_id (by fun_prop)]
  simp

attribute [simp] coe_zero'

lemma gaussian_charFunDual_congr [IsFiniteMeasure μ] {m : E}
    {f : StrongDual ℝ E →L[ℝ] StrongDual ℝ E →L[ℝ] ℝ}
    (hf : f.toBilinForm.IsPosSemidef) (h : ∀ L, charFunDual μ L = exp (L m * I - f L L / 2)) :
    m = ∫ x, x ∂μ ∧ f = covarianceBilinDual μ := by
  have h' := isGaussian_iff_gaussian_charFunDual.2 ⟨m, f, hf, h⟩
  simp_rw [h'.charFunDual_eq, Complex.exp_eq_exp_iff_exists_int, integral_complex_ofReal,
    integral_comp_id_comm IsGaussian.integrable_id] at h
  choose n hn using h
  have h L : (n L : ℂ) = (L (∫ x, x ∂μ) * I - Var[L; μ] / 2 - L m * I + f L L / 2) /
      (2 * π * I) := by
    rw [hn L]
    have : 2 * π * I ≠ 0 := by simp [Real.pi_ne_zero]
    field_simp
    ring
  have : Continuous n := by
    rw [← Complex.isometry_intCast.comp_continuous_iff]
    change Continuous (fun L ↦ (n L : ℂ))
    simp_rw [h, ← covarianceBilinDual_self_eq_variance IsGaussian.memLp_two_id]
    fun_prop
  rw [← IsLocallyConstant.iff_continuous] at this
  apply IsLocallyConstant.eq_const at this
  have this L : n L = 0 := by
    rw [this 0, ← Int.cast_inj (α := ℂ)]
    simp [h]
  simp only [this, Int.cast_zero, zero_mul, add_zero, Complex.ext_iff, sub_re, mul_re, ofReal_re,
    I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, div_ofNat_re, zero_sub, neg_inj, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, div_left_inj', sub_im, mul_im, div_ofNat_im, zero_div,
    sub_zero] at hn
  constructor
  · rw [eq_iff_forall_dual_eq ℝ]
    simp [hn]
  · rw [← toBilinForm_inj]
    apply LinearMap.BilinForm.ext_of_isSymm hf.isSymm isPosSemidef_covarianceBilinDual.isSymm
    intro x
    simp [covarianceBilinDual_self_eq_variance IsGaussian.memLp_two_id, (hn x).1.symm]

/-- Two Gaussian measures are equal if they have same mean and same covariance. -/
protected lemma IsGaussian.ext_covarianceBilinDual {ν : Measure E} [IsGaussian μ] [IsGaussian ν]
    (hm : μ[id] = ν[id]) (hv : covarianceBilinDual μ = covarianceBilinDual ν) : μ = ν := by
  apply Measure.ext_of_charFunDual
  ext L
  simp_rw [IsGaussian.charFunDual_eq, integral_complex_ofReal,
    L.integral_comp_id_comm' IsGaussian.integrable_id, hm,
    ← covarianceBilinDual_self_eq_variance IsGaussian.memLp_two_id, hv]

/-- Two Gaussian measures are equal if and only if they have same mean and same covariance. -/
protected lemma IsGaussian.ext_iff_covarianceBilinDual {ν : Measure E} [IsGaussian μ]
    [IsGaussian ν] :
    μ = ν ↔ μ[id] = ν[id] ∧ covarianceBilinDual μ = covarianceBilinDual ν where
  mp h := by simp [h]
  mpr h := IsGaussian.ext_covarianceBilinDual h.1 h.2

end NormedSpace

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

lemma isGaussian_iff_charFun_eq [IsFiniteMeasure μ] :
    IsGaussian μ ↔
    ∀ t, charFun μ t = exp (μ[fun x ↦ ⟪t, x⟫_ℝ] * I - Var[fun x ↦ ⟪t, x⟫_ℝ; μ] / 2) := by
  rw [isGaussian_iff_charFunDual_eq]
  constructor
  · intro h t
    convert h (InnerProductSpace.toDualMap ℝ E t)
    exact charFun_eq_charFunDual_toDualMap t
  · intro h L
    simpa using h ((InnerProductSpace.toDual ℝ E).symm L)

variable [SecondCountableTopology E]

lemma IsGaussian.charFun_eq [IsGaussian μ] (t : E) :
    charFun μ t = exp (⟪t, μ[id]⟫_ℝ * I - covarianceBilin μ t t / 2) := by
  rw [isGaussian_iff_charFun_eq.1 inferInstance]
  congr
  · simp_rw [integral_complex_ofReal, ← integral_inner IsGaussian.integrable_id, id]
  · rw [covarianceBilin_self IsGaussian.memLp_two_id]

lemma isGaussian_iff_gaussian_charFun [IsFiniteMeasure μ] :
    IsGaussian μ ↔
    ∃ (m : E) (f : E →L[ℝ] E →L[ℝ] ℝ),
      f.toBilinForm.IsPosSemidef ∧ ∀ t, charFun μ t = exp (⟪t, m⟫_ℝ * I - f t t / 2) := by
  rw [isGaussian_iff_gaussian_charFunDual]
  refine ⟨fun ⟨m, f, hf, h⟩ ↦ ⟨m,
    f.bilinearComp (InnerProductSpace.toDualMap ℝ E).toContinuousLinearMap
      (InnerProductSpace.toDualMap ℝ E).toContinuousLinearMap,
    ⟨⟨fun x y ↦ ?_⟩, ⟨fun x ↦ ?_⟩⟩, ?_⟩,
    fun ⟨m, f, hf, h⟩ ↦ ⟨m,
      f.bilinearComp (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry.toContinuousLinearMap
        (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry.toContinuousLinearMap,
    ⟨⟨fun x y ↦ ?_⟩, ⟨fun x ↦ ?_⟩⟩, ?_⟩⟩
  any_goals simpa using hf.eq ..
  any_goals simpa using hf.nonneg _
  · simp [charFun_eq_charFunDual_toDualMap, h]
  · simp [← charFun_toDual_symm_eq_charFunDual, h]

/-- If the characteristic function of `μ` takes the form of a gaussian characteristic function,
then the parameters have to be the expectation and the covariance bilinear form. -/
lemma gaussian_charFun_congr [IsFiniteMeasure μ] (m : E) (f : E →L[ℝ] E →L[ℝ] ℝ)
    (hf : f.toBilinForm.IsPosSemidef) (h : ∀ t, charFun μ t = exp (⟪t, m⟫_ℝ * I - f t t / 2)) :
    m = ∫ x, x ∂μ ∧ f = covarianceBilin μ := by
  let g : StrongDual ℝ E →L[ℝ] StrongDual ℝ E →L[ℝ] ℝ :=
    f.bilinearComp (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry.toContinuousLinearMap
      (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry.toContinuousLinearMap
  have : ∀ L : StrongDual ℝ E, charFunDual μ L = exp (L m * I - g L L / 2) := by
    simp [← charFun_toDual_symm_eq_charFunDual, h, g]
  have hg : g.toBilinForm.IsPosSemidef := by
    refine ⟨⟨fun x y ↦ ?_⟩, ⟨fun x ↦ ?_⟩⟩
    · simpa [g] using hf.eq ..
    · simpa [g] using hf.nonneg _
  have := gaussian_charFunDual_congr hg this
  refine ⟨this.1, ?_⟩
  ext
  simp [covarianceBilin, ← this.2, g, ← InnerProductSpace.toDual_apply_eq_toDualMap_apply]

/-- Two Gaussian measures are equal if they have same mean and same covariance. This is
`IsGaussian.ext_covarianceBilinDual` specialized to Hilbert spaces. -/
protected lemma IsGaussian.ext {ν : Measure E} [IsGaussian μ] [IsGaussian ν]
    (hm : μ[id] = ν[id]) (hv : covarianceBilin μ = covarianceBilin ν) : μ = ν := by
  apply Measure.ext_of_charFun
  ext t
  simp_rw [IsGaussian.charFun_eq, hm, hv]

/-- Two Gaussian measures are equal if and only if they have same mean and same covariance. This is
`IsGaussian.ext_iff_covarianceBilinDual` specialized to Hilbert spaces. -/
protected lemma IsGaussian.ext_iff {ν : Measure E} [IsGaussian μ] [IsGaussian ν] :
    μ = ν ↔ μ[id] = ν[id] ∧ covarianceBilin μ = covarianceBilin ν where
  mp h := by simp [h]
  mpr h := IsGaussian.ext h.1 h.2

end InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SecondCountableTopology E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

/-- Two Gaussian measures are equal if they have same mean and same covariance. -/
protected lemma IsGaussian.ext_covarianceBilin {ν : Measure E} [IsGaussian μ] [IsGaussian ν]
    (hm : μ[id] = ν[id]) (hv : covarianceBilinDual μ = covarianceBilinDual ν) : μ = ν := by
  apply Measure.ext_of_charFunDual
  ext L
  simp_rw [IsGaussian.charFunDual_eq, integral_complex_ofReal,
    L.integral_comp_id_comm' IsGaussian.integrable_id, hm,
    ← covarianceBilinDual_self_eq_variance IsGaussian.memLp_two_id, hv]

/-- Two Gaussian measures are equal if and only if they have same mean and same covariance. -/
protected lemma IsGaussian.ext_iff_covarianceBilin {ν : Measure E} [IsGaussian μ] [IsGaussian ν] :
    μ = ν ↔ μ[id] = ν[id] ∧ covarianceBilinDual μ = covarianceBilinDual ν where
  mp h := by simp [h]
  mpr h := IsGaussian.ext_covarianceBilin h.1 h.2

lemma IsGaussian.eq_gaussianReal (μ : Measure ℝ) [IsGaussian μ] :
    μ = gaussianReal μ[id] Var[id; μ].toNNReal := by
  nth_rw 1 [← Measure.map_id (μ := μ), ← coe_id' (R₁ := ℝ),
    map_eq_gaussianReal]
  rfl

end ProbabilityTheory
