/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.CovarianceBanach

/-!
# Gaussian distributions in Banach spaces

We introduce a predicate `IsGaussian` for measures on a Banach space `E` such that the map by
any continuous linear form is a Gaussian measure on `ℝ`.

For Gaussian distributions in `ℝ`, see the file `Mathlib.Probability.Distributions.Gaussian`.

## Main definitions

* `IsGaussian`: a measure `μ` is Gaussian if its map by every continuous linear form
  `L : Dual ℝ E` is a real Gaussian measure.
  That is, `μ.map L = gaussianReal (μ[L]) (Var[L; μ]).toNNReal`.

## Main statements

* `isGaussian_iff_charFunDual_eq`: a finite measure `μ` is Gaussian if and only if
  its characteristic function has value `exp (μ[L] * I - Var[L; μ] / 2)` for every
  continuous linear form `L : Dual ℝ E`.

## References

* [Martin Hairer, *An introduction to stochastic PDEs*][hairer2009introduction]

-/

open MeasureTheory Complex NormedSpace
open scoped ENNReal NNReal

namespace ProbabilityTheory

section Centered

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {mE : MeasurableSpace E}

/-- A measure `μ` is centered if `μ[L] = 0` for all continuous linear forms `L`. -/
def IsCentered (μ : Measure E) : Prop := ∀ L : E →L[ℝ] ℝ, μ[L] = 0

lemma isCentered_dirac_zero [OpensMeasurableSpace E] : IsCentered (Measure.dirac (0 : E)) := by
  intro L; simp

lemma isCentered_map_sub_integral_id [CompleteSpace E] [BorelSpace E]
    {μ : Measure E} [IsProbabilityMeasure μ] (h_Lp : MemLp id 1 μ) :
    IsCentered (μ.map (fun x ↦ x - μ[id])) := by
  intro L
  rw [integral_map (by fun_prop) (by fun_prop)]
  simp only [map_sub]
  rw [integral_sub (h_Lp.integrable_continuousLinearMap L) (integrable_const _)]
  simp [← ContinuousLinearMap.integral_comm_of_memLp_id h_Lp]

end Centered

/-- A measure is Gaussian if its map by every continuous linear form is a real Gaussian measure. -/
class IsGaussian {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
  {mE : MeasurableSpace E} (μ : Measure E) : Prop where
  map_eq_gaussianReal (L : E →L[ℝ] ℝ) : μ.map L = gaussianReal (μ[L]) (Var[L; μ]).toNNReal

/-- A real Gaussian measure is Gaussian. -/
instance isGaussian_gaussianReal (m : ℝ) (v : ℝ≥0) : IsGaussian (gaussianReal m v) where
  map_eq_gaussianReal L := by
    rw [gaussianReal_map_continuousLinearMap]
    simp only [integral_continuousLinearMap_gaussianReal, variance_continuousLinearMap_gaussianReal,
      Real.coe_toNNReal']
    congr
    rw [Real.toNNReal_mul (by positivity), Real.toNNReal_coe]
    congr
    simp only [left_eq_sup]
    positivity

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
  {μ : Measure E} [IsGaussian μ]

/-- Dirac measures are Gaussian. -/
instance {x : E} : IsGaussian (Measure.dirac x) where
  map_eq_gaussianReal L := by rw [Measure.map_dirac (by fun_prop)]; simp

/-- A Gaussian measure is a probability measure. -/
instance : IsProbabilityMeasure μ where
  measure_univ := by
    let L : Dual ℝ E := Nonempty.some inferInstance
    have : μ.map L Set.univ = 1 := by simp [IsGaussian.map_eq_gaussianReal L]
    simpa [Measure.map_apply (by fun_prop : Measurable L) .univ] using this

lemma IsGaussian.memLp_dual (μ : Measure E) [IsGaussian μ] (L : Dual ℝ E)
    (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp L p μ := by
  suffices MemLp (id ∘ L) p μ from this
  rw [← memLp_map_measure_iff (by fun_prop) (by fun_prop), IsGaussian.map_eq_gaussianReal L]
  convert memLp_id_gaussianReal p.toNNReal
  simp [hp]

@[fun_prop]
lemma IsGaussian.integrable_dual (μ : Measure E) [IsGaussian μ] (L : Dual ℝ E) :
    Integrable L μ := by
  rw [← memLp_one_iff_integrable]
  exact IsGaussian.memLp_dual μ L 1 (by simp)

section charFunDual

/-- The characteristic function of a Gaussian measure `μ` has value
`exp (μ[L] * I - Var[L; μ] / 2)` at `L : Dual ℝ E`. -/
lemma IsGaussian.charFunDual_eq (L : Dual ℝ E) :
    charFunDual μ L = exp (μ[L] * I - Var[L; μ] / 2) := by
  calc charFunDual μ L
  _ = charFun (μ.map L) 1 := by rw [charFunDual_eq_charFun_map_one]
  _ = charFun (gaussianReal (μ[L]) (Var[L; μ]).toNNReal) 1 := by
    rw [IsGaussian.map_eq_gaussianReal L]
  _ = exp (μ[L] * I - Var[L; μ] / 2) := by
    rw [charFun_gaussianReal]
    simp only [ofReal_one, one_mul, Real.coe_toNNReal', one_pow, mul_one]
    congr
    · rw [integral_complex_ofReal]
    · simp only [sup_eq_left]
      exact variance_nonneg _ _

lemma IsGaussian.charFunDual_eq_of_isCentered (hμ : IsCentered μ) (L : E →L[ℝ] ℝ) :
    charFunDual μ L = cexp (- Var[L; μ] / 2) := by
  rw [IsGaussian.charFunDual_eq L, integral_complex_ofReal, hμ L]
  simp [neg_div]

/-- A finite measure is Gaussian iff its characteristic function has value
`exp (μ[L] * I - Var[L; μ] / 2)` for every `L : Dual ℝ E`. -/
theorem isGaussian_iff_charFunDual_eq {μ : Measure E} [IsFiniteMeasure μ] :
    IsGaussian μ ↔ ∀ L : Dual ℝ E, charFunDual μ L = exp (μ[L] * I - Var[L; μ] / 2) := by
  refine ⟨fun h ↦ h.charFunDual_eq, fun h ↦ ⟨fun L ↦ Measure.ext_of_charFun ?_⟩⟩
  ext u
  rw [charFun_map_eq_charFunDual_smul L u, h (u • L), charFun_gaussianReal]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, ofReal_mul,
    Real.coe_toNNReal']
  congr
  · rw [integral_const_mul, integral_complex_ofReal]
  · rw [max_eq_left (variance_nonneg _ _), mul_comm, ← ofReal_pow, ← ofReal_mul, ← variance_mul]
    congr

alias ⟨_, isGaussian_of_charFunDual_eq⟩ := isGaussian_iff_charFunDual_eq

end charFunDual

lemma isGaussian_map_prod_add [SecondCountableTopology E]
    {μ ν : Measure E} [IsGaussian μ] [IsGaussian ν] :
    IsGaussian ((μ.prod ν).map (fun p ↦ p.1 + p.2)) where
  map_eq_gaussianReal := by
    intro L
    have h1 : ((μ.prod ν).map (fun p ↦ p.1 + p.2)).map L
        = ((μ.map L).prod (ν.map L)).map (fun p ↦ p.1 + p.2) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      have : (L ∘ fun (p : E × E) ↦ p.1 + p.2)
          = (fun p : ℝ × ℝ ↦ p.1 + p.2) ∘ (Prod.map L L) := by ext; simp
      rw [this, ← Measure.map_map (by fun_prop) (by fun_prop),
        ← Measure.map_prod_map]
      · fun_prop
      · fun_prop
    have : ∫ x, L x ∂((μ.prod ν).map (fun p ↦ p.1 + p.2))
          = ∫ x, x ∂(((μ.map L).prod (ν.map L)).map (fun p ↦ p.1 + p.2)) := by
        rw [← h1, integral_map (φ := L) (by fun_prop) (by fun_prop)]
    rw [h1, this, ← variance_id_map (by fun_prop), h1, IsGaussian.map_eq_gaussianReal L,
      IsGaussian.map_eq_gaussianReal L, gaussianReal_map_prod_add]
    congr
    · simp
    · simp [variance_nonneg]

instance isGaussian_conv [SecondCountableTopology E]
    {μ ν : Measure E} [IsGaussian μ] [IsGaussian ν] :
    IsGaussian (μ ∗ ν) := isGaussian_map_prod_add

section Map

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- The map of a Gaussian measure by a continuous linear map is Gaussian. -/
instance isGaussian_map (L : E →L[ℝ] F) : IsGaussian (μ.map L) where
  map_eq_gaussianReal L' := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    change Measure.map (L'.comp L) μ = _
    rw [IsGaussian.map_eq_gaussianReal (L'.comp L)]
    congr
    · rw [integral_map (by fun_prop) (by fun_prop)]
      simp
    · rw [← variance_id_map (by fun_prop)]
      conv_rhs => rw [← variance_id_map (by fun_prop)]
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      simp

instance isGaussian_map_equiv (L : E ≃L[ℝ] F) : IsGaussian (μ.map L) :=
  isGaussian_map (L : E →L[ℝ] F)

lemma isCentered_conv_map_neg [SecondCountableTopology E] :
    IsCentered (μ ∗ (μ.map (ContinuousLinearEquiv.neg ℝ))) := by
  intro L
  rw [integral_conv (by fun_prop)]
  simp only [map_add]
  calc ∫ x, ∫ y, L x + L y ∂μ.map (ContinuousLinearEquiv.neg ℝ) ∂μ
  _ = ∫ x, L x + ∫ y, L y ∂μ.map (ContinuousLinearEquiv.neg ℝ) ∂μ := by
    congr with x
    rw [integral_add (by fun_prop) (by fun_prop)]
    simp [- ContinuousLinearEquiv.coe_neg, integral_const, smul_eq_mul, add_left_inj]
  _ = ∫ x, L x ∂μ + ∫ y, L y ∂μ.map (ContinuousLinearEquiv.neg ℝ) := by
    rw [integral_add (by fun_prop) (by fun_prop)]
    simp
  _ = 0 := by
    rw [integral_map (by fun_prop) (by fun_prop)]
    simp [integral_neg]

end Map

section Rotation

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
  {ν : Measure F} [IsGaussian ν]

lemma memLp_comp_inl_prod (L : E × F →L[ℝ] ℝ) {p : ℝ≥0∞} (hp : p ≠ ∞) :
    MemLp (fun x ↦ (L.comp (.inl ℝ E F) x.1)) p (μ.prod ν) := by
  change MemLp ((L.comp (.inl ℝ E F) ∘ Prod.fst)) p (μ.prod ν)
  rw [← memLp_map_measure_iff]
  · simp only [Measure.map_fst_prod, measure_univ, one_smul]
    exact IsGaussian.memLp_dual μ (L.comp (.inl ℝ E F)) p hp
  · simp only [Measure.map_fst_prod, measure_univ, one_smul]
    exact (IsGaussian.integrable_dual μ (L.comp (.inl ℝ E F))).1
  · fun_prop

lemma memLp_comp_inr_prod (L : E × F →L[ℝ] ℝ) {p : ℝ≥0∞} (hp : p ≠ ∞) :
    MemLp (fun x ↦ (L.comp (.inr ℝ E F) x.2)) p (μ.prod ν) := by
  change MemLp ((L.comp (.inr ℝ E F) ∘ Prod.snd)) p (μ.prod ν)
  rw [← memLp_map_measure_iff]
  · simp only [Measure.map_snd_prod, measure_univ, one_smul]
    exact IsGaussian.memLp_dual _ (L.comp (.inr ℝ E F)) p hp
  · simp only [Measure.map_snd_prod, measure_univ, one_smul]
    exact (IsGaussian.integrable_dual _ (L.comp (.inr ℝ E F))).1
  · fun_prop

lemma memLp_prod (L : E × F →L[ℝ] ℝ) {p : ℝ≥0∞} (hp : p ≠ ∞) :
    MemLp L p (μ.prod ν) := by
  suffices MemLp (fun v ↦ L.comp (.inl ℝ E F) v.1 + L.comp (.inr ℝ E F) v.2) p (μ.prod ν) by
    simp_rw [L.comp_inl_add_comp_inr] at this
    exact this
  exact MemLp.add (memLp_comp_inl_prod L hp) (memLp_comp_inr_prod L hp)

lemma integrable_comp_inl_prod (L : E × F →L[ℝ] ℝ) :
    Integrable (fun x ↦ (L.comp (.inl ℝ E F) x.1)) (μ.prod ν) := by
  rw [← memLp_one_iff_integrable]
  exact memLp_comp_inl_prod L (by simp)

lemma integrable_comp_inr_prod (L : E × F →L[ℝ] ℝ) :
    Integrable (fun x ↦ (L.comp (.inr ℝ E F) x.2)) (μ.prod ν) := by
  rw [← memLp_one_iff_integrable]
  exact memLp_comp_inr_prod L (by simp)

lemma integral_continuousLinearMap_prod (L : E × F →L[ℝ] ℝ) :
    (μ.prod ν)[L] = μ[L.comp (.inl ℝ E F)] + ν[L.comp (.inr ℝ E F)] := by
  simp_rw [← L.comp_inl_add_comp_inr]
  rw [integral_add (integrable_comp_inl_prod L) (integrable_comp_inr_prod L)]
  · congr
    · rw [integral_prod _ (integrable_comp_inl_prod L)]
      simp
    · rw [integral_prod _ (integrable_comp_inr_prod L)]
      simp

lemma variance_continuousLinearMap_prod (L : E × F →L[ℝ] ℝ) :
    Var[L; μ.prod ν] = Var[L.comp (.inl ℝ E F); μ] + Var[L.comp (.inr ℝ E F); ν] := by
  rw [variance_def' (memLp_prod L (by simp)), integral_continuousLinearMap_prod L,
    variance_def', variance_def']
  rotate_left
  · exact IsGaussian.memLp_dual _ _ _ (by simp)
  · exact IsGaussian.memLp_dual _ _ _ (by simp)
  let L₁ := L.comp (.inl ℝ E F)
  let L₂ := L.comp (.inr ℝ E F)
  simp only [Pi.pow_apply, Function.comp_apply,
    ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply]
  suffices h_sq : ∫ v, L v ^ 2 ∂(μ.prod ν)
      = ∫ x, L₁ x ^ 2 ∂μ + ∫ x, L₂ x ^ 2 ∂ν + 2 * μ[L₁] * ν[L₂] by rw [h_sq]; ring
  calc ∫ v, L v ^ 2 ∂μ.prod ν
  _ = ∫ v, (L₁ v.1 + L₂ v.2) ^ 2 ∂μ.prod ν := by simp_rw [← L.comp_inl_add_comp_inr]; simp [L₁, L₂]
  _ = ∫ v, L₁ v.1 ^ 2 + L₂ v.2 ^ 2 + 2 * L₁ v.1 * L₂ v.2 ∂μ.prod ν := by
    congr with v; ring
  _ = ∫ v, L₁ v.1 ^ 2 ∂μ.prod ν + ∫ v, L₂ v.2 ^ 2 ∂μ.prod ν
      + 2 * ∫ v, L₁ v.1 * L₂ v.2 ∂μ.prod ν := by
    have h_int1 : Integrable (fun a ↦ L₁ a.1 ^ 2) (μ.prod ν) := by
      rw [← integrable_norm_iff]
      swap; · exact Measurable.aestronglyMeasurable <| by fun_prop
      simp only [norm_pow]
      refine MemLp.integrable_norm_pow ?_ (by simp)
      exact memLp_comp_inl_prod L (by simp)
    have h_int2 : Integrable (fun a ↦ L₂ a.2 ^ 2) (μ.prod ν) := by
      rw [← integrable_norm_iff]
      swap; · exact Measurable.aestronglyMeasurable <| by fun_prop
      simp only [norm_pow]
      refine MemLp.integrable_norm_pow ?_ (by simp)
      exact memLp_comp_inr_prod L (by simp)
    rw [integral_add, integral_add]
    · simp_rw [mul_assoc]
      rw [integral_const_mul]
    · exact h_int1
    · exact h_int2
    · exact Integrable.add h_int1 h_int2
    · simp_rw [mul_assoc]
      refine Integrable.const_mul ?_ _
      refine MemLp.integrable_mul (p := 2) (q := 2) ?_ ?_
      · exact memLp_comp_inl_prod L (by simp)
      · exact memLp_comp_inr_prod L (by simp)
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
  suffices μ[L₁] * I - Var[L₁; μ] / 2 +(ν[L₂] * I - Var[L₂; ν] / 2)
      = (μ.prod ν)[L] * I - Var[L; μ.prod ν] / 2 by convert this
  rw [sub_add_sub_comm, ← add_mul]
  congr
  · simp_rw [integral_complex_ofReal]
    rw [integral_continuousLinearMap_prod L]
    norm_cast
  · field_simp
    rw [variance_continuousLinearMap_prod]
    norm_cast

/-- The rotation in `E × E` with angle `θ`, as a continuous linear map. -/
noncomputable
def _root_.ContinuousLinearMap.rotation (θ : ℝ) :
    E × E →L[ℝ] E × E where
  toFun := fun x ↦ (Real.cos θ • x.1 + Real.sin θ • x.2, - Real.sin θ • x.1 + Real.cos θ • x.2)
  map_add' x y := by
    simp only [Prod.fst_add, smul_add, Prod.snd_add, neg_smul, Prod.mk_add_mk]
    abel_nf
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, neg_smul, RingHom.id_apply, Prod.smul_mk, smul_add,
      smul_neg]
    simp_rw [smul_comm c]
  cont := by fun_prop

lemma _root_.ContinuousLinearMap.rotation_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (θ : ℝ) (x : E × E) :
    ContinuousLinearMap.rotation θ x
     = (Real.cos θ • x.1 + Real.sin θ • x.2, - Real.sin θ • x.1 + Real.cos θ • x.2) := rfl

lemma IsGaussian.map_rotation_eq_self [SecondCountableTopology E] [CompleteSpace E]
    (hμ : IsCentered μ) (θ : ℝ) :
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
  show Var[(L.comp (.rotation θ)).comp (.inl ℝ E E); μ]
        + Var[(L.comp (.rotation θ)).comp (.inr ℝ E E); μ]
      = Var[L.comp (.inl ℝ E E); μ] + Var[L.comp (.inr ℝ E E); μ]
  have h1 : (L.comp (.rotation θ)).comp (.inl ℝ E E)
      = Real.cos θ • L.comp (.inl ℝ E E) - Real.sin θ • L.comp (.inr ℝ E E) := by
    ext x
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.rotation_apply, smul_zero, add_zero,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul,
      ContinuousLinearMap.inr_apply]
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
  rw [h1, h2, ← covariance_same (by fun_prop), ← covariance_same (by fun_prop),
    ← covariance_same (by fun_prop), ← covariance_same (by fun_prop)]
  simp only [ContinuousLinearMap.coe_sub',
    ContinuousLinearMap.coe_add']
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
  · refine MemLp.add ?_ ?_
    · exact IsGaussian.memLp_dual _ _ _ (by simp)
    · exact IsGaussian.memLp_dual _ _ _ (by simp)
  · exact IsGaussian.memLp_dual _ _ _ (by simp)
  · exact IsGaussian.memLp_dual _ _ _ (by simp)
  · exact IsGaussian.memLp_dual _ _ _ (by simp)
  · exact IsGaussian.memLp_dual _ _ _ (by simp)
  · exact IsGaussian.memLp_dual _ _ _ (by simp)
  · exact IsGaussian.memLp_dual _ _ _ (by simp)
  · exact IsGaussian.memLp_dual _ _ _ (by simp)
  · exact IsGaussian.memLp_dual _ _ _ (by simp)
  · refine MemLp.sub ?_ ?_
    · exact IsGaussian.memLp_dual _ _ _ (by simp)
    · exact IsGaussian.memLp_dual _ _ _ (by simp)
  simp only [ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp', covariance_smul_right,
    covariance_smul_left]
  ring_nf
  rw [add_assoc, add_add_add_comm, mul_comm _ (Real.sin θ ^ 2), ← add_mul, ← add_mul,
    Real.cos_sq_add_sin_sq, one_mul, one_mul]

end Rotation

end ProbabilityTheory
