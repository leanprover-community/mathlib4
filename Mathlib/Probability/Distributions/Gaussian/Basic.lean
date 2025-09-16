/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Gaussian distributions in Banach spaces

We introduce a predicate `IsGaussian` for measures on a Banach space `E` such that the map by
any continuous linear form is a Gaussian measure on `ℝ`.

For Gaussian distributions in `ℝ`, see the file `Mathlib.Probability.Distributions.Gaussian.Real`.

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

/-- A measure is Gaussian if its map by every continuous linear form is a real Gaussian measure. -/
class IsGaussian {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    {mE : MeasurableSpace E} (μ : Measure E) : Prop where
  map_eq_gaussianReal (L : StrongDual ℝ E) : μ.map L = gaussianReal (μ[L]) (Var[L; μ]).toNNReal

/-- A Gaussian measure is a probability measure. -/
instance IsGaussian.toIsProbabilityMeasure {E : Type*} [TopologicalSpace E] [AddCommMonoid E]
    [Module ℝ E] {mE : MeasurableSpace E} (μ : Measure E) [IsGaussian μ] :
    IsProbabilityMeasure μ where
  measure_univ := by
    have : μ.map (0 : StrongDual ℝ E) Set.univ = 1 := by simp [IsGaussian.map_eq_gaussianReal]
    simpa [Measure.map_apply (by fun_prop : Measurable (0 : StrongDual ℝ E)) .univ] using this

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

lemma IsGaussian.memLp_dual (μ : Measure E) [IsGaussian μ] (L : StrongDual ℝ E)
    (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp L p μ := by
  suffices MemLp (id ∘ L) p μ from this
  rw [← memLp_map_measure_iff (by fun_prop) (by fun_prop), IsGaussian.map_eq_gaussianReal L]
  convert memLp_id_gaussianReal p.toNNReal
  simp [hp]

@[fun_prop]
lemma IsGaussian.integrable_dual (μ : Measure E) [IsGaussian μ] (L : StrongDual ℝ E) :
    Integrable L μ := by
  rw [← memLp_one_iff_integrable]
  exact IsGaussian.memLp_dual μ L 1 (by simp)

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

lemma isGaussian_map_equiv_iff {μ : Measure E} (L : E ≃L[ℝ] F) :
    IsGaussian (μ.map L) ↔ IsGaussian μ := by
  refine ⟨fun h ↦ ?_, fun _ ↦ inferInstance⟩
  suffices μ = (μ.map L).map L.symm by rw [this]; infer_instance
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  simp

section charFunDual

/-- The characteristic function of a Gaussian measure `μ` has value
`exp (μ[L] * I - Var[L; μ] / 2)` at `L : Dual ℝ E`. -/
lemma IsGaussian.charFunDual_eq (L : StrongDual ℝ E) :
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

/-- A finite measure is Gaussian iff its characteristic function has value
`exp (μ[L] * I - Var[L; μ] / 2)` for every `L : Dual ℝ E`. -/
theorem isGaussian_iff_charFunDual_eq {μ : Measure E} [IsFiniteMeasure μ] :
    IsGaussian μ ↔ ∀ L : StrongDual ℝ E, charFunDual μ L = exp (μ[L] * I - Var[L; μ] / 2) := by
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

instance isGaussian_conv [SecondCountableTopology E]
    {μ ν : Measure E} [IsGaussian μ] [IsGaussian ν] :
    IsGaussian (μ ∗ ν) where
  map_eq_gaussianReal L := by
    have : (μ ∗ ν)[L] = ∫ x, x ∂((μ.map L).conv (ν.map L)) := by
      rw [← Measure.map_conv_continuousLinearMap L,
        integral_map (φ := L) (by fun_prop) (by fun_prop)]
    rw [Measure.map_conv_continuousLinearMap L, this, ← variance_id_map (by fun_prop),
      Measure.map_conv_continuousLinearMap L, IsGaussian.map_eq_gaussianReal L,
      IsGaussian.map_eq_gaussianReal L, gaussianReal_conv_gaussianReal]
    congr <;> simp [variance_nonneg]

instance (c : E) : IsGaussian (μ.map (fun x ↦ x + c)) := by
  refine isGaussian_of_charFunDual_eq fun L ↦ ?_
  rw [charFunDual_map_add_const, IsGaussian.charFunDual_eq, ← exp_add]
  have hL_comp : L ∘ (fun x ↦ x + c) = fun x ↦ L x + L c := by ext; simp
  rw [variance_map (by fun_prop) (by fun_prop), integral_map (by fun_prop) (by fun_prop),
    hL_comp, variance_add_const (by fun_prop), integral_complex_ofReal, integral_complex_ofReal]
  simp only [map_add]
  rw [integral_add (by fun_prop) (by fun_prop)]
  congr
  simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul, ofReal_add]
  ring

instance (c : E) : IsGaussian (μ.map (fun x ↦ c + x)) := by simp_rw [add_comm c]; infer_instance

instance (c : E) : IsGaussian (μ.map (fun x ↦ x - c)) := by simp_rw [sub_eq_add_neg]; infer_instance

instance : IsGaussian (μ.map (fun x ↦ -x)) := by
  change IsGaussian (μ.map (ContinuousLinearEquiv.neg ℝ))
  infer_instance

instance (c : E) : IsGaussian (μ.map (fun x ↦ c - x)) := by
  simp_rw [sub_eq_add_neg]
  suffices IsGaussian ((μ.map (fun x ↦ -x)).map (fun x ↦ c + x)) by
    rw [Measure.map_map (by fun_prop) (by fun_prop)] at this
    convert this using 1
  infer_instance

end ProbabilityTheory
