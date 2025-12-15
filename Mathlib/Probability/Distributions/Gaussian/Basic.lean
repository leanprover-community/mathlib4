/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Gaussian distributions in Banach spaces

We introduce a predicate `IsGaussian` for measures on a Banach space `E` such that the map by
any continuous linear form is a Gaussian measure on `ℝ`.

For Gaussian distributions in `ℝ`, see the file
`Mathlib/Probability/Distributions/Gaussian/Real.lean`.

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

@[expose] public section

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

/-- A Gaussian measure over `ℝ` is some `gaussianReal`. -/
lemma IsGaussian.eq_gaussianReal (μ : Measure ℝ) (h : IsGaussian μ) :
    μ = gaussianReal μ[id] Var[id; μ].toNNReal := calc
  μ = μ.map (ContinuousLinearMap.id ℝ ℝ) := by simp
  _ = gaussianReal μ[id] Var[id; μ].toNNReal := by rw [h.map_eq_gaussianReal]; simp

lemma isGaussian_of_isGaussian_map {E : Type*} [TopologicalSpace E] [AddCommMonoid E]
    [Module ℝ E] {mE : MeasurableSpace E} [OpensMeasurableSpace E] {μ : Measure E}
    (h : ∀ L : E →L[ℝ] ℝ, IsGaussian (μ.map L)) : IsGaussian μ := by
  refine ⟨fun L ↦ ?_⟩
  rw [(h L).eq_gaussianReal, integral_map, variance_map]
  · simp
  all_goals fun_prop

lemma isGaussian_of_map_eq_gaussianReal {E : Type*} [TopologicalSpace E] [AddCommMonoid E]
    [Module ℝ E] {mE : MeasurableSpace E} [OpensMeasurableSpace E] {μ : Measure E}
    (h : ∀ L : E →L[ℝ] ℝ, ∃ (m : ℝ) (v : ℝ≥0), μ.map L = gaussianReal m v) :
    IsGaussian μ := by
  refine isGaussian_of_isGaussian_map fun L ↦ ?_
  obtain ⟨m, v, h⟩ := h L
  rw [h]
  infer_instance

/-- Mapping a Gaussian measure by a measurable and continuous linear map yields a Gaussian
measure. See also `isGaussian_map`, which does not assume measurability but has stronger hypotheses
on `E`. In particular, it requires `E` to be a Borel space, which requires some second countability
hypotheses if `E` is a product space. This version does not, which can be useful for instance
if `L := Prod.fst`, which is always measurable. -/
lemma isGaussian_map_of_measurable {E F : Type*} [TopologicalSpace E] [AddCommMonoid E]
    [Module ℝ E] {mE : MeasurableSpace E} [TopologicalSpace F] [AddCommMonoid F]
    [Module ℝ F] {mF : MeasurableSpace F} [OpensMeasurableSpace F] {μ : Measure E}
    {L : E →L[ℝ] F} [IsGaussian μ] (hL : Measurable L) : IsGaussian (μ.map L) := by
  refine isGaussian_of_map_eq_gaussianReal fun L' ↦ ⟨μ[L' ∘L L], Var[L' ∘L L; μ].toNNReal, ?_⟩
  rw [Measure.map_map (by fun_prop) hL, ← ContinuousLinearMap.coe_comp',
    IsGaussian.map_eq_gaussianReal]

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
instance isGaussian_map (L : E →L[ℝ] F) : IsGaussian (μ.map L) :=
    isGaussian_map_of_measurable (by fun_prop)

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
  · rw [max_eq_left (variance_nonneg _ _), mul_comm, ← ofReal_pow, ← ofReal_mul,
      ← variance_const_mul]
    congr

alias ⟨_, isGaussian_of_charFunDual_eq⟩ := isGaussian_iff_charFunDual_eq

end charFunDual

section charFun

open InnerProductSpace
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] {μ : Measure E}

lemma IsGaussian.charFun_eq [IsGaussian μ] (t : E) :
    charFun μ t = exp (μ[fun x ↦ ⟪t, x⟫] * I - Var[fun x ↦ ⟪t, x⟫; μ] / 2) := by
  rw [charFun_eq_charFunDual_toDualMap, IsGaussian.charFunDual_eq]
  simp [toDualMap]

-- TODO: This should not require completeness as `toDualMap` has dense range, but this is not
-- in mathlib.
lemma isGaussian_iff_charFun_eq [CompleteSpace E] [IsFiniteMeasure μ] :
    IsGaussian μ ↔
    ∀ t, charFun μ t = exp (μ[fun x ↦ ⟪t, x⟫] * I - Var[fun x ↦ ⟪t, x⟫; μ] / 2) := by
  simp_rw [isGaussian_iff_charFunDual_eq, (toDual ℝ E).surjective.forall,
    charFun_eq_charFunDual_toDualMap]
  simp [toDualMap, toDual]

end charFun

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
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, ofReal_add]
  ring

instance (c : E) : IsGaussian (μ.map (fun x ↦ c + x)) := by simp_rw [add_comm c]; infer_instance

instance (c : E) : IsGaussian (μ.map (fun x ↦ x - c)) := by simp_rw [sub_eq_add_neg]; infer_instance

instance : IsGaussian (μ.map (fun x ↦ -x)) := by
  change IsGaussian (μ.map (ContinuousLinearEquiv.neg ℝ))
  infer_instance

instance (c : E) : IsGaussian (μ.map (fun x ↦ c - x)) := by
  simp_rw [sub_eq_add_neg]
  suffices IsGaussian ((μ.map (fun x ↦ -x)).map (fun x ↦ c + x)) by
    rwa [Measure.map_map (by fun_prop) (by fun_prop), Function.comp_def] at this
  infer_instance

/-- A product of Gaussian distributions is Gaussian. -/
instance [SecondCountableTopologyEither E F] {ν : Measure F} [IsGaussian ν] :
    IsGaussian (μ.prod ν) := by
  refine isGaussian_of_charFunDual_eq fun L ↦ ?_
  rw [charFunDual_prod, IsGaussian.charFunDual_eq, IsGaussian.charFunDual_eq, ← Complex.exp_add]
  congr
  let (eq := hL₁) L₁ := L.comp (.inl ℝ E F)
  let (eq := hL₂) L₂ := L.comp (.inr ℝ E F)
  rw [← hL₁, ← hL₂, sub_add_sub_comm, ← add_mul]
  congr
  · simp_rw [integral_complex_ofReal]
    rw [integral_continuousLinearMap_prod' (IsGaussian.integrable_dual μ (L.comp (.inl ℝ E F)))
      (IsGaussian.integrable_dual ν (L.comp (.inr ℝ E F)))]
    norm_cast
  · field_simp
    rw [variance_dual_prod' (IsGaussian.memLp_dual μ (L.comp (.inl ℝ E F)) 2 (by simp))
      (IsGaussian.memLp_dual ν (L.comp (.inr ℝ E F)) 2 (by simp))]
    norm_cast

end ProbabilityTheory
