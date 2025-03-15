/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Moments.SubGaussian

/-!
# The moment generating function of a bounded random variable

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

-/

open MeasureTheory Set Real

open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {a b x t : ℝ} {ω : Ω}

lemma eq_mul_add_mul_of_mem_Icc (hx : x ∈ Icc a b) :
    x = (1 - (x - a) / (b - a)) * a + (x - a) / (b - a) * b := by
  by_cases hab : a = b
  · simp only [hab, sub_self, div_zero, sub_zero, one_mul, zero_mul, add_zero, exp_le_exp]
    simpa [hab] using hx
  symm
  calc (1 - (x - a) / (b - a)) * a + (x - a) / (b - a) * b
  _ = a + (x - a)/(b - a) * (b - a) := by ring
  _ = a + (x - a) := by congr; rw [div_mul_cancel₀]; rw [sub_ne_zero]; exact Ne.symm hab
  _ = x := by abel

lemma ConvexOn.le_of_mem_Icc {f : ℝ → ℝ} (hf : ConvexOn ℝ (Icc a b) f) (hx : x ∈ Icc a b) :
    f x ≤ (1 - (x - a) / (b - a)) * f a + (x - a) / (b - a) * f b := by
  have hab : a ≤ b := by by_contra h_contra; simp [h_contra] at hx
  conv_lhs => rw [eq_mul_add_mul_of_mem_Icc hx]
  -- 3 inequalities to help `gcongr` and `positivity`
  have h1 : 0 ≤ x - a := sub_nonneg.mpr hx.1
  have h2 : x ≤ b := hx.2
  have h3 : 0 ≤ b - a := sub_nonneg.mpr hab
  have h_nonneg_left : 0 ≤ 1 - (x - a) / (b - a) := by
    by_cases hab' : a = b
    · simp [hab']
    rw [sub_nonneg, div_le_one]
    · gcongr
    · rw [sub_pos]
      exact lt_of_le_of_ne hab hab'
  have h_nonneg_right : 0 ≤ (x - a) / (b - a) := by positivity
  refine hf.2 (by simp [hab] : a ∈ Icc a b) (by simp [hab] : b ∈ Icc a b)
    h_nonneg_left h_nonneg_right ?_
  abel

lemma mgf_le_of_mem_Icc [IsProbabilityMeasure μ] (hXm : AEMeasurable X μ)
    (h : ∀ᵐ ω ∂μ, X ω ∈ Icc a b) (t : ℝ) :
    mgf X μ t ≤ (1 - (μ[X] - a)/(b - a)) * exp (t * a) + (μ[X] - a)/(b - a) * exp (t * b) := by
  by_cases hab : a = b
  · simp only [hab, sub_self, div_zero, sub_zero, one_mul, zero_mul, add_zero, mgf]
    refine le_of_eq (integral_eq_const ?_)
    filter_upwards [h] with ω hω
    congr
    simpa [hab] using hω
  have h_exp x (hx : x ∈ Icc a b) : exp (t * x)
      ≤ (1 - (x - a) / (b - a)) * exp (t * a) + (x - a) / (b - a) * exp (t * b) := by
    refine ConvexOn.le_of_mem_Icc (f := fun x ↦ exp (t * x)) ?_ hx
    refine ConvexOn.subset ?_ (subset_univ (Icc a b)) (convex_Icc a b)
    let lin : ℝ →ₗ[ℝ] ℝ := LinearMap.mulLeft ℝ (t : ℝ)
    convert (convexOn_exp.comp_linearMap lin) using 1
  have hX : Integrable X μ := integrable_of_le_of_le hXm.aestronglyMeasurable
      (h.mono fun x hx ↦ hx.1) (h.mono fun x hx ↦ hx.2) (integrable_const a) (integrable_const b)
  calc ∫ ω, exp (t * X ω) ∂μ
  _ ≤ ∫ ω, (1 - (X ω - a) / (b - a)) * exp (t * a) + (X ω - a) / (b - a) * exp (t * b) ∂μ := by
    refine integral_mono_of_nonneg ?_ (by fun_prop) ?_
    · exact ae_of_all _ fun _ ↦ by positivity
    · filter_upwards [h] with ω hω using h_exp (X ω) hω
  _ = (1 - (μ[X] - a) / (b - a)) * exp (t * a) + (μ[X] - a) / (b - a) * exp (t * b) := by
    rw [integral_add, integral_mul_right, integral_mul_right, integral_sub, integral_div,
      integral_sub]
    · simp
    all_goals { fun_prop }

lemma aemeasurable_dirac [MeasurableSingletonClass Ω] {f : Ω → ℝ} :
    AEMeasurable f (Measure.dirac ω) :=
  ⟨fun _ ↦ f ω, measurable_const, by simp only [ae_dirac_eq]; rfl⟩

lemma aestronglyMeasurable_dirac [MeasurableSingletonClass Ω] {f : Ω → ℝ} :
    AEStronglyMeasurable f (Measure.dirac ω) :=
  ⟨fun _ ↦ f ω, stronglyMeasurable_const, by simp only [ae_dirac_eq]; rfl⟩

@[fun_prop]
lemma integrable_dirac [MeasurableSingletonClass Ω] {f : Ω → ℝ} :
    Integrable f (Measure.dirac ω) :=
  ⟨aestronglyMeasurable_dirac, by simp [HasFiniteIntegral, lintegral_dirac]⟩

lemma mgf_dirac' [MeasurableSingletonClass Ω] :
    mgf X (Measure.dirac ω) t = exp (t * X ω) := by
  rw [mgf, integral_dirac]

lemma mgf_id_dirac : mgf id (Measure.dirac x) t = exp (t * x) := by rw [mgf_dirac', id_eq]

lemma mgf_add_measure {ν : Measure Ω}
    (hμ : Integrable (fun ω ↦ exp (t * X ω)) μ) (hν : Integrable (fun ω ↦ exp (t * X ω)) ν) :
    mgf X (μ + ν) t = mgf X μ t + mgf X ν t := by
  rw [mgf, integral_add_measure hμ hν, mgf, mgf]

lemma mgf_smul_measure (c : ℝ≥0∞) : mgf X (c • μ) t = c.toReal * mgf X μ t := by
  rw [mgf, integral_smul_measure, mgf, smul_eq_mul]

lemma integral_eq_of_two_points_of_measurable [IsProbabilityMeasure μ] (hXm : Measurable X)
    (h : ∀ᵐ ω ∂μ, X ω = a ∨ X ω = b) (hab : a ≠ b) :
    μ[X] = (μ (X ⁻¹' {a})).toReal * a + (μ (X ⁻¹' {b})).toReal * b := by
  rw [← setIntegral_univ]
  have : (univ : Set Ω) =ᵐ[μ] ((X ⁻¹' {a}) ∪ (X ⁻¹' {b}) : Set Ω) := by
    filter_upwards [h] with ω hω
    simp only [eq_iff_iff]
    suffices ω ∈ univ ↔ ω ∈ (X ⁻¹' {a} ∪ X ⁻¹' {b}) by exact this
    simpa using hω
  rw [setIntegral_congr_set this, setIntegral_union]
  rotate_left
  · rw [Set.disjoint_iff]
    intro ω
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_empty_iff_false, imp_false,
      not_and]
    intro hωa
    rwa [hωa]
  · exact hXm (measurableSet_singleton _)
  · rw [integrableOn_congr_fun (g := fun _ ↦ a)]
    · exact (integrable_const _).integrableOn
    · intro ω hω
      simpa using hω
    · exact hXm (measurableSet_singleton _)
  · rw [integrableOn_congr_fun (g := fun _ ↦ b)]
    · exact (integrable_const _).integrableOn
    · intro ω hω
      simpa using hω
    · exact hXm (measurableSet_singleton _)
  congr
  · rw [setIntegral_congr_fun (g := fun _ ↦ a)]
    · simp
    · exact hXm (measurableSet_singleton _)
    · intro ω hω
      simpa using hω
  · rw [setIntegral_congr_fun (g := fun _ ↦ b)]
    · simp
    · exact hXm (measurableSet_singleton _)
    · intro ω hω
      simpa using hω

lemma integral_eq_of_two_points [IsProbabilityMeasure μ] (hXm : AEMeasurable X μ)
    (h : ∀ᵐ ω ∂μ, X ω = a ∨ X ω = b) (hab : a ≠ b) :
    μ[X] = (μ (X ⁻¹' {a})).toReal * a + (μ (X ⁻¹' {b})).toReal * b := by
  sorry

lemma measure_left_eq_of_two_points [IsProbabilityMeasure μ] (hXm : AEMeasurable X μ)
    (h : ∀ᵐ ω ∂μ, X ω = a ∨ X ω = b) :
    (μ (X ⁻¹' {a})).toReal = 1 - (μ[X] - a) / (b - a) := by
  by_cases hab : a = b
  · simp only [hab, sub_self, div_zero, sub_zero]
    sorry
  sorry

lemma measure_right_eq_of_two_points [IsProbabilityMeasure μ] (hXm : AEMeasurable X μ)
    (h : ∀ᵐ ω ∂μ, X ω = a ∨ X ω = b) (hab : a ≠ b) :
    (μ (X ⁻¹' {b})).toReal = (μ[X] - a) / (b - a) := by
  sorry

lemma mgf_of_two_points [IsProbabilityMeasure μ] (hXm : AEMeasurable X μ)
    (h : ∀ᵐ ω ∂μ, X ω = a ∨ X ω = b) (t : ℝ) :
    mgf X μ t = (1 - (μ[X] - a)/(b - a)) * exp (t * a) + (μ[X] - a)/(b - a) * exp (t * b) := by
  by_cases hab : a = b
  · simp only [hab, sub_self, div_zero, sub_zero, one_mul, zero_mul, add_zero]
    sorry
  rw [← mgf_id_map hXm]
  have : μ.map X = μ (X ⁻¹' {a}) • Measure.dirac a + μ (X ⁻¹' {b}) • Measure.dirac b := by
    sorry
  rw [this, mgf_add_measure, mgf_smul_measure, mgf_smul_measure, mgf_id_dirac, mgf_id_dirac]
  rotate_left
  · exact integrable_dirac.smul_measure (measure_ne_top _ _)
  · exact integrable_dirac.smul_measure (measure_ne_top _ _)
  congr
  · exact measure_left_eq_of_two_points hXm h
  · exact measure_right_eq_of_two_points hXm h hab

end  ProbabilityTheory
