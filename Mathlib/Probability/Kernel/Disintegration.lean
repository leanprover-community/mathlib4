/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Kexing Ying
-/
import Mathlib.Probability.Kernel.Disintegration.Basic

#align_import probability.kernel.disintegration from "leanprover-community/mathlib"@"6315581f5650ffa2fbdbbbedc41243c8d7070981"

/-!
# Disintegration of measures on product spaces

Let `ρ` be a finite measure on `α × Ω`, where `Ω` is a standard Borel space. In mathlib terms, `Ω`
verifies `[Nonempty Ω] [MeasurableSpace Ω] [StandardBorelSpace Ω]`.
Then there exists a kernel `ρ.condKernel : kernel α Ω` such that for any measurable set
`s : Set (α × Ω)`, `ρ s = ∫⁻ a, ρ.condKernel a {x | (a, x) ∈ s} ∂ρ.fst`.

In terms of kernels, `ρ.condKernel` is such that for any measurable space `γ`, we
have a disintegration of the constant kernel from `γ` with value `ρ`:
`kernel.const γ ρ = (kernel.const γ ρ.fst) ⊗ₖ (kernel.prodMkLeft γ (condKernel ρ))`,
where `ρ.fst` is the marginal measure of `ρ` on `α`. In particular, `ρ = ρ.fst ⊗ₘ ρ.condKernel`.

In order to obtain a disintegration for any standard Borel space, we use that these spaces embed
measurably into `ℝ`: it then suffices to define a suitable kernel for `Ω = ℝ`. In the real case,
we define a conditional kernel by taking for each `a : α` the measure associated to the Stieltjes
function `condCDF ρ a` (the conditional cumulative distribution function).

## Main definitions

* `MeasureTheory.Measure.condKernel ρ : kernel α Ω`: conditional kernel described above.

## Main statements

* `ProbabilityTheory.lintegral_condKernel`:
  `∫⁻ a, ∫⁻ ω, f (a, ω) ∂(ρ.condKernel a) ∂ρ.fst = ∫⁻ x, f x ∂ρ`
* `ProbabilityTheory.lintegral_condKernel_mem`:
  `∫⁻ a, ρ.condKernel a {x | (a, x) ∈ s} ∂ρ.fst = ρ s`
* `ProbabilityTheory.kernel.const_eq_compProd`:
  `kernel.const γ ρ = (kernel.const γ ρ.fst) ⊗ₖ (kernel.prodMkLeft γ ρ.condKernel)`
* `ProbabilityTheory.measure_eq_compProd`: `ρ = ρ.fst ⊗ₘ ρ.condKernel`
* `ProbabilityTheory.eq_condKernel_of_measure_eq_compProd`: a.e. uniqueness of `condKernel`

-/


open MeasureTheory Set Filter

open scoped ENNReal MeasureTheory Topology ProbabilityTheory

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α}

#noalign probability_theory.cond_kernel_real
#noalign probability_theory.cond_kernel_real_Iic
#noalign probability_theory.set_lintegral_cond_kernel_real_Iic
#noalign probability_theory.set_lintegral_cond_kernel_real_univ
#noalign probability_theory.lintegral_cond_kernel_real_univ
#noalign probability_theory.set_lintegral_cond_kernel_real_prod
#noalign probability_theory.lintegral_cond_kernel_real_mem
#noalign probability_theory.kernel.const_eq_comp_prod_real
#noalign probability_theory.measure_eq_comp_prod_real
#noalign probability_theory.lintegral_cond_kernel_real
#noalign probability_theory.ae_cond_kernel_real_eq_one

section StandardBorel

/-! ### Disintegration of measures on standard Borel spaces

Since every standard Borel space embeds measurably into `ℝ`, we can generalize the disintegration
property on `ℝ` to all these spaces. -/


variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [Nonempty Ω] (ρ : Measure (α × Ω)) [IsFiniteMeasure ρ]

#noalign probability_theory.exists_cond_kernel
#noalign probability_theory.cond_kernel_def
#noalign probability_theory.kernel.const_unit_eq_comp_prod

/-- **Disintegration** of finite product measures on `α × Ω`, where `Ω` is standard Borel. Such a
measure can be written as the composition-product of the constant kernel with value `ρ.fst`
(marginal measure over `α`) and a Markov kernel from `α` to `Ω`. We call that Markov kernel
`ProbabilityTheory.condKernel ρ`. -/
theorem measure_eq_compProd : ρ = ρ.fst ⊗ₘ ρ.condKernel := by
  rw [Measure.compProd_fst_condKernel]
#align probability_theory.measure_eq_comp_prod ProbabilityTheory.measure_eq_compProd

#noalign probability_theory.kernel.const_eq_comp_prod

/-- Auxiliary lemma for `condKernel_apply_of_ne_zero`. -/
lemma condKernel_apply_of_ne_zero_of_measurableSet [MeasurableSingletonClass α]
    {ρ : Measure (α × Ω)} [IsFiniteMeasure ρ]
    {x : α} (hx : ρ.fst {x} ≠ 0) {s : Set Ω} (hs : MeasurableSet s) :
    ρ.condKernel x s = (ρ.fst {x})⁻¹ * ρ ({x} ×ˢ s) := by
  nth_rewrite 3 [measure_eq_compProd ρ]
  rw [Measure.compProd_apply (measurableSet_prod.mpr (Or.inl ⟨measurableSet_singleton x, hs⟩))]
  classical
  have : ∀ a, ρ.condKernel a (Prod.mk a ⁻¹' {x} ×ˢ s)
      = ({x} : Set α).indicator (fun a ↦ ρ.condKernel a s) a := by
    intro a
    by_cases hax : a = x
    · simp only [hax, Set.singleton_prod, Set.mem_singleton_iff, Set.indicator_of_mem]
      congr with y
      simp
    · simp only [Set.singleton_prod, Set.mem_singleton_iff, hax, not_false_eq_true,
        Set.indicator_of_not_mem]
      have : Prod.mk a ⁻¹' (Prod.mk x '' s) = ∅ := by
        ext y
        simp [Ne.symm hax]
      simp only [this, measure_empty]
  simp_rw [this]
  rw [MeasureTheory.lintegral_indicator _ (measurableSet_singleton x)]
  simp only [Measure.restrict_singleton, lintegral_smul_measure, lintegral_dirac]
  rw [← mul_assoc, ENNReal.inv_mul_cancel hx (measure_ne_top ρ.fst _), one_mul]

/-- If the singleton `{x}` has non-zero mass for `ρ.fst`, then for all `s : Set Ω`,
`ρ.condKernel x s = (ρ.fst {x})⁻¹ * ρ ({x} ×ˢ s)` . -/
lemma condKernel_apply_of_ne_zero [MeasurableSingletonClass α]
    {ρ : Measure (α × Ω)} [IsFiniteMeasure ρ] {x : α} (hx : ρ.fst {x} ≠ 0)
    (s : Set Ω) :
    ρ.condKernel x s = (ρ.fst {x})⁻¹ * ρ ({x} ×ˢ s) := by
  have : ρ.condKernel x s = ((ρ.fst {x})⁻¹ • ρ).comap (fun (y : Ω) ↦ (x, y)) s := by
    congr 2 with s hs
    simp [condKernel_apply_of_ne_zero_of_measurableSet hx hs,
      (measurableEmbedding_prod_mk_left x).comap_apply]
  simp [this, (measurableEmbedding_prod_mk_left x).comap_apply, hx]

theorem Measure.lintegral_condKernel_mem {s : Set (α × Ω)} (hs : MeasurableSet s) :
    ∫⁻ a, ρ.condKernel a {x | (a, x) ∈ s} ∂ρ.fst = ρ s := by
  conv_rhs => rw [measure_eq_compProd ρ]
  simp_rw [Measure.compProd_apply hs]
  rfl
#align probability_theory.lintegral_cond_kernel_mem ProbabilityTheory.Measure.lintegral_condKernel_mem

theorem Measure.set_lintegral_condKernel_eq_measure_prod {s : Set α} (hs : MeasurableSet s) {t : Set Ω}
    (ht : MeasurableSet t) : ∫⁻ a in s, ρ.condKernel a t ∂ρ.fst = ρ (s ×ˢ t) := by
  have : ρ (s ×ˢ t) = (ρ.fst ⊗ₘ ρ.condKernel) (s ×ˢ t) := by
    congr; exact measure_eq_compProd ρ
  rw [this, Measure.compProd_apply (hs.prod ht)]
  classical
  have : ∀ a, ρ.condKernel a (Prod.mk a ⁻¹' s ×ˢ t)
      = s.indicator (fun a ↦ ρ.condKernel a t) a := by
    intro a
    by_cases ha : a ∈ s <;> simp [ha]
  simp_rw [this]
  rw [lintegral_indicator _ hs]
#align probability_theory.set_lintegral_cond_kernel_eq_measure_prod ProbabilityTheory.Measure.set_lintegral_condKernel_eq_measure_prod

theorem Measure.lintegral_condKernel {f : α × Ω → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ a, ∫⁻ ω, f (a, ω) ∂ρ.condKernel a ∂ρ.fst = ∫⁻ x, f x ∂ρ := by
  conv_rhs => rw [measure_eq_compProd ρ]
  rw [Measure.lintegral_compProd hf]
#align probability_theory.lintegral_cond_kernel ProbabilityTheory.lintegral_condKernel

theorem Measure.set_lintegral_condKernel {f : α × Ω → ℝ≥0∞} (hf : Measurable f) {s : Set α}
    (hs : MeasurableSet s) {t : Set Ω} (ht : MeasurableSet t) :
    ∫⁻ a in s, ∫⁻ ω in t, f (a, ω) ∂ρ.condKernel a ∂ρ.fst = ∫⁻ x in s ×ˢ t, f x ∂ρ := by
  conv_rhs => rw [measure_eq_compProd ρ]
  rw [Measure.set_lintegral_compProd hf hs ht]
#align probability_theory.set_lintegral_cond_kernel ProbabilityTheory.set_lintegral_condKernel

theorem Measure.set_lintegral_condKernel_univ_right {f : α × Ω → ℝ≥0∞} (hf : Measurable f) {s : Set α}
    (hs : MeasurableSet s) :
    ∫⁻ a in s, ∫⁻ ω, f (a, ω) ∂ρ.condKernel a ∂ρ.fst = ∫⁻ x in s ×ˢ univ, f x ∂ρ := by
  rw [← set_lintegral_condKernel ρ hf hs MeasurableSet.univ]; simp_rw [Measure.restrict_univ]
#align probability_theory.set_lintegral_cond_kernel_univ_right ProbabilityTheory.set_lintegral_condKernel_univ_right

theorem Measure.set_lintegral_condKernel_univ_left {f : α × Ω → ℝ≥0∞} (hf : Measurable f) {t : Set Ω}
    (ht : MeasurableSet t) :
    ∫⁻ a, ∫⁻ ω in t, f (a, ω) ∂ρ.condKernel a ∂ρ.fst = ∫⁻ x in univ ×ˢ t, f x ∂ρ := by
  rw [← set_lintegral_condKernel ρ hf MeasurableSet.univ ht]; simp_rw [Measure.restrict_univ]
#align probability_theory.set_lintegral_cond_kernel_univ_left ProbabilityTheory.set_lintegral_condKernel_univ_left

section IntegralCondKernel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem _root_.MeasureTheory.AEStronglyMeasurable.integral_condKernel {ρ : Measure (α × Ω)}
    [IsFiniteMeasure ρ] {f : α × Ω → E} (hf : AEStronglyMeasurable f ρ) :
    AEStronglyMeasurable (fun x ↦ ∫ y, f (x, y) ∂ρ.condKernel x) ρ.fst := by
  rw [measure_eq_compProd ρ] at hf
  exact AEStronglyMeasurable.integral_kernel_compProd hf
#align measure_theory.ae_strongly_measurable.integral_cond_kernel MeasureTheory.AEStronglyMeasurable.integral_condKernel

theorem Measure.integral_condKernel {ρ : Measure (α × Ω)} [IsFiniteMeasure ρ] {f : α × Ω → E}
    (hf : Integrable f ρ) : ∫ a, ∫ x, f (a, x) ∂ρ.condKernel a ∂ρ.fst = ∫ ω, f ω ∂ρ := by
  conv_rhs => rw [measure_eq_compProd ρ]
  have hf': Integrable f (ρ.fst ⊗ₘ ρ.condKernel) := by rwa [measure_eq_compProd ρ] at hf
  rw [Measure.integral_compProd hf']
#align probability_theory.integral_cond_kernel ProbabilityTheory.integral_condKernel

theorem Measure.set_integral_condKernel {ρ : Measure (α × Ω)} [IsFiniteMeasure ρ] {f : α × Ω → E}
    {s : Set α} (hs : MeasurableSet s) {t : Set Ω} (ht : MeasurableSet t)
    (hf : IntegrableOn f (s ×ˢ t) ρ) :
    ∫ a in s, ∫ ω in t, f (a, ω) ∂ρ.condKernel a ∂ρ.fst = ∫ x in s ×ˢ t, f x ∂ρ := by
  conv_rhs => rw [measure_eq_compProd ρ]
  rw [Measure.set_integral_compProd hs ht]
  rwa [measure_eq_compProd ρ] at hf
#align probability_theory.set_integral_cond_kernel ProbabilityTheory.set_integral_condKernel

theorem Measure.set_integral_condKernel_univ_right {ρ : Measure (α × Ω)} [IsFiniteMeasure ρ] {f : α × Ω → E}
    {s : Set α} (hs : MeasurableSet s) (hf : IntegrableOn f (s ×ˢ univ) ρ) :
    ∫ a in s, ∫ ω, f (a, ω) ∂ρ.condKernel a ∂ρ.fst = ∫ x in s ×ˢ univ, f x ∂ρ := by
  rw [← set_integral_condKernel hs MeasurableSet.univ hf]; simp_rw [Measure.restrict_univ]
#align probability_theory.set_integral_cond_kernel_univ_right ProbabilityTheory.set_integral_condKernel_univ_right

theorem Measure.set_integral_condKernel_univ_left {ρ : Measure (α × Ω)} [IsFiniteMeasure ρ] {f : α × Ω → E}
    {t : Set Ω} (ht : MeasurableSet t) (hf : IntegrableOn f (univ ×ˢ t) ρ) :
    ∫ a, ∫ ω in t, f (a, ω) ∂ρ.condKernel a ∂ρ.fst = ∫ x in univ ×ˢ t, f x ∂ρ := by
  rw [← set_integral_condKernel MeasurableSet.univ ht hf]; simp_rw [Measure.restrict_univ]
#align probability_theory.set_integral_cond_kernel_univ_left ProbabilityTheory.set_integral_condKernel_univ_left

end IntegralCondKernel

end StandardBorel

end ProbabilityTheory

namespace MeasureTheory

/-! ### Integrability

We place these lemmas in the `MeasureTheory` namespace to enable dot notation. -/

open ProbabilityTheory

variable {α Ω E F : Type*} {mα : MeasurableSpace α} [MeasurableSpace Ω]
  [StandardBorelSpace Ω] [Nonempty Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] {ρ : Measure (α × Ω)} [IsFiniteMeasure ρ]

theorem AEStronglyMeasurable.ae_integrable_condKernel_iff {f : α × Ω → F}
    (hf : AEStronglyMeasurable f ρ) :
    (∀ᵐ a ∂ρ.fst, Integrable (fun ω ↦ f (a, ω)) (ρ.condKernel a)) ∧
      Integrable (fun a ↦ ∫ ω, ‖f (a, ω)‖ ∂ρ.condKernel a) ρ.fst ↔ Integrable f ρ := by
  rw [measure_eq_compProd ρ] at hf
  conv_rhs => rw [measure_eq_compProd ρ]
  rw [Measure.integrable_compProd_iff hf]
#align measure_theory.ae_strongly_measurable.ae_integrable_cond_kernel_iff MeasureTheory.AEStronglyMeasurable.ae_integrable_condKernel_iff

theorem Integrable.condKernel_ae {f : α × Ω → F} (hf_int : Integrable f ρ) :
    ∀ᵐ a ∂ρ.fst, Integrable (fun ω ↦ f (a, ω)) (ρ.condKernel a) := by
  have hf_ae : AEStronglyMeasurable f ρ := hf_int.1
  rw [← hf_ae.ae_integrable_condKernel_iff] at hf_int
  exact hf_int.1
#align measure_theory.integrable.cond_kernel_ae MeasureTheory.Integrable.condKernel_ae

theorem Integrable.integral_norm_condKernel {f : α × Ω → F} (hf_int : Integrable f ρ) :
    Integrable (fun x ↦ ∫ y, ‖f (x, y)‖ ∂ρ.condKernel x) ρ.fst := by
  have hf_ae : AEStronglyMeasurable f ρ := hf_int.1
  rw [← hf_ae.ae_integrable_condKernel_iff] at hf_int
  exact hf_int.2
#align measure_theory.integrable.integral_norm_cond_kernel MeasureTheory.Integrable.integral_norm_condKernel

theorem Integrable.norm_integral_condKernel {f : α × Ω → E} (hf_int : Integrable f ρ) :
    Integrable (fun x ↦ ‖∫ y, f (x, y) ∂ρ.condKernel x‖) ρ.fst := by
  refine hf_int.integral_norm_condKernel.mono hf_int.1.integral_condKernel.norm ?_
  refine eventually_of_forall fun x ↦ ?_
  rw [norm_norm]
  refine (norm_integral_le_integral_norm _).trans_eq (Real.norm_of_nonneg ?_).symm
  exact integral_nonneg_of_ae (eventually_of_forall fun y ↦ norm_nonneg _)
#align measure_theory.integrable.norm_integral_cond_kernel MeasureTheory.Integrable.norm_integral_condKernel

theorem Integrable.integral_condKernel {f : α × Ω → E} (hf_int : Integrable f ρ) :
    Integrable (fun x ↦ ∫ y, f (x, y) ∂ρ.condKernel x) ρ.fst :=
  (integrable_norm_iff hf_int.1.integral_condKernel).mp hf_int.norm_integral_condKernel
#align measure_theory.integrable.integral_cond_kernel MeasureTheory.Integrable.integral_condKernel

end MeasureTheory
