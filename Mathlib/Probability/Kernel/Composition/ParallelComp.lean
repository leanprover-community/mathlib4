/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Probability.Kernel.Composition.Basic

/-!

# Parallel composition of kernels

Two kernels `κ : Kernel α β` and `η : Kernel γ δ` can be applied in parallel to give a kernel
`κ ∥ₖ η` from `α × γ` to `β × δ`: `(κ ∥ₖ η) (a, c) = (κ a).prod (η c)`.

## Main definitions

* `parallelComp (κ : Kernel α β) (η : Kernel γ δ) : Kernel (α × γ) (β × δ)`: parallel composition
  of two s-finite kernels. We define a notation `κ ∥ₖ η = parallelComp κ η`.
  `∫⁻ bd, g bd ∂(κ ∥ₖ η) ac = ∫⁻ b, ∫⁻ d, g (b, d) ∂η ac.2 ∂κ ac.1`

## Main statements

* `parallelComp_comp_copy`: `(κ ∥ₖ η) ∘ₖ (copy α) = κ ×ₖ η`
* `deterministic_comp_copy`: for a deterministic kernel, copying then applying the kernel to
  the two copies is the same as first applying the kernel then copying. That is, if `κ` is
  a deterministic kernel, `(κ ∥ₖ κ) ∘ₖ copy α = copy β ∘ₖ κ`.

## Notations

* `κ ∥ₖ η = ProbabilityTheory.Kernel.parallelComp κ η`

-/

open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {α β γ δ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}
  {κ : Kernel α β} {η : Kernel γ δ} {x : α × γ}

open Classical in
/-- Parallel product of two kernels. -/
noncomputable
def parallelComp (κ : Kernel α β) (η : Kernel γ δ) : Kernel (α × γ) (β × δ) :=
  if h : IsSFiniteKernel κ ∧ IsSFiniteKernel η then
  { toFun := fun x ↦ (κ x.1).prod (η x.2)
    measurable' := by
      have hκ := h.1
      have hη := h.2
      refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
      simp_rw [Measure.prod_apply hs]
      refine Measurable.lintegral_kernel_prod_right'
        (f := fun y ↦ prodMkLeft α η y.1 (Prod.mk y.2 ⁻¹' s)) (κ := prodMkRight γ κ) ?_
      have : (fun y ↦ prodMkLeft α η y.1 (Prod.mk y.2 ⁻¹' s))
          = fun y ↦ prodMkRight β (prodMkLeft α η) y (Prod.mk y.2 ⁻¹' s) := rfl
      rw [this]
      exact measurable_kernel_prod_mk_left (measurable_fst.snd.prod_mk measurable_snd hs) }
  else 0

@[inherit_doc]
scoped[ProbabilityTheory] infixl:100 " ∥ₖ " => ProbabilityTheory.Kernel.parallelComp

@[simp]
lemma parallelComp_of_not_isSFiniteKernel_left (η : Kernel γ δ) (h : ¬ IsSFiniteKernel κ) :
    κ ∥ₖ η = 0 := by
  rw [parallelComp, dif_neg]
  simp [h]

@[simp]
lemma parallelComp_of_not_isSFiniteKernel_right (κ : Kernel α β) (h : ¬ IsSFiniteKernel η) :
    κ ∥ₖ η = 0 := by
  rw [parallelComp, dif_neg]
  simp [h]

lemma parallelComp_apply (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel γ δ) [IsSFiniteKernel η] (x : α × γ) :
    (κ ∥ₖ η) x = (κ x.1).prod (η x.2) := by
  rw [parallelComp, dif_pos ⟨inferInstance, inferInstance⟩]
  rfl

lemma parallelComp_apply' [IsSFiniteKernel κ] [IsSFiniteKernel η]
    {s : Set (β × δ)} (hs : MeasurableSet s) :
    (κ ∥ₖ η) x s = ∫⁻ b, η x.2 (Prod.mk b ⁻¹' s) ∂κ x.1 := by
  rw [parallelComp_apply, Measure.prod_apply hs]

@[simp]
lemma parallelComp_apply_univ [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    (κ ∥ₖ η) x Set.univ = κ x.1 Set.univ * η x.2 Set.univ := by
  rw [parallelComp_apply, Measure.prod_apply .univ, mul_comm]
  simp

@[simp]
lemma parallelComp_zero_left (η : Kernel γ δ) : (0 : Kernel α β) ∥ₖ η = 0 := by
  by_cases h : IsSFiniteKernel η
  · ext; simp [parallelComp_apply]
  · exact parallelComp_of_not_isSFiniteKernel_right _ h

@[simp]
lemma parallelComp_zero_right (κ : Kernel α β) : κ ∥ₖ (0 : Kernel γ δ) = 0 := by
  by_cases h : IsSFiniteKernel κ
  · ext; simp [parallelComp_apply]
  · exact parallelComp_of_not_isSFiniteKernel_left _ h

lemma lintegral_parallelComp [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (ac : α × γ) {g : β × δ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ bd, g bd ∂(κ ∥ₖ η) ac = ∫⁻ b, ∫⁻ d, g (b, d) ∂η ac.2 ∂κ ac.1 := by
  rw [parallelComp_apply, MeasureTheory.lintegral_prod _ hg.aemeasurable]

lemma lintegral_parallelComp_symm [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (ac : α × γ) {g : β × δ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ bd, g bd ∂(κ ∥ₖ η) ac = ∫⁻ d, ∫⁻ b, g (b, d) ∂κ ac.1 ∂η ac.2 := by
  rw [parallelComp_apply, MeasureTheory.lintegral_prod_symm _ hg.aemeasurable]

lemma parallelComp_sum_left {ι : Type*} [Countable ι] (κ : ι → Kernel α β)
    [∀ i, IsSFiniteKernel (κ i)] (η : Kernel γ δ) :
    Kernel.sum κ ∥ₖ η = Kernel.sum fun i ↦ κ i ∥ₖ η := by
  by_cases h : IsSFiniteKernel η
  swap; · simp [h]
  ext x
  simp_rw [Kernel.sum_apply, parallelComp_apply, Kernel.sum_apply, Measure.prod_sum_left]

lemma parallelComp_sum_right {ι : Type*} [Countable ι] (κ : Kernel α β)
    (η : ι → Kernel γ δ) [∀ i, IsSFiniteKernel (η i)] :
    κ ∥ₖ Kernel.sum η = Kernel.sum fun i ↦ κ ∥ₖ η i := by
  by_cases h : IsSFiniteKernel κ
  swap; · simp [h]
  ext x
  simp_rw [Kernel.sum_apply, parallelComp_apply, Kernel.sum_apply, Measure.prod_sum_right]

instance [IsMarkovKernel κ] [IsMarkovKernel η] : IsMarkovKernel (κ ∥ₖ η) :=
  ⟨fun x ↦ ⟨by simp [parallelComp_apply_univ]⟩⟩

instance [IsZeroOrMarkovKernel κ] [IsZeroOrMarkovKernel η] : IsZeroOrMarkovKernel (κ ∥ₖ η) := by
  obtain rfl | _ := eq_zero_or_isMarkovKernel κ <;> obtain rfl | _ := eq_zero_or_isMarkovKernel η
  all_goals simpa using by infer_instance

instance [IsFiniteKernel κ] [IsFiniteKernel η] : IsFiniteKernel (κ ∥ₖ η) := by
  refine ⟨⟨IsFiniteKernel.bound κ * IsFiniteKernel.bound η,
    ENNReal.mul_lt_top (IsFiniteKernel.bound_lt_top κ) (IsFiniteKernel.bound_lt_top η),
    fun a ↦ ?_⟩⟩
  calc (κ ∥ₖ η) a Set.univ
  _ = κ a.1 Set.univ * η a.2 Set.univ := parallelComp_apply_univ
  _ ≤ IsFiniteKernel.bound κ * IsFiniteKernel.bound η := by
    gcongr
    · exact measure_le_bound κ a.1 Set.univ
    · exact measure_le_bound η a.2 Set.univ

instance [IsSFiniteKernel κ] [IsSFiniteKernel η] : IsSFiniteKernel (κ ∥ₖ η) := by
  simp_rw [← kernel_sum_seq κ, ← kernel_sum_seq η, parallelComp_sum_left, parallelComp_sum_right]
  infer_instance

lemma parallelComp_comp_copy (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel α γ) [IsSFiniteKernel η] :
    (κ ∥ₖ η) ∘ₖ (copy α) = κ ×ₖ η := by
  ext a s hs
  simp_rw [prod_apply, comp_apply, copy_apply, Measure.bind_apply hs (Kernel.measurable _)]
  rw [lintegral_dirac']
  swap; · exact Kernel.measurable_coe _ hs
  rw [parallelComp_apply]

lemma swap_parallelComp : swap β δ ∘ₖ (κ ∥ₖ η) = η ∥ₖ κ ∘ₖ swap α γ := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  by_cases hη : IsSFiniteKernel η
  swap; · simp [hη]
  ext ac s hs
  simp_rw [comp_apply, parallelComp_apply, Measure.bind_apply hs (Kernel.measurable _), swap_apply,
    lintegral_dirac' _ (Kernel.measurable_coe _ hs), parallelComp_apply' hs, Prod.fst_swap,
    Prod.snd_swap]
  rw [MeasureTheory.lintegral_prod_symm]
  swap; · exact ((Kernel.id.measurable_coe hs).comp measurable_swap).aemeasurable
  congr with d
  simp_rw [Prod.swap_prod_mk, Measure.dirac_apply' _ hs]
  have h_eq (x : β) : s.indicator (1 : δ × β → ℝ≥0∞) (d, x) = (Prod.mk d ⁻¹' s).indicator 1 x := by
    by_cases h : (d, x) ∈ s <;> simp [h]
  simp_rw [h_eq]
  rw [lintegral_indicator]
  · simp
  · exact measurable_prod_mk_left hs

/-- For a deterministic kernel, copying then applying the kernel to the two copies is the same
as first applying the kernel then copying. -/
lemma deterministic_comp_copy {f : α → β} (hf : Measurable f) :
    (Kernel.deterministic f hf ∥ₖ Kernel.deterministic f hf) ∘ₖ Kernel.copy α
      = Kernel.copy β ∘ₖ Kernel.deterministic f hf := by
  simp_rw [Kernel.parallelComp_comp_copy, Kernel.deterministic_prod_deterministic,
    Kernel.copy, Kernel.deterministic_comp_deterministic, Function.comp_def]

end ProbabilityTheory.Kernel
