/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.MeasurableLIntegral

/-!

# Parallel composition of kernels

Two kernels `κ : Kernel α β` and `η : Kernel γ δ` can be applied in parallel to give a kernel
`κ ∥ₖ η` from `α × γ` to `β × δ`: `(κ ∥ₖ η) (a, c) = (κ a).prod (η c)`.

## Main definitions

* `parallelComp (κ : Kernel α β) (η : Kernel γ δ) : Kernel (α × γ) (β × δ)`: parallel composition
  of two s-finite kernels. We define a notation `κ ∥ₖ η = parallelComp κ η`.
  `∫⁻ bd, g bd ∂(κ ∥ₖ η) ac = ∫⁻ b, ∫⁻ d, g (b, d) ∂η ac.2 ∂κ ac.1`

## Notation

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
irreducible_def parallelComp (κ : Kernel α β) (η : Kernel γ δ) : Kernel (α × γ) (β × δ) :=
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
      exact measurable_kernel_prodMk_left (measurable_fst.snd.prodMk measurable_snd hs) }
  else 0

@[inherit_doc]
scoped[ProbabilityTheory] infixl:100 " ∥ₖ " => ProbabilityTheory.Kernel.parallelComp

@[simp]
lemma parallelComp_of_not_isSFiniteKernel_left (η : Kernel γ δ) (h : ¬ IsSFiniteKernel κ) :
    κ ∥ₖ η = 0 := by
  rw [parallelComp, dif_neg (not_and_of_not_left _ h)]

@[simp]
lemma parallelComp_of_not_isSFiniteKernel_right (κ : Kernel α β) (h : ¬ IsSFiniteKernel η) :
    κ ∥ₖ η = 0 := by
  rw [parallelComp, dif_neg (not_and_of_not_right _ h)]

lemma parallelComp_apply (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel γ δ) [IsSFiniteKernel η] (x : α × γ) :
    (κ ∥ₖ η) x = (κ x.1).prod (η x.2) := by
  rw [parallelComp, dif_pos ⟨inferInstance, inferInstance⟩, coe_mk]

lemma parallelComp_apply' [IsSFiniteKernel κ] [IsSFiniteKernel η]
    {s : Set (β × δ)} (hs : MeasurableSet s) :
    (κ ∥ₖ η) x s = ∫⁻ b, η x.2 (Prod.mk b ⁻¹' s) ∂κ x.1 := by
  rw [parallelComp_apply, Measure.prod_apply hs]

lemma parallelComp_apply_prod [IsSFiniteKernel κ] [IsSFiniteKernel η] (s : Set β) (t : Set δ) :
    (κ ∥ₖ η) x (s ×ˢ t) = (κ x.1 s) * (η x.2 t) := by
  rw [parallelComp_apply, Measure.prod_prod]

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

lemma deterministic_parallelComp_deterministic
    {f : α → γ} {g : β → δ} (hf : Measurable f) (hg : Measurable g) :
    (deterministic f hf) ∥ₖ (deterministic g hg)
      = deterministic (Prod.map f g) (hf.prodMap hg) := by
  ext x : 1
  simp_rw [parallelComp_apply, deterministic_apply, Prod.map, Measure.dirac_prod_dirac]

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
  refine ⟨⟨κ.bound * η.bound, ENNReal.mul_lt_top κ.bound_lt_top η.bound_lt_top, fun a ↦ ?_⟩⟩
  calc (κ ∥ₖ η) a Set.univ
  _ = κ a.1 Set.univ * η a.2 Set.univ := parallelComp_apply_univ
  _ ≤ κ.bound * η.bound := by
    gcongr
    · exact measure_le_bound κ a.1 Set.univ
    · exact measure_le_bound η a.2 Set.univ

instance : IsSFiniteKernel (κ ∥ₖ η) := by
  by_cases h : IsSFiniteKernel κ
  swap
  · simp only [h, not_false_eq_true, parallelComp_of_not_isSFiniteKernel_left]
    infer_instance
  by_cases h : IsSFiniteKernel η
  swap
  · simp only [h, not_false_eq_true, parallelComp_of_not_isSFiniteKernel_right]
    infer_instance
  simp_rw [← kernel_sum_seq κ, ← kernel_sum_seq η, parallelComp_sum_left, parallelComp_sum_right]
  infer_instance

end ProbabilityTheory.Kernel
