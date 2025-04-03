/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.CompMap

/-!
# Product and composition of kernels

We define the product `κ ×ₖ η` of s-finite kernels `κ : Kernel α β` and `η : Kernel α γ`, which is
a kernel from `α` to `β × γ`.

## Main definitions

* `prod (κ : Kernel α β) (η : Kernel α γ) : Kernel α (β × γ)`: product of 2 s-finite kernels.
  `∫⁻ bc, f bc ∂((κ ×ₖ η) a) = ∫⁻ b, ∫⁻ c, f (b, c) ∂(η a) ∂(κ a)`

## Main statements

* `lintegral_prod`: Lebesgue integral of a function against a product of   kernels.
* Instances stating that `IsMarkovKernel`, `IsZeroOrMarkovKernel`, `IsFiniteKernel` and
  `IsSFiniteKernel` are stable by product.

## Notations

* `κ ×ₖ η = ProbabilityTheory.Kernel.prod κ η`

-/


open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

namespace Kernel

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

variable {γ δ : Type*} {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}

/-- Product of two kernels. This is meaningful only when the kernels are s-finite. -/
noncomputable def prod (κ : Kernel α β) (η : Kernel α γ) : Kernel α (β × γ) :=
  κ ⊗ₖ swapLeft (prodMkLeft β η)

@[inherit_doc]
scoped[ProbabilityTheory] infixl:100 " ×ₖ " => ProbabilityTheory.Kernel.prod

@[simp]
lemma zero_prod (η : Kernel α γ) : (0 : Kernel α β) ×ₖ η = 0 := by simp [prod]

@[simp]
lemma prod_zero (κ : Kernel α β) : κ ×ₖ (0 : Kernel α γ) = 0 := by simp [prod]

@[simp]
lemma prod_of_not_isSFiniteKernel_left {κ : Kernel α β} (η : Kernel α γ) (h : ¬ IsSFiniteKernel κ) :
    κ ×ₖ η = 0 := by
  simp [prod, h]

@[simp]
lemma prod_of_not_isSFiniteKernel_right (κ : Kernel α β) {η : Kernel α γ}
    (h : ¬ IsSFiniteKernel η) :
    κ ×ₖ η = 0 := by
  cases isEmpty_or_nonempty β with
  | inl h => simp [eq_zero_of_isEmpty_right κ]
  | inr h =>
    rw [prod, compProd_of_not_isSFiniteKernel_right]
    simpa [swapLeft_prodMkLeft, isSFiniteKernel_prodMkRight_iff]

theorem prod_apply' (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η]
    (a : α) {s : Set (β × γ)} (hs : MeasurableSet s) :
    (κ ×ₖ η) a s = ∫⁻ b : β, (η a) (Prod.mk b ⁻¹' s) ∂κ a := by
  simp_rw [prod, compProd_apply hs, swapLeft_apply _ _, prodMkLeft_apply, Prod.swap_prod_mk]

lemma prod_apply (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η]
    (a : α) :
    (κ ×ₖ η) a = (κ a).prod (η a) := by
  ext s hs
  rw [prod_apply' _ _ _ hs, Measure.prod_apply hs]

lemma prod_const (μ : Measure β) [SFinite μ] (ν : Measure γ) [SFinite ν] :
    const α μ ×ₖ const α ν = const α (μ.prod ν) := by
  ext x
  rw [const_apply, prod_apply, const_apply, const_apply]

theorem lintegral_prod (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η]
    (a : α) {g : β × γ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ c, g c ∂(κ ×ₖ η) a = ∫⁻ b, ∫⁻ c, g (b, c) ∂η a ∂κ a := by
  simp_rw [prod, lintegral_compProd _ _ _ hg, swapLeft_apply, prodMkLeft_apply, Prod.swap_prod_mk]

theorem lintegral_prod_symm (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ)
    [IsSFiniteKernel η] (a : α) {g : β × γ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ c, g c ∂(κ ×ₖ η) a = ∫⁻ c, ∫⁻ b, g (b, c) ∂κ a ∂η a := by
  rw [prod_apply, MeasureTheory.lintegral_prod_symm _ hg.aemeasurable]

theorem lintegral_deterministic_prod {f : α → β} (hf : Measurable f) (κ : Kernel α γ)
    [IsSFiniteKernel κ] (a : α) {g : (β × γ) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ p, g p ∂((deterministic f hf) ×ₖ κ) a = ∫⁻ c, g (f a, c) ∂κ a := by
  rw [lintegral_prod _ _ _ hg, lintegral_deterministic' _ hg.lintegral_prod_right']

theorem lintegral_prod_deterministic {f : α → γ} (hf : Measurable f) (κ : Kernel α β)
    [IsSFiniteKernel κ] (a : α) {g : (β × γ) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ p, g p ∂(κ ×ₖ (deterministic f hf)) a = ∫⁻ b, g (b, f a) ∂κ a := by
  rw [lintegral_prod_symm _ _ _ hg, lintegral_deterministic' _ hg.lintegral_prod_left']

theorem lintegral_id_prod {f : (α × β) → ℝ≥0∞} (hf : Measurable f) (κ : Kernel α β)
    [IsSFiniteKernel κ] (a : α) :
    ∫⁻ p, f p ∂(Kernel.id ×ₖ κ) a = ∫⁻ b, f (a, b) ∂κ a := by
  rw [Kernel.id, lintegral_deterministic_prod _ _ _ hf, id_eq]

theorem lintegral_prod_id {f : (α × β) → ℝ≥0∞} (hf : Measurable f) (κ : Kernel β α)
    [IsSFiniteKernel κ] (b : β) :
    ∫⁻ p, f p ∂(κ ×ₖ Kernel.id) b = ∫⁻ a, f (a, b) ∂κ b := by
  rw [Kernel.id, lintegral_prod_deterministic _ _ _ hf, id_eq]

theorem deterministic_prod_apply' {f : α → β} (mf : Measurable f) (κ : Kernel α γ)
    [IsSFiniteKernel κ] (a : α) {s : Set (β × γ)} (hs : MeasurableSet s) :
    ((Kernel.deterministic f mf) ×ₖ κ) a s = κ a (Prod.mk (f a) ⁻¹' s) := by
  rw [prod_apply' _ _ _ hs, lintegral_deterministic']
  exact measurable_measure_prodMk_left hs

theorem id_prod_apply' (κ : Kernel α β) [IsSFiniteKernel κ] (a : α) {s : Set (α × β)}
    (hs : MeasurableSet s) : (Kernel.id ×ₖ κ) a s = κ a (Prod.mk a ⁻¹' s) := by
  rw [Kernel.id, deterministic_prod_apply' _ _ _ hs, id_eq]

instance IsMarkovKernel.prod (κ : Kernel α β) [IsMarkovKernel κ] (η : Kernel α γ)
    [IsMarkovKernel η] : IsMarkovKernel (κ ×ₖ η) := by rw [Kernel.prod]; infer_instance

nonrec instance IsZeroOrMarkovKernel.prod (κ : Kernel α β) [h : IsZeroOrMarkovKernel κ]
    (η : Kernel α γ) [IsZeroOrMarkovKernel η] : IsZeroOrMarkovKernel (κ ×ₖ η) := by
  rcases eq_zero_or_isMarkovKernel κ with rfl | h
  · simp only [prod, swapLeft_prodMkLeft, compProd_zero_left]; infer_instance
  rcases eq_zero_or_isMarkovKernel η with rfl | h'
  · simp only [prod, swapLeft, prodMkLeft_zero, comap_zero, compProd_zero_right]; infer_instance
  infer_instance

instance IsFiniteKernel.prod (κ : Kernel α β) [IsFiniteKernel κ] (η : Kernel α γ)
    [IsFiniteKernel η] : IsFiniteKernel (κ ×ₖ η) := by rw [Kernel.prod]; infer_instance

instance IsSFiniteKernel.prod (κ : Kernel α β) (η : Kernel α γ) :
    IsSFiniteKernel (κ ×ₖ η) := by rw [Kernel.prod]; infer_instance

@[simp] lemma fst_prod (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ) [IsMarkovKernel η] :
    fst (κ ×ₖ η) = κ := by
  rw [prod]; simp

@[simp] lemma snd_prod (κ : Kernel α β) [IsMarkovKernel κ] (η : Kernel α γ) [IsSFiniteKernel η] :
    snd (κ ×ₖ η) = η := by
  ext x; simp [snd_apply, prod_apply]

lemma comap_prod (κ : Kernel β γ) [IsSFiniteKernel κ] (η : Kernel β δ) [IsSFiniteKernel η]
    {f : α → β} (hf : Measurable f) :
    (κ ×ₖ η).comap f hf = (κ.comap f hf) ×ₖ (η.comap f hf) := by
  ext1 x
  rw [comap_apply, prod_apply, prod_apply, comap_apply, comap_apply]

lemma map_prod_map {ε} {mε : MeasurableSpace ε} (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel α δ) [IsSFiniteKernel η] {f : β → γ} (hf : Measurable f) {g : δ → ε}
    (hg : Measurable g) : (κ.map f) ×ₖ (η.map g) = (κ ×ₖ η).map (Prod.map f g) := by
  ext1 x
  rw [map_apply _ (hf.prodMap hg), prod_apply κ, ← Measure.map_prod_map _ _ hf hg, prod_apply,
    map_apply _ hf, map_apply _ hg]

lemma map_prod_eq (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η]
    {f : β → δ} (hf : Measurable f) : (κ.map f) ×ₖ η = (κ ×ₖ η).map (Prod.map f id) := by
  rw [← map_prod_map _ _ hf measurable_id, map_id]

lemma comap_prod_swap (κ : Kernel α β) (η : Kernel γ δ) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    comap (prodMkRight α η ×ₖ prodMkLeft γ κ) Prod.swap measurable_swap
      = map (prodMkRight γ κ ×ₖ prodMkLeft α η) Prod.swap := by
  rw [ext_fun_iff]
  intro x f hf
  rw [lintegral_comap, lintegral_map _ measurable_swap _ hf, lintegral_prod _ _ _ hf,
    lintegral_prod]
  swap; · fun_prop
  simp only [prodMkRight_apply, Prod.fst_swap, Prod.swap_prod_mk, lintegral_prodMkLeft,
    Prod.snd_swap]
  refine (lintegral_lintegral_swap ?_).symm
  fun_prop

lemma map_prod_swap (κ : Kernel α β) (η : Kernel α γ) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    map (κ ×ₖ η) Prod.swap = η ×ₖ κ := by
  rw [ext_fun_iff]
  intro x f hf
  rw [lintegral_map _ measurable_swap _ hf, lintegral_prod, lintegral_prod _ _ _ hf]
  swap; · fun_prop
  refine (lintegral_lintegral_swap ?_).symm
  fun_prop

@[simp]
lemma swap_prod {κ : Kernel α β} [IsSFiniteKernel κ] {η : Kernel α γ} [IsSFiniteKernel η] :
    (swap β γ) ∘ₖ (κ ×ₖ η) = (η ×ₖ κ) := by
  rw [swap_comp_eq_map, map_prod_swap]

lemma deterministic_prod_deterministic {f : α → β} {g : α → γ}
    (hf : Measurable f) (hg : Measurable g) :
    deterministic f hf ×ₖ deterministic g hg
      = deterministic (fun a ↦ (f a, g a)) (hf.prodMk hg) := by
  ext; simp_rw [prod_apply, deterministic_apply, Measure.dirac_prod_dirac]

lemma id_prod_eq : @Kernel.id (α × β) inferInstance =
    (deterministic Prod.fst measurable_fst) ×ₖ (deterministic Prod.snd measurable_snd) := by
  rw [deterministic_prod_deterministic]
  rfl

theorem comp_eq_snd_compProd (η : Kernel β γ) [IsSFiniteKernel η] (κ : Kernel α β)
    [IsSFiniteKernel κ] : η ∘ₖ κ = snd (κ ⊗ₖ prodMkLeft α η) := by
  ext a s hs
  rw [comp_apply' _ _ _ hs, snd_apply' _ _ hs, compProd_apply]
  swap
  · exact measurable_snd hs
  simp [← Set.preimage_comp]

@[simp] lemma snd_compProd_prodMkLeft
    (κ : Kernel α β) (η : Kernel β γ) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    snd (κ ⊗ₖ prodMkLeft α η) = η ∘ₖ κ := by
  ext a s hs
  rw [snd_apply' _ _ hs, compProd_apply, comp_apply' _ _ _ hs]
  · rfl
  · exact measurable_snd hs

lemma compProd_prodMkLeft_eq_comp
    (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel β γ) [IsSFiniteKernel η] :
    κ ⊗ₖ (prodMkLeft α η) = (Kernel.id ×ₖ η) ∘ₖ κ := by
  ext a s hs
  rw [comp_eq_snd_compProd, compProd_apply hs, snd_apply' _ _ hs, compProd_apply]
  swap; · exact measurable_snd hs
  simp only [prodMkLeft_apply, ← Set.preimage_comp, Prod.snd_comp_mk, Set.preimage_id_eq, id_eq,
    prod_apply' _ _ _ hs, id_apply]
  congr with b
  rw [lintegral_dirac']
  exact measurable_measure_prodMk_left hs

lemma prodAssoc_prod (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η]
    (ξ : Kernel α δ) [IsSFiniteKernel ξ] :
    ((κ ×ₖ ξ) ×ₖ η).map MeasurableEquiv.prodAssoc = κ ×ₖ (ξ ×ₖ η) := by
  ext1 a
  rw [map_apply _ (by fun_prop), prod_apply, prod_apply, Measure.prodAssoc_prod, prod_apply,
    prod_apply]

lemma prod_const_comp {δ} {mδ : MeasurableSpace δ} (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel β γ) [IsSFiniteKernel η] (μ : Measure δ) [SFinite μ] :
    (η ×ₖ (const β μ)) ∘ₖ κ = (η ∘ₖ κ) ×ₖ (const α μ) := by
  ext x s ms
  simp_rw [comp_apply' _ _ _ ms, prod_apply' _ _ _ ms, const_apply,
  lintegral_comp _ _ _ (measurable_measure_prodMk_left ms)]

lemma const_prod_comp {δ} {mδ : MeasurableSpace δ} (κ : Kernel α β) [IsSFiniteKernel κ]
    (μ : Measure γ) [SFinite μ] (η : Kernel β δ) [IsSFiniteKernel η] :
    ((const β μ) ×ₖ η) ∘ₖ κ = (const α μ) ×ₖ (η ∘ₖ κ) := by
  ext x s ms
  simp_rw [comp_apply' _ _ _ ms, prod_apply, Measure.prod_apply_symm ms, const_apply,
  lintegral_comp _ _ _ (measurable_measure_prodMk_right ms)]

end Kernel
end ProbabilityTheory
