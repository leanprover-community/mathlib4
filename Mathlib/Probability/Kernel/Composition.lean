/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.MeasurableIntegral

#align_import probability.kernel.composition from "leanprover-community/mathlib"@"3b92d54a05ee592aa2c6181a4e76b1bb7cc45d0b"

/-!
# Product and composition of kernels

We define
* the composition-product `κ ⊗ₖ η` of two s-finite kernels `κ : kernel α β` and
  `η : kernel (α × β) γ`, a kernel from `α` to `β × γ`.
* the map and comap of a kernel along a measurable function.
* the composition `η ∘ₖ κ` of kernels `κ : kernel α β` and `η : kernel β γ`, kernel from `α` to
  `γ`.
* the product `κ ×ₖ η` of s-finite kernels `κ : kernel α β` and `η : kernel α γ`,
  a kernel from `α` to `β × γ`.

A note on names:
The composition-product `kernel α β → kernel (α × β) γ → kernel α (β × γ)` is named composition in
[kallenberg2021] and product on the wikipedia article on transition kernels.
Most papers studying categories of kernels call composition the map we call composition. We adopt
that convention because it fits better with the use of the name `comp` elsewhere in mathlib.

## Main definitions

Kernels built from other kernels:
* `compProd (κ : kernel α β) (η : kernel (α × β) γ) : kernel α (β × γ)`: composition-product of 2
  s-finite kernels. We define a notation `κ ⊗ₖ η = compProd κ η`.
  `∫⁻ bc, f bc ∂((κ ⊗ₖ η) a) = ∫⁻ b, ∫⁻ c, f (b, c) ∂(η (a, b)) ∂(κ a)`
* `map (κ : kernel α β) (f : β → γ) (hf : Measurable f) : kernel α γ`
  `∫⁻ c, g c ∂(map κ f hf a) = ∫⁻ b, g (f b) ∂(κ a)`
* `comap (κ : kernel α β) (f : γ → α) (hf : Measurable f) : kernel γ β`
  `∫⁻ b, g b ∂(comap κ f hf c) = ∫⁻ b, g b ∂(κ (f c))`
* `comp (η : kernel β γ) (κ : kernel α β) : kernel α γ`: composition of 2 kernels.
  We define a notation `η ∘ₖ κ = comp η κ`.
  `∫⁻ c, g c ∂((η ∘ₖ κ) a) = ∫⁻ b, ∫⁻ c, g c ∂(η b) ∂(κ a)`
* `prod (κ : kernel α β) (η : kernel α γ) : kernel α (β × γ)`: product of 2 s-finite kernels.
  `∫⁻ bc, f bc ∂((κ ×ₖ η) a) = ∫⁻ b, ∫⁻ c, f (b, c) ∂(η a) ∂(κ a)`

## Main statements

* `lintegral_compProd`, `lintegral_map`, `lintegral_comap`, `lintegral_comp`, `lintegral_prod`:
  Lebesgue integral of a function against a composition-product/map/comap/composition/product of
  kernels.
* Instances of the form `<class>.<operation>` where class is one of `IsMarkovKernel`,
  `IsFiniteKernel`, `IsSFiniteKernel` and operation is one of `compProd`, `map`, `comap`,
  `comp`, `prod`. These instances state that the three classes are stable by the various operations.

## Notations

* `κ ⊗ₖ η = ProbabilityTheory.kernel.compProd κ η`
* `η ∘ₖ κ = ProbabilityTheory.kernel.comp η κ`
* `κ ×ₖ η = ProbabilityTheory.kernel.prod κ η`

-/


open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

namespace kernel

variable {α β ι : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

section CompositionProduct

/-!
### Composition-Product of kernels

We define a kernel composition-product
`compProd : kernel α β → kernel (α × β) γ → kernel α (β × γ)`.
-/


variable {γ : Type*} {mγ : MeasurableSpace γ} {s : Set (β × γ)}

/-- Auxiliary function for the definition of the composition-product of two kernels.
For all `a : α`, `compProdFun κ η a` is a countably additive function with value zero on the empty
set, and the composition-product of kernels is defined in `kernel.compProd` through
`Measure.ofMeasurable`. -/
noncomputable def compProdFun (κ : kernel α β) (η : kernel (α × β) γ) (a : α) (s : Set (β × γ)) :
    ℝ≥0∞ :=
  ∫⁻ b, η (a, b) {c | (b, c) ∈ s} ∂κ a
#align probability_theory.kernel.comp_prod_fun ProbabilityTheory.kernel.compProdFun

theorem compProdFun_empty (κ : kernel α β) (η : kernel (α × β) γ) (a : α) :
    compProdFun κ η a ∅ = 0 := by
  simp only [compProdFun, Set.mem_empty_iff_false, Set.setOf_false, measure_empty,
    MeasureTheory.lintegral_const, zero_mul]
#align probability_theory.kernel.comp_prod_fun_empty ProbabilityTheory.kernel.compProdFun_empty

theorem compProdFun_iUnion (κ : kernel α β) (η : kernel (α × β) γ) [IsSFiniteKernel η] (a : α)
    (f : ℕ → Set (β × γ)) (hf_meas : ∀ i, MeasurableSet (f i))
    (hf_disj : Pairwise (Disjoint on f)) :
    compProdFun κ η a (⋃ i, f i) = ∑' i, compProdFun κ η a (f i) := by
  have h_Union :
    (fun b => η (a, b) {c : γ | (b, c) ∈ ⋃ i, f i}) = fun b =>
      η (a, b) (⋃ i, {c : γ | (b, c) ∈ f i}) := by
    ext1 b
    congr with c
    simp only [Set.mem_iUnion, Set.iSup_eq_iUnion, Set.mem_setOf_eq]
  rw [compProdFun, h_Union]
  have h_tsum :
    (fun b => η (a, b) (⋃ i, {c : γ | (b, c) ∈ f i})) = fun b =>
      ∑' i, η (a, b) {c : γ | (b, c) ∈ f i} := by
    ext1 b
    rw [measure_iUnion]
    · intro i j hij s hsi hsj c hcs
      have hbci : {(b, c)} ⊆ f i := by rw [Set.singleton_subset_iff]; exact hsi hcs
      have hbcj : {(b, c)} ⊆ f j := by rw [Set.singleton_subset_iff]; exact hsj hcs
      simpa only [Set.bot_eq_empty, Set.le_eq_subset, Set.singleton_subset_iff,
        Set.mem_empty_iff_false] using hf_disj hij hbci hbcj
    · -- Porting note: behavior of `@` changed relative to lean 3, was
      -- exact fun i => (@measurable_prod_mk_left β γ _ _ b) _ (hf_meas i)
      exact fun i => (@measurable_prod_mk_left β γ _ _ b) (hf_meas i)
  rw [h_tsum, lintegral_tsum]
  · rfl
  · intro i
    have hm : MeasurableSet {p : (α × β) × γ | (p.1.2, p.2) ∈ f i} :=
      measurable_fst.snd.prod_mk measurable_snd (hf_meas i)
    exact ((measurable_kernel_prod_mk_left hm).comp measurable_prod_mk_left).aemeasurable
#align probability_theory.kernel.comp_prod_fun_Union ProbabilityTheory.kernel.compProdFun_iUnion

theorem compProdFun_tsum_right (κ : kernel α β) (η : kernel (α × β) γ) [IsSFiniteKernel η] (a : α)
    (hs : MeasurableSet s) : compProdFun κ η a s = ∑' n, compProdFun κ (seq η n) a s := by
  simp_rw [compProdFun, (measure_sum_seq η _).symm]
  have :
    ∫⁻ b, Measure.sum (fun n => seq η n (a, b)) {c : γ | (b, c) ∈ s} ∂κ a =
      ∫⁻ b, ∑' n, seq η n (a, b) {c : γ | (b, c) ∈ s} ∂κ a := by
    congr
    ext1 b
    rw [Measure.sum_apply]
    exact measurable_prod_mk_left hs
  rw [this, lintegral_tsum]
  exact fun n => ((measurable_kernel_prod_mk_left (κ := (seq η n))
    ((measurable_fst.snd.prod_mk measurable_snd) hs)).comp measurable_prod_mk_left).aemeasurable
#align probability_theory.kernel.comp_prod_fun_tsum_right ProbabilityTheory.kernel.compProdFun_tsum_right

theorem compProdFun_tsum_left (κ : kernel α β) (η : kernel (α × β) γ) [IsSFiniteKernel κ] (a : α)
    (s : Set (β × γ)) : compProdFun κ η a s = ∑' n, compProdFun (seq κ n) η a s := by
  simp_rw [compProdFun, (measure_sum_seq κ _).symm, lintegral_sum_measure]
#align probability_theory.kernel.comp_prod_fun_tsum_left ProbabilityTheory.kernel.compProdFun_tsum_left

theorem compProdFun_eq_tsum (κ : kernel α β) [IsSFiniteKernel κ] (η : kernel (α × β) γ)
    [IsSFiniteKernel η] (a : α) (hs : MeasurableSet s) :
    compProdFun κ η a s = ∑' (n) (m), compProdFun (seq κ n) (seq η m) a s := by
  simp_rw [compProdFun_tsum_left κ η a s, compProdFun_tsum_right _ η a hs]
#align probability_theory.kernel.comp_prod_fun_eq_tsum ProbabilityTheory.kernel.compProdFun_eq_tsum

/-- Auxiliary lemma for `measurable_compProdFun`. -/
theorem measurable_compProdFun_of_finite (κ : kernel α β) [IsFiniteKernel κ] (η : kernel (α × β) γ)
    [IsFiniteKernel η] (hs : MeasurableSet s) : Measurable fun a => compProdFun κ η a s := by
  simp only [compProdFun]
  have h_meas : Measurable (Function.uncurry fun a b => η (a, b) {c : γ | (b, c) ∈ s}) := by
    have :
      (Function.uncurry fun a b => η (a, b) {c : γ | (b, c) ∈ s}) = fun p =>
        η p {c : γ | (p.2, c) ∈ s} := by
      ext1 p
      rw [Function.uncurry_apply_pair]
    rw [this]
    exact measurable_kernel_prod_mk_left (measurable_fst.snd.prod_mk measurable_snd hs)
  exact h_meas.lintegral_kernel_prod_right
#align probability_theory.kernel.measurable_comp_prod_fun_of_finite ProbabilityTheory.kernel.measurable_compProdFun_of_finite

theorem measurable_compProdFun (κ : kernel α β) [IsSFiniteKernel κ] (η : kernel (α × β) γ)
    [IsSFiniteKernel η] (hs : MeasurableSet s) : Measurable fun a => compProdFun κ η a s := by
  simp_rw [compProdFun_tsum_right κ η _ hs]
  refine Measurable.ennreal_tsum fun n => ?_
  simp only [compProdFun]
  have h_meas : Measurable (Function.uncurry fun a b => seq η n (a, b) {c : γ | (b, c) ∈ s}) := by
    have :
      (Function.uncurry fun a b => seq η n (a, b) {c : γ | (b, c) ∈ s}) = fun p =>
        seq η n p {c : γ | (p.2, c) ∈ s} := by
      ext1 p
      rw [Function.uncurry_apply_pair]
    rw [this]
    exact measurable_kernel_prod_mk_left (measurable_fst.snd.prod_mk measurable_snd hs)
  exact h_meas.lintegral_kernel_prod_right
#align probability_theory.kernel.measurable_comp_prod_fun ProbabilityTheory.kernel.measurable_compProdFun

open scoped Classical

/-- Composition-Product of kernels. For s-finite kernels, it satisfies
`∫⁻ bc, f bc ∂(compProd κ η a) = ∫⁻ b, ∫⁻ c, f (b, c) ∂(η (a, b)) ∂(κ a)`
(see `ProbabilityTheory.kernel.lintegral_compProd`).
If either of the kernels is not s-finite, `compProd` is given the junk value 0. -/
noncomputable def compProd (κ : kernel α β) (η : kernel (α × β) γ) : kernel α (β × γ) :=
if h : IsSFiniteKernel κ ∧ IsSFiniteKernel η then
{ val := fun a ↦
    Measure.ofMeasurable (fun s _ => compProdFun κ η a s) (compProdFun_empty κ η a)
      (@compProdFun_iUnion _ _ _ _ _ _ κ η h.2 a)
  property := by
    have : IsSFiniteKernel κ := h.1
    have : IsSFiniteKernel η := h.2
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    have :
      (fun a =>
          Measure.ofMeasurable (fun s _ => compProdFun κ η a s) (compProdFun_empty κ η a)
            (compProdFun_iUnion κ η a) s) =
        fun a => compProdFun κ η a s := by
      ext1 a; rwa [Measure.ofMeasurable_apply]
    rw [this]
    exact measurable_compProdFun κ η hs }
else 0
#align probability_theory.kernel.comp_prod ProbabilityTheory.kernel.compProd

scoped[ProbabilityTheory] infixl:100 " ⊗ₖ " => ProbabilityTheory.kernel.compProd

theorem compProd_apply_eq_compProdFun (κ : kernel α β) [IsSFiniteKernel κ] (η : kernel (α × β) γ)
    [IsSFiniteKernel η] (a : α) (hs : MeasurableSet s) :
    (κ ⊗ₖ η) a s = compProdFun κ η a s := by
  rw [compProd, dif_pos]
  swap
  · constructor <;> infer_instance
  change
    Measure.ofMeasurable (fun s _ => compProdFun κ η a s) (compProdFun_empty κ η a)
        (compProdFun_iUnion κ η a) s =
      ∫⁻ b, η (a, b) {c | (b, c) ∈ s} ∂κ a
  rw [Measure.ofMeasurable_apply _ hs]
  rfl
#align probability_theory.kernel.comp_prod_apply_eq_comp_prod_fun ProbabilityTheory.kernel.compProd_apply_eq_compProdFun

theorem compProd_of_not_isSFiniteKernel_left (κ : kernel α β) (η : kernel (α × β) γ)
    (h : ¬ IsSFiniteKernel κ) :
    κ ⊗ₖ η = 0 := by
  rw [compProd, dif_neg]
  simp [h]

theorem compProd_of_not_isSFiniteKernel_right (κ : kernel α β) (η : kernel (α × β) γ)
    (h : ¬ IsSFiniteKernel η) :
    κ ⊗ₖ η = 0 := by
  rw [compProd, dif_neg]
  simp [h]

theorem compProd_apply (κ : kernel α β) [IsSFiniteKernel κ] (η : kernel (α × β) γ)
    [IsSFiniteKernel η] (a : α) (hs : MeasurableSet s) :
    (κ ⊗ₖ η) a s = ∫⁻ b, η (a, b) {c | (b, c) ∈ s} ∂κ a :=
  compProd_apply_eq_compProdFun κ η a hs
#align probability_theory.kernel.comp_prod_apply ProbabilityTheory.kernel.compProd_apply

theorem le_compProd_apply (κ : kernel α β) [IsSFiniteKernel κ] (η : kernel (α × β) γ)
    [IsSFiniteKernel η] (a : α) (s : Set (β × γ)) :
    ∫⁻ b, η (a, b) {c | (b, c) ∈ s} ∂κ a ≤ (κ ⊗ₖ η) a s :=
  calc
    ∫⁻ b, η (a, b) {c | (b, c) ∈ s} ∂κ a ≤
        ∫⁻ b, η (a, b) {c | (b, c) ∈ toMeasurable ((κ ⊗ₖ η) a) s} ∂κ a :=
      lintegral_mono fun _ => measure_mono fun _ h_mem => subset_toMeasurable _ _ h_mem
    _ = (κ ⊗ₖ η) a (toMeasurable ((κ ⊗ₖ η) a) s) :=
      (kernel.compProd_apply_eq_compProdFun κ η a (measurableSet_toMeasurable _ _)).symm
    _ = (κ ⊗ₖ η) a s := measure_toMeasurable s
#align probability_theory.kernel.le_comp_prod_apply ProbabilityTheory.kernel.le_compProd_apply

@[simp]
lemma compProd_zero_left (κ : kernel (α × β) γ) :
    (0 : kernel α β) ⊗ₖ κ = 0 := by
  by_cases h : IsSFiniteKernel κ
  · ext a s hs
    rw [kernel.compProd_apply _ _ _ hs]
    simp
  · rw [kernel.compProd_of_not_isSFiniteKernel_right _ _ h]

@[simp]
lemma compProd_zero_right (κ : kernel α β) (γ : Type*) [MeasurableSpace γ] :
    κ ⊗ₖ (0 : kernel (α × β) γ) = 0 := by
  by_cases h : IsSFiniteKernel κ
  · ext a s hs
    rw [kernel.compProd_apply _ _ _ hs]
    simp
  · rw [kernel.compProd_of_not_isSFiniteKernel_left _ _ h]

section Ae

/-! ### `ae` filter of the composition-product -/


variable {κ : kernel α β} [IsSFiniteKernel κ] {η : kernel (α × β) γ} [IsSFiniteKernel η] {a : α}

theorem ae_kernel_lt_top (a : α) (h2s : (κ ⊗ₖ η) a s ≠ ∞) :
    ∀ᵐ b ∂κ a, η (a, b) (Prod.mk b ⁻¹' s) < ∞ := by
  let t := toMeasurable ((κ ⊗ₖ η) a) s
  have : ∀ b : β, η (a, b) (Prod.mk b ⁻¹' s) ≤ η (a, b) (Prod.mk b ⁻¹' t) := fun b =>
    measure_mono (Set.preimage_mono (subset_toMeasurable _ _))
  have ht : MeasurableSet t := measurableSet_toMeasurable _ _
  have h2t : (κ ⊗ₖ η) a t ≠ ∞ := by rwa [measure_toMeasurable]
  have ht_lt_top : ∀ᵐ b ∂κ a, η (a, b) (Prod.mk b ⁻¹' t) < ∞ := by
    rw [kernel.compProd_apply _ _ _ ht] at h2t
    exact ae_lt_top (kernel.measurable_kernel_prod_mk_left' ht a) h2t
  filter_upwards [ht_lt_top] with b hb
  exact (this b).trans_lt hb
#align probability_theory.kernel.ae_kernel_lt_top ProbabilityTheory.kernel.ae_kernel_lt_top

theorem compProd_null (a : α) (hs : MeasurableSet s) :
    (κ ⊗ₖ η) a s = 0 ↔ (fun b => η (a, b) (Prod.mk b ⁻¹' s)) =ᵐ[κ a] 0 := by
  rw [kernel.compProd_apply _ _ _ hs, lintegral_eq_zero_iff]
  · rfl
  · exact kernel.measurable_kernel_prod_mk_left' hs a
#align probability_theory.kernel.comp_prod_null ProbabilityTheory.kernel.compProd_null

theorem ae_null_of_compProd_null (h : (κ ⊗ₖ η) a s = 0) :
    (fun b => η (a, b) (Prod.mk b ⁻¹' s)) =ᵐ[κ a] 0 := by
  obtain ⟨t, hst, mt, ht⟩ := exists_measurable_superset_of_null h
  simp_rw [compProd_null a mt] at ht
  rw [Filter.eventuallyLE_antisymm_iff]
  exact
    ⟨Filter.EventuallyLE.trans_eq
        (Filter.eventually_of_forall fun x => (measure_mono (Set.preimage_mono hst) : _)) ht,
      Filter.eventually_of_forall fun x => zero_le _⟩
#align probability_theory.kernel.ae_null_of_comp_prod_null ProbabilityTheory.kernel.ae_null_of_compProd_null

theorem ae_ae_of_ae_compProd {p : β × γ → Prop} (h : ∀ᵐ bc ∂(κ ⊗ₖ η) a, p bc) :
    ∀ᵐ b ∂κ a, ∀ᵐ c ∂η (a, b), p (b, c) :=
  ae_null_of_compProd_null h
#align probability_theory.kernel.ae_ae_of_ae_comp_prod ProbabilityTheory.kernel.ae_ae_of_ae_compProd

lemma ae_compProd_of_ae_ae {p : β × γ → Prop} (hp : MeasurableSet {x | p x})
    (h : ∀ᵐ b ∂κ a, ∀ᵐ c ∂η (a, b), p (b, c)) :
    ∀ᵐ bc ∂(κ ⊗ₖ η) a, p bc := by
  simp_rw [ae_iff] at h ⊢
  rw [compProd_null]
  · exact h
  · exact hp.compl

lemma ae_compProd_iff {p : β × γ → Prop} (hp : MeasurableSet {x | p x}) :
    (∀ᵐ bc ∂(κ ⊗ₖ η) a, p bc) ↔ ∀ᵐ b ∂κ a, ∀ᵐ c ∂η (a, b), p (b, c) :=
  ⟨fun h ↦ ae_ae_of_ae_compProd h, fun h ↦ ae_compProd_of_ae_ae hp h⟩

end Ae

section Restrict

variable {κ : kernel α β} [IsSFiniteKernel κ] {η : kernel (α × β) γ} [IsSFiniteKernel η] {a : α}

theorem compProd_restrict {s : Set β} {t : Set γ} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    kernel.restrict κ hs ⊗ₖ kernel.restrict η ht = kernel.restrict (κ ⊗ₖ η) (hs.prod ht) := by
  ext a u hu
  rw [compProd_apply _ _ _ hu, restrict_apply' _ _ _ hu,
    compProd_apply _ _ _ (hu.inter (hs.prod ht))]
  simp only [kernel.restrict_apply, Measure.restrict_apply' ht, Set.mem_inter_iff,
    Set.prod_mk_mem_set_prod_eq]
  have :
    ∀ b,
      η (a, b) {c : γ | (b, c) ∈ u ∧ b ∈ s ∧ c ∈ t} =
        s.indicator (fun b => η (a, b) ({c : γ | (b, c) ∈ u} ∩ t)) b := by
    intro b
    classical
    rw [Set.indicator_apply]
    split_ifs with h
    · simp only [h, true_and_iff]
      rfl
    · simp only [h, false_and_iff, and_false_iff, Set.setOf_false, measure_empty]
  simp_rw [this]
  rw [lintegral_indicator _ hs]
#align probability_theory.kernel.comp_prod_restrict ProbabilityTheory.kernel.compProd_restrict

theorem compProd_restrict_left {s : Set β} (hs : MeasurableSet s) :
    kernel.restrict κ hs ⊗ₖ η = kernel.restrict (κ ⊗ₖ η) (hs.prod MeasurableSet.univ) := by
  rw [← compProd_restrict]
  · congr; exact kernel.restrict_univ.symm
#align probability_theory.kernel.comp_prod_restrict_left ProbabilityTheory.kernel.compProd_restrict_left

theorem compProd_restrict_right {t : Set γ} (ht : MeasurableSet t) :
    κ ⊗ₖ kernel.restrict η ht = kernel.restrict (κ ⊗ₖ η) (MeasurableSet.univ.prod ht) := by
  rw [← compProd_restrict]
  · congr; exact kernel.restrict_univ.symm
#align probability_theory.kernel.comp_prod_restrict_right ProbabilityTheory.kernel.compProd_restrict_right

end Restrict

section Lintegral

/-! ### Lebesgue integral -/


/-- Lebesgue integral against the composition-product of two kernels. -/
theorem lintegral_compProd' (κ : kernel α β) [IsSFiniteKernel κ] (η : kernel (α × β) γ)
    [IsSFiniteKernel η] (a : α) {f : β → γ → ℝ≥0∞} (hf : Measurable (Function.uncurry f)) :
    ∫⁻ bc, f bc.1 bc.2 ∂(κ ⊗ₖ η) a = ∫⁻ b, ∫⁻ c, f b c ∂η (a, b) ∂κ a := by
  let F : ℕ → SimpleFunc (β × γ) ℝ≥0∞ := SimpleFunc.eapprox (Function.uncurry f)
  have h : ∀ a, ⨆ n, F n a = Function.uncurry f a :=
    SimpleFunc.iSup_eapprox_apply (Function.uncurry f) hf
  simp only [Prod.forall, Function.uncurry_apply_pair] at h
  simp_rw [← h]
  have h_mono : Monotone F := fun i j hij b =>
    SimpleFunc.monotone_eapprox (Function.uncurry f) hij _
  rw [lintegral_iSup (fun n => (F n).measurable) h_mono]
  have : ∀ b, ∫⁻ c, ⨆ n, F n (b, c) ∂η (a, b) = ⨆ n, ∫⁻ c, F n (b, c) ∂η (a, b) := by
    intro a
    rw [lintegral_iSup]
    · exact fun n => (F n).measurable.comp measurable_prod_mk_left
    · exact fun i j hij b => h_mono hij _
  simp_rw [this]
  have h_some_meas_integral :
    ∀ f' : SimpleFunc (β × γ) ℝ≥0∞, Measurable fun b => ∫⁻ c, f' (b, c) ∂η (a, b) := by
    intro f'
    have :
      (fun b => ∫⁻ c, f' (b, c) ∂η (a, b)) =
        (fun ab => ∫⁻ c, f' (ab.2, c) ∂η ab) ∘ fun b => (a, b) := by
      ext1 ab; rfl
    rw [this]
    apply Measurable.comp _ (measurable_prod_mk_left (m := mα))
    exact Measurable.lintegral_kernel_prod_right
      ((SimpleFunc.measurable _).comp (measurable_fst.snd.prod_mk measurable_snd))
  rw [lintegral_iSup]
  rotate_left
  · exact fun n => h_some_meas_integral (F n)
  · exact fun i j hij b => lintegral_mono fun c => h_mono hij _
  congr
  ext1 n
  -- Porting note: Added `(P := _)`
  refine SimpleFunc.induction (P := fun f => (∫⁻ (a : β × γ), f a ∂(κ ⊗ₖ η) a =
      ∫⁻ (a_1 : β), ∫⁻ (c : γ), f (a_1, c) ∂η (a, a_1) ∂κ a)) ?_ ?_ (F n)
  · intro c s hs
    classical -- Porting note: Added `classical` for `Set.piecewise_eq_indicator`
    simp (config := { unfoldPartialApp := true }) only [SimpleFunc.const_zero,
      SimpleFunc.coe_piecewise, SimpleFunc.coe_const, SimpleFunc.coe_zero,
      Set.piecewise_eq_indicator, Function.const, lintegral_indicator_const hs]
    rw [compProd_apply κ η _ hs, ← lintegral_const_mul c _]
    swap
    · exact (measurable_kernel_prod_mk_left ((measurable_fst.snd.prod_mk measurable_snd) hs)).comp
        measurable_prod_mk_left
    congr
    ext1 b
    rw [lintegral_indicator_const_comp measurable_prod_mk_left hs]
    rfl
  · intro f f' _ hf_eq hf'_eq
    simp_rw [SimpleFunc.coe_add, Pi.add_apply]
    change
      ∫⁻ x, (f : β × γ → ℝ≥0∞) x + f' x ∂(κ ⊗ₖ η) a =
        ∫⁻ b, ∫⁻ c : γ, f (b, c) + f' (b, c) ∂η (a, b) ∂κ a
    rw [lintegral_add_left (SimpleFunc.measurable _), hf_eq, hf'_eq, ← lintegral_add_left]
    swap
    · exact h_some_meas_integral f
    congr with b
    rw [lintegral_add_left]
    exact (SimpleFunc.measurable _).comp measurable_prod_mk_left
#align probability_theory.kernel.lintegral_comp_prod' ProbabilityTheory.kernel.lintegral_compProd'

/-- Lebesgue integral against the composition-product of two kernels. -/
theorem lintegral_compProd (κ : kernel α β) [IsSFiniteKernel κ] (η : kernel (α × β) γ)
    [IsSFiniteKernel η] (a : α) {f : β × γ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ bc, f bc ∂(κ ⊗ₖ η) a = ∫⁻ b, ∫⁻ c, f (b, c) ∂η (a, b) ∂κ a := by
  let g := Function.curry f
  change ∫⁻ bc, f bc ∂(κ ⊗ₖ η) a = ∫⁻ b, ∫⁻ c, g b c ∂η (a, b) ∂κ a
  rw [← lintegral_compProd']
  · simp_rw [g, Function.curry_apply]
  · simp_rw [g, Function.uncurry_curry]; exact hf
#align probability_theory.kernel.lintegral_comp_prod ProbabilityTheory.kernel.lintegral_compProd

/-- Lebesgue integral against the composition-product of two kernels. -/
theorem lintegral_compProd₀ (κ : kernel α β) [IsSFiniteKernel κ] (η : kernel (α × β) γ)
    [IsSFiniteKernel η] (a : α) {f : β × γ → ℝ≥0∞} (hf : AEMeasurable f ((κ ⊗ₖ η) a)) :
    ∫⁻ z, f z ∂(κ ⊗ₖ η) a = ∫⁻ x, ∫⁻ y, f (x, y) ∂η (a, x) ∂κ a := by
  have A : ∫⁻ z, f z ∂(κ ⊗ₖ η) a = ∫⁻ z, hf.mk f z ∂(κ ⊗ₖ η) a := lintegral_congr_ae hf.ae_eq_mk
  have B : ∫⁻ x, ∫⁻ y, f (x, y) ∂η (a, x) ∂κ a = ∫⁻ x, ∫⁻ y, hf.mk f (x, y) ∂η (a, x) ∂κ a := by
    apply lintegral_congr_ae
    filter_upwards [ae_ae_of_ae_compProd hf.ae_eq_mk] with _ ha using lintegral_congr_ae ha
  rw [A, B, lintegral_compProd]
  exact hf.measurable_mk
#align probability_theory.kernel.lintegral_comp_prod₀ ProbabilityTheory.kernel.lintegral_compProd₀

theorem set_lintegral_compProd (κ : kernel α β) [IsSFiniteKernel κ] (η : kernel (α × β) γ)
    [IsSFiniteKernel η] (a : α) {f : β × γ → ℝ≥0∞} (hf : Measurable f) {s : Set β} {t : Set γ}
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    ∫⁻ z in s ×ˢ t, f z ∂(κ ⊗ₖ η) a = ∫⁻ x in s, ∫⁻ y in t, f (x, y) ∂η (a, x) ∂κ a := by
  simp_rw [← kernel.restrict_apply (κ ⊗ₖ η) (hs.prod ht), ← compProd_restrict hs ht,
    lintegral_compProd _ _ _ hf, kernel.restrict_apply]
#align probability_theory.kernel.set_lintegral_comp_prod ProbabilityTheory.kernel.set_lintegral_compProd

theorem set_lintegral_compProd_univ_right (κ : kernel α β) [IsSFiniteKernel κ]
    (η : kernel (α × β) γ) [IsSFiniteKernel η] (a : α) {f : β × γ → ℝ≥0∞} (hf : Measurable f)
    {s : Set β} (hs : MeasurableSet s) :
    ∫⁻ z in s ×ˢ Set.univ, f z ∂(κ ⊗ₖ η) a = ∫⁻ x in s, ∫⁻ y, f (x, y) ∂η (a, x) ∂κ a := by
  simp_rw [set_lintegral_compProd κ η a hf hs MeasurableSet.univ, Measure.restrict_univ]
#align probability_theory.kernel.set_lintegral_comp_prod_univ_right ProbabilityTheory.kernel.set_lintegral_compProd_univ_right

theorem set_lintegral_compProd_univ_left (κ : kernel α β) [IsSFiniteKernel κ] (η : kernel (α × β) γ)
    [IsSFiniteKernel η] (a : α) {f : β × γ → ℝ≥0∞} (hf : Measurable f) {t : Set γ}
    (ht : MeasurableSet t) :
    ∫⁻ z in Set.univ ×ˢ t, f z ∂(κ ⊗ₖ η) a = ∫⁻ x, ∫⁻ y in t, f (x, y) ∂η (a, x) ∂κ a := by
  simp_rw [set_lintegral_compProd κ η a hf MeasurableSet.univ ht, Measure.restrict_univ]
#align probability_theory.kernel.set_lintegral_comp_prod_univ_left ProbabilityTheory.kernel.set_lintegral_compProd_univ_left

end Lintegral

theorem compProd_eq_tsum_compProd (κ : kernel α β) [IsSFiniteKernel κ] (η : kernel (α × β) γ)
    [IsSFiniteKernel η] (a : α) (hs : MeasurableSet s) :
    (κ ⊗ₖ η) a s = ∑' (n : ℕ) (m : ℕ), (seq κ n ⊗ₖ seq η m) a s := by
  simp_rw [compProd_apply_eq_compProdFun _ _ _ hs]; exact compProdFun_eq_tsum κ η a hs
#align probability_theory.kernel.comp_prod_eq_tsum_comp_prod ProbabilityTheory.kernel.compProd_eq_tsum_compProd

theorem compProd_eq_sum_compProd (κ : kernel α β) [IsSFiniteKernel κ] (η : kernel (α × β) γ)
    [IsSFiniteKernel η] : κ ⊗ₖ η = kernel.sum fun n => kernel.sum fun m => seq κ n ⊗ₖ seq η m := by
  ext a s hs; simp_rw [kernel.sum_apply' _ a hs]; rw [compProd_eq_tsum_compProd κ η a hs]
#align probability_theory.kernel.comp_prod_eq_sum_comp_prod ProbabilityTheory.kernel.compProd_eq_sum_compProd

theorem compProd_eq_sum_compProd_left (κ : kernel α β) [IsSFiniteKernel κ] (η : kernel (α × β) γ) :
    κ ⊗ₖ η = kernel.sum fun n => seq κ n ⊗ₖ η := by
  by_cases h : IsSFiniteKernel η
  swap
  · simp_rw [compProd_of_not_isSFiniteKernel_right _ _ h]
    simp
  rw [compProd_eq_sum_compProd]
  congr with n a s hs
  simp_rw [kernel.sum_apply' _ _ hs, compProd_apply_eq_compProdFun _ _ _ hs,
    compProdFun_tsum_right _ η a hs]
#align probability_theory.kernel.comp_prod_eq_sum_comp_prod_left ProbabilityTheory.kernel.compProd_eq_sum_compProd_left

theorem compProd_eq_sum_compProd_right (κ : kernel α β) (η : kernel (α × β) γ)
    [IsSFiniteKernel η] : κ ⊗ₖ η = kernel.sum fun n => κ ⊗ₖ seq η n := by
  by_cases hκ : IsSFiniteKernel κ
  swap
  · simp_rw [compProd_of_not_isSFiniteKernel_left _ _ hκ]
    simp
  rw [compProd_eq_sum_compProd]
  simp_rw [compProd_eq_sum_compProd_left κ _]
  rw [kernel.sum_comm]
#align probability_theory.kernel.comp_prod_eq_sum_comp_prod_right ProbabilityTheory.kernel.compProd_eq_sum_compProd_right

instance IsMarkovKernel.compProd (κ : kernel α β) [IsMarkovKernel κ] (η : kernel (α × β) γ)
    [IsMarkovKernel η] : IsMarkovKernel (κ ⊗ₖ η) :=
  ⟨fun a =>
    ⟨by
      rw [compProd_apply κ η a MeasurableSet.univ]
      simp only [Set.mem_univ, Set.setOf_true, measure_univ, lintegral_one]⟩⟩
#align probability_theory.kernel.is_markov_kernel.comp_prod ProbabilityTheory.kernel.IsMarkovKernel.compProd

theorem compProd_apply_univ_le (κ : kernel α β) (η : kernel (α × β) γ) [IsFiniteKernel η] (a : α) :
    (κ ⊗ₖ η) a Set.univ ≤ κ a Set.univ * IsFiniteKernel.bound η := by
  by_cases hκ : IsSFiniteKernel κ
  swap
  · rw [compProd_of_not_isSFiniteKernel_left _ _ hκ]
    simp
  rw [compProd_apply κ η a MeasurableSet.univ]
  simp only [Set.mem_univ, Set.setOf_true]
  let Cη := IsFiniteKernel.bound η
  calc
    ∫⁻ b, η (a, b) Set.univ ∂κ a ≤ ∫⁻ _, Cη ∂κ a :=
      lintegral_mono fun b => measure_le_bound η (a, b) Set.univ
    _ = Cη * κ a Set.univ := MeasureTheory.lintegral_const Cη
    _ = κ a Set.univ * Cη := mul_comm _ _
#align probability_theory.kernel.comp_prod_apply_univ_le ProbabilityTheory.kernel.compProd_apply_univ_le

instance IsFiniteKernel.compProd (κ : kernel α β) [IsFiniteKernel κ] (η : kernel (α × β) γ)
    [IsFiniteKernel η] : IsFiniteKernel (κ ⊗ₖ η) :=
  ⟨⟨IsFiniteKernel.bound κ * IsFiniteKernel.bound η,
      ENNReal.mul_lt_top (IsFiniteKernel.bound_ne_top κ) (IsFiniteKernel.bound_ne_top η), fun a =>
      calc
        (κ ⊗ₖ η) a Set.univ ≤ κ a Set.univ * IsFiniteKernel.bound η := compProd_apply_univ_le κ η a
        _ ≤ IsFiniteKernel.bound κ * IsFiniteKernel.bound η :=
          mul_le_mul (measure_le_bound κ a Set.univ) le_rfl (zero_le _) (zero_le _)⟩⟩
#align probability_theory.kernel.is_finite_kernel.comp_prod ProbabilityTheory.kernel.IsFiniteKernel.compProd

instance IsSFiniteKernel.compProd (κ : kernel α β) (η : kernel (α × β) γ) :
    IsSFiniteKernel (κ ⊗ₖ η) := by
  by_cases h : IsSFiniteKernel κ
  swap
  · rw [compProd_of_not_isSFiniteKernel_left _ _ h]
    infer_instance
  by_cases h : IsSFiniteKernel η
  swap
  · rw [compProd_of_not_isSFiniteKernel_right _ _ h]
    infer_instance
  rw [compProd_eq_sum_compProd]
  exact kernel.isSFiniteKernel_sum fun n => kernel.isSFiniteKernel_sum inferInstance
#align probability_theory.kernel.is_s_finite_kernel.comp_prod ProbabilityTheory.kernel.IsSFiniteKernel.compProd

lemma compProd_add_left (μ κ : kernel α β) (η : kernel (α × β) γ)
    [IsSFiniteKernel μ] [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    (μ + κ) ⊗ₖ η = μ ⊗ₖ η + κ ⊗ₖ η := by ext _ _ hs; simp [compProd_apply _ _ _ hs]

lemma compProd_add_right (μ : kernel α β) (κ η : kernel (α × β) γ)
    [IsSFiniteKernel μ] [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    μ ⊗ₖ (κ + η) = μ ⊗ₖ κ + μ ⊗ₖ η := by
  ext a s hs
  simp only [compProd_apply _ _ _ hs, coeFn_add, Pi.add_apply, Measure.coe_add]
  rw [lintegral_add_left]
  exact measurable_kernel_prod_mk_left' hs a

lemma comapRight_compProd_id_prod {δ : Type*} {mδ : MeasurableSpace δ}
    (κ : kernel α β) [IsSFiniteKernel κ] (η : kernel (α × β) γ) [IsSFiniteKernel η]
    {f : δ → γ} (hf : MeasurableEmbedding f) :
    comapRight (κ ⊗ₖ η) (MeasurableEmbedding.id.prod_mk hf) = κ ⊗ₖ (comapRight η hf) := by
  ext a t ht
  rw [comapRight_apply' _ _ _ ht, compProd_apply, compProd_apply _ _ _ ht]
  swap; · exact (MeasurableEmbedding.id.prod_mk hf).measurableSet_image.mpr ht
  refine lintegral_congr (fun b ↦ ?_)
  simp only [id_eq, Set.mem_image, Prod.mk.injEq, Prod.exists]
  rw [comapRight_apply']
  swap; · exact measurable_prod_mk_left ht
  congr with x
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨b', c, h, rfl, rfl⟩
    exact ⟨c, h, rfl⟩
  · rintro ⟨c, h, rfl⟩
    exact ⟨b, c, h, rfl, rfl⟩

end CompositionProduct

section MapComap

/-! ### map, comap -/


variable {γ δ : Type*} {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ} {f : β → γ} {g : γ → α}

/-- The pushforward of a kernel along a measurable function.
We include measurability in the assumptions instead of using junk values
to make sure that typeclass inference can infer that the `map` of a Markov kernel
is again a Markov kernel. -/
noncomputable def map (κ : kernel α β) (f : β → γ) (hf : Measurable f) : kernel α γ where
  val a := (κ a).map f
  property := (Measure.measurable_map _ hf).comp (kernel.measurable κ)
#align probability_theory.kernel.map ProbabilityTheory.kernel.map

theorem map_apply (κ : kernel α β) (hf : Measurable f) (a : α) : map κ f hf a = (κ a).map f :=
  rfl
#align probability_theory.kernel.map_apply ProbabilityTheory.kernel.map_apply

theorem map_apply' (κ : kernel α β) (hf : Measurable f) (a : α) {s : Set γ} (hs : MeasurableSet s) :
    map κ f hf a s = κ a (f ⁻¹' s) := by rw [map_apply, Measure.map_apply hf hs]
#align probability_theory.kernel.map_apply' ProbabilityTheory.kernel.map_apply'

@[simp]
lemma map_zero (hf : Measurable f) : kernel.map (0 : kernel α β) f hf = 0 := by
  ext; rw [kernel.map_apply]; simp

@[simp]
lemma map_id (κ : kernel α β) : map κ id measurable_id = κ := by ext a; rw [map_apply]; simp

@[simp]
lemma map_id' (κ : kernel α β) : map κ (fun a ↦ a) measurable_id = κ := map_id κ

nonrec theorem lintegral_map (κ : kernel α β) (hf : Measurable f) (a : α) {g' : γ → ℝ≥0∞}
    (hg : Measurable g') : ∫⁻ b, g' b ∂map κ f hf a = ∫⁻ a, g' (f a) ∂κ a := by
  rw [map_apply _ hf, lintegral_map hg hf]
#align probability_theory.kernel.lintegral_map ProbabilityTheory.kernel.lintegral_map

theorem sum_map_seq (κ : kernel α β) [IsSFiniteKernel κ] (hf : Measurable f) :
    (kernel.sum fun n => map (seq κ n) f hf) = map κ f hf := by
  ext a s hs
  rw [kernel.sum_apply, map_apply' κ hf a hs, Measure.sum_apply _ hs, ← measure_sum_seq κ,
    Measure.sum_apply _ (hf hs)]
  simp_rw [map_apply' _ hf _ hs]
#align probability_theory.kernel.sum_map_seq ProbabilityTheory.kernel.sum_map_seq

instance IsMarkovKernel.map (κ : kernel α β) [IsMarkovKernel κ] (hf : Measurable f) :
    IsMarkovKernel (map κ f hf) :=
  ⟨fun a => ⟨by rw [map_apply' κ hf a MeasurableSet.univ, Set.preimage_univ, measure_univ]⟩⟩
#align probability_theory.kernel.is_markov_kernel.map ProbabilityTheory.kernel.IsMarkovKernel.map

instance IsFiniteKernel.map (κ : kernel α β) [IsFiniteKernel κ] (hf : Measurable f) :
    IsFiniteKernel (map κ f hf) := by
  refine ⟨⟨IsFiniteKernel.bound κ, IsFiniteKernel.bound_lt_top κ, fun a => ?_⟩⟩
  rw [map_apply' κ hf a MeasurableSet.univ]
  exact measure_le_bound κ a _
#align probability_theory.kernel.is_finite_kernel.map ProbabilityTheory.kernel.IsFiniteKernel.map

instance IsSFiniteKernel.map (κ : kernel α β) [IsSFiniteKernel κ] (hf : Measurable f) :
    IsSFiniteKernel (map κ f hf) :=
  ⟨⟨fun n => kernel.map (seq κ n) f hf, inferInstance, (sum_map_seq κ hf).symm⟩⟩
#align probability_theory.kernel.is_s_finite_kernel.map ProbabilityTheory.kernel.IsSFiniteKernel.map

@[simp]
lemma map_const (μ : Measure α) {f : α → β} (hf : Measurable f) :
    map (const γ μ) f hf = const γ (μ.map f) := by
  ext x s hs
  rw [map_apply' _ _ _ hs, const_apply, const_apply, Measure.map_apply hf hs]

/-- Pullback of a kernel, such that for each set s `comap κ g hg c s = κ (g c) s`.
We include measurability in the assumptions instead of using junk values
to make sure that typeclass inference can infer that the `comap` of a Markov kernel
is again a Markov kernel. -/
def comap (κ : kernel α β) (g : γ → α) (hg : Measurable g) : kernel γ β where
  val a := κ (g a)
  property := (kernel.measurable κ).comp hg
#align probability_theory.kernel.comap ProbabilityTheory.kernel.comap

theorem comap_apply (κ : kernel α β) (hg : Measurable g) (c : γ) : comap κ g hg c = κ (g c) :=
  rfl
#align probability_theory.kernel.comap_apply ProbabilityTheory.kernel.comap_apply

theorem comap_apply' (κ : kernel α β) (hg : Measurable g) (c : γ) (s : Set β) :
    comap κ g hg c s = κ (g c) s :=
  rfl
#align probability_theory.kernel.comap_apply' ProbabilityTheory.kernel.comap_apply'

@[simp]
lemma comap_zero (hg : Measurable g) : kernel.comap (0 : kernel α β) g hg = 0 := by
  ext; rw [kernel.comap_apply]; simp

@[simp]
lemma comap_id (κ : kernel α β) : comap κ id measurable_id = κ := by ext a; rw [comap_apply]; simp

@[simp]
lemma comap_id' (κ : kernel α β) : comap κ (fun a ↦ a) measurable_id = κ := comap_id κ

theorem lintegral_comap (κ : kernel α β) (hg : Measurable g) (c : γ) (g' : β → ℝ≥0∞) :
    ∫⁻ b, g' b ∂comap κ g hg c = ∫⁻ b, g' b ∂κ (g c) :=
  rfl
#align probability_theory.kernel.lintegral_comap ProbabilityTheory.kernel.lintegral_comap

theorem sum_comap_seq (κ : kernel α β) [IsSFiniteKernel κ] (hg : Measurable g) :
    (kernel.sum fun n => comap (seq κ n) g hg) = comap κ g hg := by
  ext a s hs
  rw [kernel.sum_apply, comap_apply' κ hg a s, Measure.sum_apply _ hs, ← measure_sum_seq κ,
    Measure.sum_apply _ hs]
  simp_rw [comap_apply' _ hg _ s]
#align probability_theory.kernel.sum_comap_seq ProbabilityTheory.kernel.sum_comap_seq

instance IsMarkovKernel.comap (κ : kernel α β) [IsMarkovKernel κ] (hg : Measurable g) :
    IsMarkovKernel (comap κ g hg) :=
  ⟨fun a => ⟨by rw [comap_apply' κ hg a Set.univ, measure_univ]⟩⟩
#align probability_theory.kernel.is_markov_kernel.comap ProbabilityTheory.kernel.IsMarkovKernel.comap

instance IsFiniteKernel.comap (κ : kernel α β) [IsFiniteKernel κ] (hg : Measurable g) :
    IsFiniteKernel (comap κ g hg) := by
  refine ⟨⟨IsFiniteKernel.bound κ, IsFiniteKernel.bound_lt_top κ, fun a => ?_⟩⟩
  rw [comap_apply' κ hg a Set.univ]
  exact measure_le_bound κ _ _
#align probability_theory.kernel.is_finite_kernel.comap ProbabilityTheory.kernel.IsFiniteKernel.comap

instance IsSFiniteKernel.comap (κ : kernel α β) [IsSFiniteKernel κ] (hg : Measurable g) :
    IsSFiniteKernel (comap κ g hg) :=
  ⟨⟨fun n => kernel.comap (seq κ n) g hg, inferInstance, (sum_comap_seq κ hg).symm⟩⟩
#align probability_theory.kernel.is_s_finite_kernel.comap ProbabilityTheory.kernel.IsSFiniteKernel.comap

lemma comap_map_comm (κ : kernel β γ) {f : α → β} {g : γ → δ}
    (hf : Measurable f) (hg : Measurable g) :
    comap (map κ g hg) f hf = map (comap κ f hf) g hg := by
  ext x s _
  rw [comap_apply, map_apply, map_apply, comap_apply]

end MapComap

open scoped ProbabilityTheory

section FstSnd

variable {δ : Type*} {mδ : MeasurableSpace δ}

/-- Define a `kernel (γ × α) β` from a `kernel α β` by taking the comap of the projection. -/
def prodMkLeft (γ : Type*) [MeasurableSpace γ] (κ : kernel α β) : kernel (γ × α) β :=
  comap κ Prod.snd measurable_snd
#align probability_theory.kernel.prod_mk_left ProbabilityTheory.kernel.prodMkLeft

/-- Define a `kernel (α × γ) β` from a `kernel α β` by taking the comap of the projection. -/
def prodMkRight (γ : Type*) [MeasurableSpace γ] (κ : kernel α β) : kernel (α × γ) β :=
  comap κ Prod.fst measurable_fst

variable {γ : Type*} {mγ : MeasurableSpace γ} {f : β → γ} {g : γ → α}

@[simp]
theorem prodMkLeft_apply (κ : kernel α β) (ca : γ × α) : prodMkLeft γ κ ca = κ ca.snd :=
  rfl
#align probability_theory.kernel.prod_mk_left_apply ProbabilityTheory.kernel.prodMkLeft_apply

@[simp]
theorem prodMkRight_apply (κ : kernel α β) (ca : α × γ) : prodMkRight γ κ ca = κ ca.fst := rfl

theorem prodMkLeft_apply' (κ : kernel α β) (ca : γ × α) (s : Set β) :
    prodMkLeft γ κ ca s = κ ca.snd s :=
  rfl
#align probability_theory.kernel.prod_mk_left_apply' ProbabilityTheory.kernel.prodMkLeft_apply'

theorem prodMkRight_apply' (κ : kernel α β) (ca : α × γ) (s : Set β) :
    prodMkRight γ κ ca s = κ ca.fst s := rfl

@[simp]
lemma prodMkLeft_zero : kernel.prodMkLeft α (0 : kernel β γ) = 0 := by
  ext x s _; simp

@[simp]
lemma prodMkRight_zero : kernel.prodMkRight α (0 : kernel β γ) = 0 := by
  ext x s _; simp

@[simp]
lemma prodMkLeft_add (κ η : kernel α β) :
    prodMkLeft γ (κ + η) = prodMkLeft γ κ + prodMkLeft γ η := by ext; simp

@[simp]
lemma prodMkRight_add (κ η : kernel α β) :
    prodMkRight γ (κ + η) = prodMkRight γ κ + prodMkRight γ η := by ext; simp

theorem lintegral_prodMkLeft (κ : kernel α β) (ca : γ × α) (g : β → ℝ≥0∞) :
    ∫⁻ b, g b ∂prodMkLeft γ κ ca = ∫⁻ b, g b ∂κ ca.snd := rfl
#align probability_theory.kernel.lintegral_prod_mk_left ProbabilityTheory.kernel.lintegral_prodMkLeft

theorem lintegral_prodMkRight (κ : kernel α β) (ca : α × γ) (g : β → ℝ≥0∞) :
    ∫⁻ b, g b ∂prodMkRight γ κ ca = ∫⁻ b, g b ∂κ ca.fst := rfl

instance IsMarkovKernel.prodMkLeft (κ : kernel α β) [IsMarkovKernel κ] :
    IsMarkovKernel (prodMkLeft γ κ) := by rw [kernel.prodMkLeft]; infer_instance
#align probability_theory.kernel.is_markov_kernel.prod_mk_left ProbabilityTheory.kernel.IsMarkovKernel.prodMkLeft

instance IsMarkovKernel.prodMkRight (κ : kernel α β) [IsMarkovKernel κ] :
    IsMarkovKernel (prodMkRight γ κ) := by rw [kernel.prodMkRight]; infer_instance

instance IsFiniteKernel.prodMkLeft (κ : kernel α β) [IsFiniteKernel κ] :
    IsFiniteKernel (prodMkLeft γ κ) := by rw [kernel.prodMkLeft]; infer_instance
#align probability_theory.kernel.is_finite_kernel.prod_mk_left ProbabilityTheory.kernel.IsFiniteKernel.prodMkLeft

instance IsFiniteKernel.prodMkRight (κ : kernel α β) [IsFiniteKernel κ] :
    IsFiniteKernel (prodMkRight γ κ) := by rw [kernel.prodMkRight]; infer_instance

instance IsSFiniteKernel.prodMkLeft (κ : kernel α β) [IsSFiniteKernel κ] :
    IsSFiniteKernel (prodMkLeft γ κ) := by rw [kernel.prodMkLeft]; infer_instance
#align probability_theory.kernel.is_s_finite_kernel.prod_mk_left ProbabilityTheory.kernel.IsSFiniteKernel.prodMkLeft

instance IsSFiniteKernel.prodMkRight (κ : kernel α β) [IsSFiniteKernel κ] :
    IsSFiniteKernel (prodMkRight γ κ) := by rw [kernel.prodMkRight]; infer_instance

lemma map_prodMkLeft (γ : Type*) [MeasurableSpace γ] (κ : kernel α β)
    {f : β → δ} (hf : Measurable f) :
    map (prodMkLeft γ κ) f hf = prodMkLeft γ (map κ f hf) := rfl

lemma map_prodMkRight (κ : kernel α β) (γ : Type*) [MeasurableSpace γ]
    {f : β → δ} (hf : Measurable f) :
    map (prodMkRight γ κ) f hf = prodMkRight γ (map κ f hf) := rfl

/-- Define a `kernel (β × α) γ` from a `kernel (α × β) γ` by taking the comap of `Prod.swap`. -/
def swapLeft (κ : kernel (α × β) γ) : kernel (β × α) γ :=
  comap κ Prod.swap measurable_swap
#align probability_theory.kernel.swap_left ProbabilityTheory.kernel.swapLeft

@[simp]
theorem swapLeft_apply (κ : kernel (α × β) γ) (a : β × α) : swapLeft κ a = κ a.swap := rfl
#align probability_theory.kernel.swap_left_apply ProbabilityTheory.kernel.swapLeft_apply

theorem swapLeft_apply' (κ : kernel (α × β) γ) (a : β × α) (s : Set γ) :
    swapLeft κ a s = κ a.swap s := rfl
#align probability_theory.kernel.swap_left_apply' ProbabilityTheory.kernel.swapLeft_apply'

theorem lintegral_swapLeft (κ : kernel (α × β) γ) (a : β × α) (g : γ → ℝ≥0∞) :
    ∫⁻ c, g c ∂swapLeft κ a = ∫⁻ c, g c ∂κ a.swap := by
  rw [swapLeft_apply]
#align probability_theory.kernel.lintegral_swap_left ProbabilityTheory.kernel.lintegral_swapLeft

instance IsMarkovKernel.swapLeft (κ : kernel (α × β) γ) [IsMarkovKernel κ] :
    IsMarkovKernel (swapLeft κ) := by rw [kernel.swapLeft]; infer_instance
#align probability_theory.kernel.is_markov_kernel.swap_left ProbabilityTheory.kernel.IsMarkovKernel.swapLeft

instance IsFiniteKernel.swapLeft (κ : kernel (α × β) γ) [IsFiniteKernel κ] :
    IsFiniteKernel (swapLeft κ) := by rw [kernel.swapLeft]; infer_instance
#align probability_theory.kernel.is_finite_kernel.swap_left ProbabilityTheory.kernel.IsFiniteKernel.swapLeft

instance IsSFiniteKernel.swapLeft (κ : kernel (α × β) γ) [IsSFiniteKernel κ] :
    IsSFiniteKernel (swapLeft κ) := by rw [kernel.swapLeft]; infer_instance
#align probability_theory.kernel.is_s_finite_kernel.swap_left ProbabilityTheory.kernel.IsSFiniteKernel.swapLeft

@[simp] lemma swapLeft_prodMkLeft (κ : kernel α β) (γ : Type*) [MeasurableSpace γ] :
    swapLeft (prodMkLeft γ κ) = prodMkRight γ κ := rfl

@[simp] lemma swapLeft_prodMkRight (κ : kernel α β) (γ : Type*) [MeasurableSpace γ] :
    swapLeft (prodMkRight γ κ) = prodMkLeft γ κ := rfl

/-- Define a `kernel α (γ × β)` from a `kernel α (β × γ)` by taking the map of `Prod.swap`. -/
noncomputable def swapRight (κ : kernel α (β × γ)) : kernel α (γ × β) :=
  map κ Prod.swap measurable_swap
#align probability_theory.kernel.swap_right ProbabilityTheory.kernel.swapRight

theorem swapRight_apply (κ : kernel α (β × γ)) (a : α) : swapRight κ a = (κ a).map Prod.swap :=
  rfl
#align probability_theory.kernel.swap_right_apply ProbabilityTheory.kernel.swapRight_apply

theorem swapRight_apply' (κ : kernel α (β × γ)) (a : α) {s : Set (γ × β)} (hs : MeasurableSet s) :
    swapRight κ a s = κ a {p | p.swap ∈ s} := by
  rw [swapRight_apply, Measure.map_apply measurable_swap hs]; rfl
#align probability_theory.kernel.swap_right_apply' ProbabilityTheory.kernel.swapRight_apply'

theorem lintegral_swapRight (κ : kernel α (β × γ)) (a : α) {g : γ × β → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ c, g c ∂swapRight κ a = ∫⁻ bc : β × γ, g bc.swap ∂κ a := by
  rw [swapRight, lintegral_map _ measurable_swap a hg]
#align probability_theory.kernel.lintegral_swap_right ProbabilityTheory.kernel.lintegral_swapRight

instance IsMarkovKernel.swapRight (κ : kernel α (β × γ)) [IsMarkovKernel κ] :
    IsMarkovKernel (swapRight κ) := by rw [kernel.swapRight]; infer_instance
#align probability_theory.kernel.is_markov_kernel.swap_right ProbabilityTheory.kernel.IsMarkovKernel.swapRight

instance IsFiniteKernel.swapRight (κ : kernel α (β × γ)) [IsFiniteKernel κ] :
    IsFiniteKernel (swapRight κ) := by rw [kernel.swapRight]; infer_instance
#align probability_theory.kernel.is_finite_kernel.swap_right ProbabilityTheory.kernel.IsFiniteKernel.swapRight

instance IsSFiniteKernel.swapRight (κ : kernel α (β × γ)) [IsSFiniteKernel κ] :
    IsSFiniteKernel (swapRight κ) := by rw [kernel.swapRight]; infer_instance
#align probability_theory.kernel.is_s_finite_kernel.swap_right ProbabilityTheory.kernel.IsSFiniteKernel.swapRight

/-- Define a `kernel α β` from a `kernel α (β × γ)` by taking the map of the first projection. -/
noncomputable def fst (κ : kernel α (β × γ)) : kernel α β :=
  map κ Prod.fst measurable_fst
#align probability_theory.kernel.fst ProbabilityTheory.kernel.fst

theorem fst_apply (κ : kernel α (β × γ)) (a : α) : fst κ a = (κ a).map Prod.fst :=
  rfl
#align probability_theory.kernel.fst_apply ProbabilityTheory.kernel.fst_apply

theorem fst_apply' (κ : kernel α (β × γ)) (a : α) {s : Set β} (hs : MeasurableSet s) :
    fst κ a s = κ a {p | p.1 ∈ s} := by rw [fst_apply, Measure.map_apply measurable_fst hs]; rfl
#align probability_theory.kernel.fst_apply' ProbabilityTheory.kernel.fst_apply'

@[simp]
lemma fst_zero : fst (0 : kernel α (β × γ)) = 0 := by simp [fst]

theorem lintegral_fst (κ : kernel α (β × γ)) (a : α) {g : β → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ c, g c ∂fst κ a = ∫⁻ bc : β × γ, g bc.fst ∂κ a := by
  rw [fst, lintegral_map _ measurable_fst a hg]
#align probability_theory.kernel.lintegral_fst ProbabilityTheory.kernel.lintegral_fst

instance IsMarkovKernel.fst (κ : kernel α (β × γ)) [IsMarkovKernel κ] : IsMarkovKernel (fst κ) := by
  rw [kernel.fst]; infer_instance
#align probability_theory.kernel.is_markov_kernel.fst ProbabilityTheory.kernel.IsMarkovKernel.fst

instance IsFiniteKernel.fst (κ : kernel α (β × γ)) [IsFiniteKernel κ] : IsFiniteKernel (fst κ) := by
  rw [kernel.fst]; infer_instance
#align probability_theory.kernel.is_finite_kernel.fst ProbabilityTheory.kernel.IsFiniteKernel.fst

instance IsSFiniteKernel.fst (κ : kernel α (β × γ)) [IsSFiniteKernel κ] :
    IsSFiniteKernel (fst κ) := by rw [kernel.fst]; infer_instance
#align probability_theory.kernel.is_s_finite_kernel.fst ProbabilityTheory.kernel.IsSFiniteKernel.fst

instance (priority := 100) isFiniteKernel_of_isFiniteKernel_fst {κ : kernel α (β × γ)}
    [h : IsFiniteKernel (fst κ)] :
    IsFiniteKernel κ := by
  refine ⟨h.bound, h.bound_lt_top, fun a ↦ le_trans ?_ (measure_le_bound (fst κ) a Set.univ)⟩
  rw [fst_apply' _ _ MeasurableSet.univ]
  simp

lemma fst_map_prod (κ : kernel α β) {f : β → γ} {g : β → δ}
    (hf : Measurable f) (hg : Measurable g) :
    fst (map κ (fun x ↦ (f x, g x)) (hf.prod_mk hg)) = map κ f hf := by
  ext x s hs
  rw [fst_apply' _ _ hs, map_apply', map_apply' _ _ _ hs]
  · rfl
  · exact measurable_fst hs

lemma fst_map_id_prod (κ : kernel α β) {γ : Type*} {mγ : MeasurableSpace γ}
    {f : β → γ} (hf : Measurable f) :
    fst (map κ (fun a ↦ (a, f a)) (measurable_id.prod_mk hf)) = κ := by
  rw [fst_map_prod _ measurable_id' hf, kernel.map_id']

@[simp]
lemma fst_compProd (κ : kernel α β) (η : kernel (α × β) γ) [IsSFiniteKernel κ] [IsMarkovKernel η] :
    fst (κ ⊗ₖ η) = κ := by
  ext x s hs
  rw [fst_apply' _ _ hs, compProd_apply]
  swap; · exact measurable_fst hs
  simp only [Set.mem_setOf_eq]
  classical
  have : ∀ b : β, η (x, b) {_c | b ∈ s} = s.indicator (fun _ ↦ 1) b := by
    intro b
    by_cases hb : b ∈ s <;> simp [hb]
  simp_rw [this]
  rw [lintegral_indicator_const hs, one_mul]

lemma fst_prodMkLeft (δ : Type*) [MeasurableSpace δ] (κ : kernel α (β × γ)) :
    fst (prodMkLeft δ κ) = prodMkLeft δ (fst κ) := rfl

lemma fst_prodMkRight (κ : kernel α (β × γ)) (δ : Type*) [MeasurableSpace δ] :
    fst (prodMkRight δ κ) = prodMkRight δ (fst κ) := rfl

/-- Define a `kernel α γ` from a `kernel α (β × γ)` by taking the map of the second projection. -/
noncomputable def snd (κ : kernel α (β × γ)) : kernel α γ :=
  map κ Prod.snd measurable_snd
#align probability_theory.kernel.snd ProbabilityTheory.kernel.snd

theorem snd_apply (κ : kernel α (β × γ)) (a : α) : snd κ a = (κ a).map Prod.snd :=
  rfl
#align probability_theory.kernel.snd_apply ProbabilityTheory.kernel.snd_apply

theorem snd_apply' (κ : kernel α (β × γ)) (a : α) {s : Set γ} (hs : MeasurableSet s) :
    snd κ a s = κ a {p | p.2 ∈ s} := by rw [snd_apply, Measure.map_apply measurable_snd hs]; rfl
#align probability_theory.kernel.snd_apply' ProbabilityTheory.kernel.snd_apply'

@[simp]
lemma snd_zero : snd (0 : kernel α (β × γ)) = 0 := by simp [snd]

theorem lintegral_snd (κ : kernel α (β × γ)) (a : α) {g : γ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ c, g c ∂snd κ a = ∫⁻ bc : β × γ, g bc.snd ∂κ a := by
  rw [snd, lintegral_map _ measurable_snd a hg]
#align probability_theory.kernel.lintegral_snd ProbabilityTheory.kernel.lintegral_snd

instance IsMarkovKernel.snd (κ : kernel α (β × γ)) [IsMarkovKernel κ] : IsMarkovKernel (snd κ) := by
  rw [kernel.snd]; infer_instance
#align probability_theory.kernel.is_markov_kernel.snd ProbabilityTheory.kernel.IsMarkovKernel.snd

instance IsFiniteKernel.snd (κ : kernel α (β × γ)) [IsFiniteKernel κ] : IsFiniteKernel (snd κ) := by
  rw [kernel.snd]; infer_instance
#align probability_theory.kernel.is_finite_kernel.snd ProbabilityTheory.kernel.IsFiniteKernel.snd

instance IsSFiniteKernel.snd (κ : kernel α (β × γ)) [IsSFiniteKernel κ] :
    IsSFiniteKernel (snd κ) := by rw [kernel.snd]; infer_instance
#align probability_theory.kernel.is_s_finite_kernel.snd ProbabilityTheory.kernel.IsSFiniteKernel.snd

instance (priority := 100) isFiniteKernel_of_isFiniteKernel_snd {κ : kernel α (β × γ)}
    [h : IsFiniteKernel (snd κ)] :
    IsFiniteKernel κ := by
  refine ⟨h.bound, h.bound_lt_top, fun a ↦ le_trans ?_ (measure_le_bound (snd κ) a Set.univ)⟩
  rw [snd_apply' _ _ MeasurableSet.univ]
  simp

lemma snd_map_prod (κ : kernel α β) {f : β → γ} {g : β → δ}
    (hf : Measurable f) (hg : Measurable g) :
    snd (map κ (fun x ↦ (f x, g x)) (hf.prod_mk hg)) = map κ g hg := by
  ext x s hs
  rw [snd_apply' _ _ hs, map_apply', map_apply' _ _ _ hs]
  · rfl
  · exact measurable_snd hs

lemma snd_map_prod_id (κ : kernel α β) {γ : Type*} {mγ : MeasurableSpace γ}
    {f : β → γ} (hf : Measurable f) :
    snd (map κ (fun a ↦ (f a, a)) (hf.prod_mk measurable_id)) = κ := by
  rw [snd_map_prod _ hf measurable_id', kernel.map_id']

lemma snd_prodMkLeft (δ : Type*) [MeasurableSpace δ] (κ : kernel α (β × γ)) :
    snd (prodMkLeft δ κ) = prodMkLeft δ (snd κ) := rfl

lemma snd_prodMkRight (κ : kernel α (β × γ)) (δ : Type*) [MeasurableSpace δ] :
    snd (prodMkRight δ κ) = prodMkRight δ (snd κ) := rfl

@[simp]
lemma fst_swapRight (κ : kernel α (β × γ)) : fst (swapRight κ) = snd κ := by
  ext a s hs
  rw [fst_apply' _ _ hs, swapRight_apply', snd_apply' _ _ hs]
  · rfl
  · exact measurable_fst hs

@[simp]
lemma snd_swapRight (κ : kernel α (β × γ)) : snd (swapRight κ) = fst κ := by
  ext a s hs
  rw [snd_apply' _ _ hs, swapRight_apply', fst_apply' _ _ hs]
  · rfl
  · exact measurable_snd hs

end FstSnd

section Comp

/-! ### Composition of two kernels -/


variable {γ : Type*} {mγ : MeasurableSpace γ} {f : β → γ} {g : γ → α}

/-- Composition of two kernels. -/
noncomputable def comp (η : kernel β γ) (κ : kernel α β) : kernel α γ where
  val a := (κ a).bind η
  property := (Measure.measurable_bind' (kernel.measurable _)).comp (kernel.measurable _)
#align probability_theory.kernel.comp ProbabilityTheory.kernel.comp

scoped[ProbabilityTheory] infixl:100 " ∘ₖ " => ProbabilityTheory.kernel.comp

theorem comp_apply (η : kernel β γ) (κ : kernel α β) (a : α) : (η ∘ₖ κ) a = (κ a).bind η :=
  rfl
#align probability_theory.kernel.comp_apply ProbabilityTheory.kernel.comp_apply

theorem comp_apply' (η : kernel β γ) (κ : kernel α β) (a : α) {s : Set γ} (hs : MeasurableSet s) :
    (η ∘ₖ κ) a s = ∫⁻ b, η b s ∂κ a := by
  rw [comp_apply, Measure.bind_apply hs (kernel.measurable _)]
#align probability_theory.kernel.comp_apply' ProbabilityTheory.kernel.comp_apply'

theorem comp_eq_snd_compProd (η : kernel β γ) [IsSFiniteKernel η] (κ : kernel α β)
    [IsSFiniteKernel κ] : η ∘ₖ κ = snd (κ ⊗ₖ prodMkLeft α η) := by
  ext a s hs
  rw [comp_apply' _ _ _ hs, snd_apply' _ _ hs, compProd_apply]
  swap
  · exact measurable_snd hs
  simp only [Set.mem_setOf_eq, Set.setOf_mem_eq, prodMkLeft_apply' _ _ s]
#align probability_theory.kernel.comp_eq_snd_comp_prod ProbabilityTheory.kernel.comp_eq_snd_compProd

theorem lintegral_comp (η : kernel β γ) (κ : kernel α β) (a : α) {g : γ → ℝ≥0∞}
    (hg : Measurable g) : ∫⁻ c, g c ∂(η ∘ₖ κ) a = ∫⁻ b, ∫⁻ c, g c ∂η b ∂κ a := by
  rw [comp_apply, Measure.lintegral_bind (kernel.measurable _) hg]
#align probability_theory.kernel.lintegral_comp ProbabilityTheory.kernel.lintegral_comp

instance IsMarkovKernel.comp (η : kernel β γ) [IsMarkovKernel η] (κ : kernel α β)
    [IsMarkovKernel κ] : IsMarkovKernel (η ∘ₖ κ) := by rw [comp_eq_snd_compProd]; infer_instance
#align probability_theory.kernel.is_markov_kernel.comp ProbabilityTheory.kernel.IsMarkovKernel.comp

instance IsFiniteKernel.comp (η : kernel β γ) [IsFiniteKernel η] (κ : kernel α β)
    [IsFiniteKernel κ] : IsFiniteKernel (η ∘ₖ κ) := by rw [comp_eq_snd_compProd]; infer_instance
#align probability_theory.kernel.is_finite_kernel.comp ProbabilityTheory.kernel.IsFiniteKernel.comp

instance IsSFiniteKernel.comp (η : kernel β γ) [IsSFiniteKernel η] (κ : kernel α β)
    [IsSFiniteKernel κ] : IsSFiniteKernel (η ∘ₖ κ) := by rw [comp_eq_snd_compProd]; infer_instance
#align probability_theory.kernel.is_s_finite_kernel.comp ProbabilityTheory.kernel.IsSFiniteKernel.comp

/-- Composition of kernels is associative. -/
theorem comp_assoc {δ : Type*} {mδ : MeasurableSpace δ} (ξ : kernel γ δ) [IsSFiniteKernel ξ]
    (η : kernel β γ) (κ : kernel α β) : ξ ∘ₖ η ∘ₖ κ = ξ ∘ₖ (η ∘ₖ κ) := by
  refine ext_fun fun a f hf => ?_
  simp_rw [lintegral_comp _ _ _ hf, lintegral_comp _ _ _ hf.lintegral_kernel]
#align probability_theory.kernel.comp_assoc ProbabilityTheory.kernel.comp_assoc

theorem deterministic_comp_eq_map (hf : Measurable f) (κ : kernel α β) :
    deterministic f hf ∘ₖ κ = map κ f hf := by
  ext a s hs
  simp_rw [map_apply' _ _ _ hs, comp_apply' _ _ _ hs, deterministic_apply' hf _ hs,
    lintegral_indicator_const_comp hf hs, one_mul]
#align probability_theory.kernel.deterministic_comp_eq_map ProbabilityTheory.kernel.deterministic_comp_eq_map

theorem comp_deterministic_eq_comap (κ : kernel α β) (hg : Measurable g) :
    κ ∘ₖ deterministic g hg = comap κ g hg := by
  ext a s hs
  simp_rw [comap_apply' _ _ _ s, comp_apply' _ _ _ hs, deterministic_apply hg a,
    lintegral_dirac' _ (kernel.measurable_coe κ hs)]
#align probability_theory.kernel.comp_deterministic_eq_comap ProbabilityTheory.kernel.comp_deterministic_eq_comap

end Comp

section Prod

/-! ### Product of two kernels -/


variable {γ : Type*} {mγ : MeasurableSpace γ}

/-- Product of two kernels. This is meaningful only when the kernels are s-finite. -/
noncomputable def prod (κ : kernel α β) (η : kernel α γ) : kernel α (β × γ) :=
  κ ⊗ₖ swapLeft (prodMkLeft β η)
#align probability_theory.kernel.prod ProbabilityTheory.kernel.prod

scoped[ProbabilityTheory] infixl:100 " ×ₖ " => ProbabilityTheory.kernel.prod

theorem prod_apply' (κ : kernel α β) [IsSFiniteKernel κ] (η : kernel α γ) [IsSFiniteKernel η]
    (a : α) {s : Set (β × γ)} (hs : MeasurableSet s) :
    (κ ×ₖ η) a s = ∫⁻ b : β, (η a) {c : γ | (b, c) ∈ s} ∂κ a := by
  simp_rw [prod, compProd_apply _ _ _ hs, swapLeft_apply _ _, prodMkLeft_apply, Prod.swap_prod_mk]
#align probability_theory.kernel.prod_apply ProbabilityTheory.kernel.prod_apply'

lemma prod_apply (κ : kernel α β) [IsSFiniteKernel κ] (η : kernel α γ) [IsSFiniteKernel η]
    (a : α) :
    (κ ×ₖ η) a = (κ a).prod (η a) := by
  ext s hs
  rw [prod_apply' _ _ _ hs, Measure.prod_apply hs]
  rfl

lemma prod_const (μ : Measure α) [SFinite μ] (ν : Measure β) [SFinite ν] :
    const α μ ×ₖ const α ν = const α (μ.prod ν) := by
  ext x
  rw [const_apply, prod_apply, const_apply, const_apply]

theorem lintegral_prod (κ : kernel α β) [IsSFiniteKernel κ] (η : kernel α γ) [IsSFiniteKernel η]
    (a : α) {g : β × γ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ c, g c ∂(κ ×ₖ η) a = ∫⁻ b, ∫⁻ c, g (b, c) ∂η a ∂κ a := by
  simp_rw [prod, lintegral_compProd _ _ _ hg, swapLeft_apply, prodMkLeft_apply, Prod.swap_prod_mk]
#align probability_theory.kernel.lintegral_prod ProbabilityTheory.kernel.lintegral_prod

instance IsMarkovKernel.prod (κ : kernel α β) [IsMarkovKernel κ] (η : kernel α γ)
    [IsMarkovKernel η] : IsMarkovKernel (κ ×ₖ η) := by rw [kernel.prod]; infer_instance
#align probability_theory.kernel.is_markov_kernel.prod ProbabilityTheory.kernel.IsMarkovKernel.prod

instance IsFiniteKernel.prod (κ : kernel α β) [IsFiniteKernel κ] (η : kernel α γ)
    [IsFiniteKernel η] : IsFiniteKernel (κ ×ₖ η) := by rw [kernel.prod]; infer_instance
#align probability_theory.kernel.is_finite_kernel.prod ProbabilityTheory.kernel.IsFiniteKernel.prod

instance IsSFiniteKernel.prod (κ : kernel α β) (η : kernel α γ) :
    IsSFiniteKernel (κ ×ₖ η) := by rw [kernel.prod]; infer_instance
#align probability_theory.kernel.is_s_finite_kernel.prod ProbabilityTheory.kernel.IsSFiniteKernel.prod

@[simp] lemma fst_prod (κ : kernel α β) [IsSFiniteKernel κ] (η : kernel α γ) [IsMarkovKernel η] :
    fst (κ ×ₖ η) = κ := by
  rw [prod]; simp

@[simp] lemma snd_prod (κ : kernel α β) [IsMarkovKernel κ] (η : kernel α γ) [IsSFiniteKernel η] :
    snd (κ ×ₖ η) = η := by
  ext x; simp [snd_apply, prod_apply]

end Prod

end kernel

end ProbabilityTheory
