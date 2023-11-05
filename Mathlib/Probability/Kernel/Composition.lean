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

theorem compProdFun_empty (κ : kernel α β) (η : kernel (α × β) γ) (a : α) :
    compProdFun κ η a ∅ = 0 := by
  simp only [compProdFun, Set.mem_empty_iff_false, Set.setOf_false, measure_empty,
    MeasureTheory.lintegral_const, zero_mul]

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

theorem compProdFun_tsum_left (κ : kernel α β) (η : kernel (α × β) γ) [IsSFiniteKernel κ] (a : α)
    (s : Set (β × γ)) : compProdFun κ η a s = ∑' n, compProdFun (seq κ n) η a s := by
  simp_rw [compProdFun, (measure_sum_seq κ _).symm, lintegral_sum_measure]

theorem compProdFun_eq_tsum (κ : kernel α β) [IsSFiniteKernel κ] (η : kernel (α × β) γ)
    [IsSFiniteKernel η] (a : α) (hs : MeasurableSet s) :
    compProdFun κ η a s = ∑' (n) (m), compProdFun (seq κ n) (seq η m) a s := by
  simp_rw [compProdFun_tsum_left κ η a s, compProdFun_tsum_right _ η a hs]

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

theorem measurable_compProdFun (κ : kernel α β) [IsSFiniteKernel κ] (η : kernel (α × β) γ)
    [IsSFiniteKernel η] (hs : MeasurableSet s) : Measurable fun a => compProdFun κ η a s := by
  simp_rw [compProdFun_tsum_right κ η _ hs]
  refine' Measurable.ennreal_tsum fun n => _
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

open Classical

/-- Composition-Product of kernels. For s-finite kernels, it satisfies
`∫⁻ bc, f bc ∂(compProd κ η a) = ∫⁻ b, ∫⁻ c, f (b, c) ∂(η (a, b)) ∂(κ a)`
(see `ProbabilityTheory.kernel.lintegral_compProd`).
If either of the kernels is not s-finite, `compProd` is given the junk value 0. -/
noncomputable def compProd (κ : kernel α β) (η : kernel (α × β) γ) : kernel α (β × γ) :=
if h : IsSFiniteKernel κ ∧ IsSFiniteKernel η then
{ val := λ a ↦
    Measure.ofMeasurable (fun s _ => compProdFun κ η a s) (compProdFun_empty κ η a)
      (@compProdFun_iUnion _ _ _ _ _ _ κ η h.2 a)
  property := by
    have : IsSFiniteKernel κ := h.1
    have : IsSFiniteKernel η := h.2
    refine' Measure.measurable_of_measurable_coe _ fun s hs => _
    have :
      (fun a =>
          Measure.ofMeasurable (fun s _ => compProdFun κ η a s) (compProdFun_empty κ η a)
            (compProdFun_iUnion κ η a) s) =
        fun a => compProdFun κ η a s :=
      by ext1 a; rwa [Measure.ofMeasurable_apply]
    rw [this]
    exact measurable_compProdFun κ η hs }
else 0

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

theorem compProd_null (a : α) (hs : MeasurableSet s) :
    (κ ⊗ₖ η) a s = 0 ↔ (fun b => η (a, b) (Prod.mk b ⁻¹' s)) =ᵐ[κ a] 0 := by
  rw [kernel.compProd_apply _ _ _ hs, lintegral_eq_zero_iff]
  · rfl
  · exact kernel.measurable_kernel_prod_mk_left' hs a

theorem ae_null_of_compProd_null (h : (κ ⊗ₖ η) a s = 0) :
    (fun b => η (a, b) (Prod.mk b ⁻¹' s)) =ᵐ[κ a] 0 := by
  obtain ⟨t, hst, mt, ht⟩ := exists_measurable_superset_of_null h
  simp_rw [compProd_null a mt] at ht
  rw [Filter.eventuallyLE_antisymm_iff]
  exact
    ⟨Filter.EventuallyLE.trans_eq
        (Filter.eventually_of_forall fun x => (measure_mono (Set.preimage_mono hst) : _)) ht,
      Filter.eventually_of_forall fun x => zero_le _⟩

theorem ae_ae_of_ae_compProd {p : β × γ → Prop} (h : ∀ᵐ bc ∂(κ ⊗ₖ η) a, p bc) :
    ∀ᵐ b ∂κ a, ∀ᵐ c ∂η (a, b), p (b, c) :=
  ae_null_of_compProd_null h

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

theorem compProd_restrict_left {s : Set β} (hs : MeasurableSet s) :
    kernel.restrict κ hs ⊗ₖ η = kernel.restrict (κ ⊗ₖ η) (hs.prod MeasurableSet.univ) := by
  rw [← compProd_restrict]; congr; exact kernel.restrict_univ.symm

theorem compProd_restrict_right {t : Set γ} (ht : MeasurableSet t) :
    κ ⊗ₖ kernel.restrict η ht = kernel.restrict (κ ⊗ₖ η) (MeasurableSet.univ.prod ht) := by
  rw [← compProd_restrict]; congr; exact kernel.restrict_univ.symm

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
        (fun ab => ∫⁻ c, f' (ab.2, c) ∂η ab) ∘ fun b => (a, b) :=
      by ext1 ab; rfl
    rw [this]
    refine' Measurable.comp _ measurable_prod_mk_left
    exact
      Measurable.lintegral_kernel_prod_right
        ((SimpleFunc.measurable _).comp (measurable_fst.snd.prod_mk measurable_snd))
  rw [lintegral_iSup]
  rotate_left
  · exact fun n => h_some_meas_integral (F n)
  · exact fun i j hij b => lintegral_mono fun c => h_mono hij _
  congr
  ext1 n
  -- Porting note: Added `(P := _)`
  refine' SimpleFunc.induction (P := fun f => (∫⁻ (a : β × γ), f a ∂(κ ⊗ₖ η) a =
      ∫⁻ (a_1 : β), ∫⁻ (c : γ), f (a_1, c) ∂η (a, a_1) ∂κ a)) _ _ (F n)
  · intro c s hs
    classical -- Porting note: Added `classical` for `Set.piecewise_eq_indicator`
    simp only [SimpleFunc.const_zero, SimpleFunc.coe_piecewise, SimpleFunc.coe_const,
      SimpleFunc.coe_zero, Set.piecewise_eq_indicator, Function.const, lintegral_indicator_const hs]
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

/-- Lebesgue integral against the composition-product of two kernels. -/
theorem lintegral_compProd (κ : kernel α β) [IsSFiniteKernel κ] (η : kernel (α × β) γ)
    [IsSFiniteKernel η] (a : α) {f : β × γ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ bc, f bc ∂(κ ⊗ₖ η) a = ∫⁻ b, ∫⁻ c, f (b, c) ∂η (a, b) ∂κ a := by
  let g := Function.curry f
  change ∫⁻ bc, f bc ∂(κ ⊗ₖ η) a = ∫⁻ b, ∫⁻ c, g b c ∂η (a, b) ∂κ a
  rw [← lintegral_compProd']
  · simp_rw [Function.curry_apply]
  · simp_rw [Function.uncurry_curry]; exact hf

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

theorem set_lintegral_compProd (κ : kernel α β) [IsSFiniteKernel κ] (η : kernel (α × β) γ)
    [IsSFiniteKernel η] (a : α) {f : β × γ → ℝ≥0∞} (hf : Measurable f) {s : Set β} {t : Set γ}
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    ∫⁻ z in s ×ˢ t, f z ∂(κ ⊗ₖ η) a = ∫⁻ x in s, ∫⁻ y in t, f (x, y) ∂η (a, x) ∂κ a := by
  simp_rw [← kernel.restrict_apply (κ ⊗ₖ η) (hs.prod ht), ← compProd_restrict hs ht,
    lintegral_compProd _ _ _ hf, kernel.restrict_apply]

theorem set_lintegral_compProd_univ_right (κ : kernel α β) [IsSFiniteKernel κ]
    (η : kernel (α × β) γ) [IsSFiniteKernel η] (a : α) {f : β × γ → ℝ≥0∞} (hf : Measurable f)
    {s : Set β} (hs : MeasurableSet s) :
    ∫⁻ z in s ×ˢ Set.univ, f z ∂(κ ⊗ₖ η) a = ∫⁻ x in s, ∫⁻ y, f (x, y) ∂η (a, x) ∂κ a := by
  simp_rw [set_lintegral_compProd κ η a hf hs MeasurableSet.univ, Measure.restrict_univ]

theorem set_lintegral_compProd_univ_left (κ : kernel α β) [IsSFiniteKernel κ] (η : kernel (α × β) γ)
    [IsSFiniteKernel η] (a : α) {f : β × γ → ℝ≥0∞} (hf : Measurable f) {t : Set γ}
    (ht : MeasurableSet t) :
    ∫⁻ z in Set.univ ×ˢ t, f z ∂(κ ⊗ₖ η) a = ∫⁻ x, ∫⁻ y in t, f (x, y) ∂η (a, x) ∂κ a := by
  simp_rw [set_lintegral_compProd κ η a hf MeasurableSet.univ ht, Measure.restrict_univ]

end Lintegral

theorem compProd_eq_tsum_compProd (κ : kernel α β) [IsSFiniteKernel κ] (η : kernel (α × β) γ)
    [IsSFiniteKernel η] (a : α) (hs : MeasurableSet s) :
    (κ ⊗ₖ η) a s = ∑' (n : ℕ) (m : ℕ), (seq κ n ⊗ₖ seq η m) a s := by
  simp_rw [compProd_apply_eq_compProdFun _ _ _ hs]; exact compProdFun_eq_tsum κ η a hs

theorem compProd_eq_sum_compProd (κ : kernel α β) [IsSFiniteKernel κ] (η : kernel (α × β) γ)
    [IsSFiniteKernel η] : κ ⊗ₖ η = kernel.sum fun n => kernel.sum fun m => seq κ n ⊗ₖ seq η m := by
  ext a s hs; simp_rw [kernel.sum_apply' _ a hs]; rw [compProd_eq_tsum_compProd κ η a hs]

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

theorem compProd_eq_sum_compProd_right (κ : kernel α β) (η : kernel (α × β) γ)
    [IsSFiniteKernel η] : κ ⊗ₖ η = kernel.sum fun n => κ ⊗ₖ seq η n := by
  by_cases hκ : IsSFiniteKernel κ
  swap
  · simp_rw [compProd_of_not_isSFiniteKernel_left _ _ hκ]
    simp
  rw [compProd_eq_sum_compProd]
  simp_rw [compProd_eq_sum_compProd_left κ _]
  rw [kernel.sum_comm]

instance IsMarkovKernel.compProd (κ : kernel α β) [IsMarkovKernel κ] (η : kernel (α × β) γ)
    [IsMarkovKernel η] : IsMarkovKernel (κ ⊗ₖ η) :=
  ⟨fun a =>
    ⟨by
      rw [compProd_apply κ η a MeasurableSet.univ]
      simp only [Set.mem_univ, Set.setOf_true, measure_univ, lintegral_one]⟩⟩

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
    _ = Cη * κ a Set.univ := (MeasureTheory.lintegral_const Cη)
    _ = κ a Set.univ * Cη := mul_comm _ _

instance IsFiniteKernel.compProd (κ : kernel α β) [IsFiniteKernel κ] (η : kernel (α × β) γ)
    [IsFiniteKernel η] : IsFiniteKernel (κ ⊗ₖ η) :=
  ⟨⟨IsFiniteKernel.bound κ * IsFiniteKernel.bound η,
      ENNReal.mul_lt_top (IsFiniteKernel.bound_ne_top κ) (IsFiniteKernel.bound_ne_top η), fun a =>
      calc
        (κ ⊗ₖ η) a Set.univ ≤ κ a Set.univ * IsFiniteKernel.bound η := compProd_apply_univ_le κ η a
        _ ≤ IsFiniteKernel.bound κ * IsFiniteKernel.bound η :=
          mul_le_mul (measure_le_bound κ a Set.univ) le_rfl (zero_le _) (zero_le _)⟩⟩

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

end CompositionProduct

section MapComap

/-! ### map, comap -/


variable {γ : Type*} {mγ : MeasurableSpace γ} {f : β → γ} {g : γ → α}

/-- The pushforward of a kernel along a measurable function.
We include measurability in the assumptions instead of using junk values
to make sure that typeclass inference can infer that the `map` of a Markov kernel
is again a Markov kernel. -/
noncomputable def map (κ : kernel α β) (f : β → γ) (hf : Measurable f) : kernel α γ where
  val a := (κ a).map f
  property := (Measure.measurable_map _ hf).comp (kernel.measurable κ)

theorem map_apply (κ : kernel α β) (hf : Measurable f) (a : α) : map κ f hf a = (κ a).map f :=
  rfl

theorem map_apply' (κ : kernel α β) (hf : Measurable f) (a : α) {s : Set γ} (hs : MeasurableSet s) :
    map κ f hf a s = κ a (f ⁻¹' s) := by rw [map_apply, Measure.map_apply hf hs]

@[simp]
lemma map_zero (hf : Measurable f) : kernel.map (0 : kernel α β) f hf = 0 := by
  ext; rw [kernel.map_apply]; simp

nonrec theorem lintegral_map (κ : kernel α β) (hf : Measurable f) (a : α) {g' : γ → ℝ≥0∞}
    (hg : Measurable g') : ∫⁻ b, g' b ∂map κ f hf a = ∫⁻ a, g' (f a) ∂κ a := by
  rw [map_apply _ hf, lintegral_map hg hf]

theorem sum_map_seq (κ : kernel α β) [IsSFiniteKernel κ] (hf : Measurable f) :
    (kernel.sum fun n => map (seq κ n) f hf) = map κ f hf := by
  ext a s hs
  rw [kernel.sum_apply, map_apply' κ hf a hs, Measure.sum_apply _ hs, ← measure_sum_seq κ,
    Measure.sum_apply _ (hf hs)]
  simp_rw [map_apply' _ hf _ hs]

instance IsMarkovKernel.map (κ : kernel α β) [IsMarkovKernel κ] (hf : Measurable f) :
    IsMarkovKernel (map κ f hf) :=
  ⟨fun a => ⟨by rw [map_apply' κ hf a MeasurableSet.univ, Set.preimage_univ, measure_univ]⟩⟩

instance IsFiniteKernel.map (κ : kernel α β) [IsFiniteKernel κ] (hf : Measurable f) :
    IsFiniteKernel (map κ f hf) := by
  refine' ⟨⟨IsFiniteKernel.bound κ, IsFiniteKernel.bound_lt_top κ, fun a => _⟩⟩
  rw [map_apply' κ hf a MeasurableSet.univ]
  exact measure_le_bound κ a _

instance IsSFiniteKernel.map (κ : kernel α β) [IsSFiniteKernel κ] (hf : Measurable f) :
    IsSFiniteKernel (map κ f hf) :=
  ⟨⟨fun n => kernel.map (seq κ n) f hf, inferInstance, (sum_map_seq κ hf).symm⟩⟩

/-- Pullback of a kernel, such that for each set s `comap κ g hg c s = κ (g c) s`.
We include measurability in the assumptions instead of using junk values
to make sure that typeclass inference can infer that the `comap` of a Markov kernel
is again a Markov kernel. -/
def comap (κ : kernel α β) (g : γ → α) (hg : Measurable g) : kernel γ β where
  val a := κ (g a)
  property := (kernel.measurable κ).comp hg

theorem comap_apply (κ : kernel α β) (hg : Measurable g) (c : γ) : comap κ g hg c = κ (g c) :=
  rfl

theorem comap_apply' (κ : kernel α β) (hg : Measurable g) (c : γ) (s : Set β) :
    comap κ g hg c s = κ (g c) s :=
  rfl

@[simp]
lemma comap_zero (hg : Measurable g) : kernel.comap (0 : kernel α β) g hg = 0 := by
  ext; rw [kernel.comap_apply]; simp

theorem lintegral_comap (κ : kernel α β) (hg : Measurable g) (c : γ) (g' : β → ℝ≥0∞) :
    ∫⁻ b, g' b ∂comap κ g hg c = ∫⁻ b, g' b ∂κ (g c) :=
  rfl

theorem sum_comap_seq (κ : kernel α β) [IsSFiniteKernel κ] (hg : Measurable g) :
    (kernel.sum fun n => comap (seq κ n) g hg) = comap κ g hg := by
  ext a s hs
  rw [kernel.sum_apply, comap_apply' κ hg a s, Measure.sum_apply _ hs, ← measure_sum_seq κ,
    Measure.sum_apply _ hs]
  simp_rw [comap_apply' _ hg _ s]

instance IsMarkovKernel.comap (κ : kernel α β) [IsMarkovKernel κ] (hg : Measurable g) :
    IsMarkovKernel (comap κ g hg) :=
  ⟨fun a => ⟨by rw [comap_apply' κ hg a Set.univ, measure_univ]⟩⟩

instance IsFiniteKernel.comap (κ : kernel α β) [IsFiniteKernel κ] (hg : Measurable g) :
    IsFiniteKernel (comap κ g hg) := by
  refine' ⟨⟨IsFiniteKernel.bound κ, IsFiniteKernel.bound_lt_top κ, fun a => _⟩⟩
  rw [comap_apply' κ hg a Set.univ]
  exact measure_le_bound κ _ _

instance IsSFiniteKernel.comap (κ : kernel α β) [IsSFiniteKernel κ] (hg : Measurable g) :
    IsSFiniteKernel (comap κ g hg) :=
  ⟨⟨fun n => kernel.comap (seq κ n) g hg, inferInstance, (sum_comap_seq κ hg).symm⟩⟩

end MapComap

open scoped ProbabilityTheory

section FstSnd

/-- Define a `kernel (γ × α) β` from a `kernel α β` by taking the comap of the projection. -/
def prodMkLeft (γ : Type*) [MeasurableSpace γ] (κ : kernel α β) : kernel (γ × α) β :=
  comap κ Prod.snd measurable_snd

variable {γ : Type*} {mγ : MeasurableSpace γ} {f : β → γ} {g : γ → α}

theorem prodMkLeft_apply (κ : kernel α β) (ca : γ × α) : prodMkLeft γ κ ca = κ ca.snd :=
  rfl

theorem prodMkLeft_apply' (κ : kernel α β) (ca : γ × α) (s : Set β) :
    prodMkLeft γ κ ca s = κ ca.snd s :=
  rfl

theorem lintegral_prodMkLeft (κ : kernel α β) (ca : γ × α) (g : β → ℝ≥0∞) :
    ∫⁻ b, g b ∂prodMkLeft γ κ ca = ∫⁻ b, g b ∂κ ca.snd :=
  rfl

instance IsMarkovKernel.prodMkLeft (κ : kernel α β) [IsMarkovKernel κ] :
    IsMarkovKernel (prodMkLeft γ κ) := by rw [kernel.prodMkLeft]; infer_instance

instance IsFiniteKernel.prodMkLeft (κ : kernel α β) [IsFiniteKernel κ] :
    IsFiniteKernel (prodMkLeft γ κ) := by rw [kernel.prodMkLeft]; infer_instance

instance IsSFiniteKernel.prodMkLeft (κ : kernel α β) [IsSFiniteKernel κ] :
    IsSFiniteKernel (prodMkLeft γ κ) := by rw [kernel.prodMkLeft]; infer_instance

/-- Define a `kernel (β × α) γ` from a `kernel (α × β) γ` by taking the comap of `Prod.swap`. -/
def swapLeft (κ : kernel (α × β) γ) : kernel (β × α) γ :=
  comap κ Prod.swap measurable_swap

theorem swapLeft_apply (κ : kernel (α × β) γ) (a : β × α) : swapLeft κ a = κ a.swap :=
  rfl

theorem swapLeft_apply' (κ : kernel (α × β) γ) (a : β × α) (s : Set γ) :
    swapLeft κ a s = κ a.swap s :=
  rfl

theorem lintegral_swapLeft (κ : kernel (α × β) γ) (a : β × α) (g : γ → ℝ≥0∞) :
    ∫⁻ c, g c ∂swapLeft κ a = ∫⁻ c, g c ∂κ a.swap := by
  rw [swapLeft, lintegral_comap _ measurable_swap a]

instance IsMarkovKernel.swapLeft (κ : kernel (α × β) γ) [IsMarkovKernel κ] :
    IsMarkovKernel (swapLeft κ) := by rw [kernel.swapLeft]; infer_instance

instance IsFiniteKernel.swapLeft (κ : kernel (α × β) γ) [IsFiniteKernel κ] :
    IsFiniteKernel (swapLeft κ) := by rw [kernel.swapLeft]; infer_instance

instance IsSFiniteKernel.swapLeft (κ : kernel (α × β) γ) [IsSFiniteKernel κ] :
    IsSFiniteKernel (swapLeft κ) := by rw [kernel.swapLeft]; infer_instance

/-- Define a `kernel α (γ × β)` from a `kernel α (β × γ)` by taking the map of `Prod.swap`. -/
noncomputable def swapRight (κ : kernel α (β × γ)) : kernel α (γ × β) :=
  map κ Prod.swap measurable_swap

theorem swapRight_apply (κ : kernel α (β × γ)) (a : α) : swapRight κ a = (κ a).map Prod.swap :=
  rfl

theorem swapRight_apply' (κ : kernel α (β × γ)) (a : α) {s : Set (γ × β)} (hs : MeasurableSet s) :
    swapRight κ a s = κ a {p | p.swap ∈ s} := by
  rw [swapRight_apply, Measure.map_apply measurable_swap hs]; rfl

theorem lintegral_swapRight (κ : kernel α (β × γ)) (a : α) {g : γ × β → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ c, g c ∂swapRight κ a = ∫⁻ bc : β × γ, g bc.swap ∂κ a := by
  rw [swapRight, lintegral_map _ measurable_swap a hg]

instance IsMarkovKernel.swapRight (κ : kernel α (β × γ)) [IsMarkovKernel κ] :
    IsMarkovKernel (swapRight κ) := by rw [kernel.swapRight]; infer_instance

instance IsFiniteKernel.swapRight (κ : kernel α (β × γ)) [IsFiniteKernel κ] :
    IsFiniteKernel (swapRight κ) := by rw [kernel.swapRight]; infer_instance

instance IsSFiniteKernel.swapRight (κ : kernel α (β × γ)) [IsSFiniteKernel κ] :
    IsSFiniteKernel (swapRight κ) := by rw [kernel.swapRight]; infer_instance

/-- Define a `kernel α β` from a `kernel α (β × γ)` by taking the map of the first projection. -/
noncomputable def fst (κ : kernel α (β × γ)) : kernel α β :=
  map κ Prod.fst measurable_fst

theorem fst_apply (κ : kernel α (β × γ)) (a : α) : fst κ a = (κ a).map Prod.fst :=
  rfl

theorem fst_apply' (κ : kernel α (β × γ)) (a : α) {s : Set β} (hs : MeasurableSet s) :
    fst κ a s = κ a {p | p.1 ∈ s} := by rw [fst_apply, Measure.map_apply measurable_fst hs]; rfl

theorem lintegral_fst (κ : kernel α (β × γ)) (a : α) {g : β → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ c, g c ∂fst κ a = ∫⁻ bc : β × γ, g bc.fst ∂κ a := by
  rw [fst, lintegral_map _ measurable_fst a hg]

instance IsMarkovKernel.fst (κ : kernel α (β × γ)) [IsMarkovKernel κ] : IsMarkovKernel (fst κ) := by
  rw [kernel.fst]; infer_instance

instance IsFiniteKernel.fst (κ : kernel α (β × γ)) [IsFiniteKernel κ] : IsFiniteKernel (fst κ) := by
  rw [kernel.fst]; infer_instance

instance IsSFiniteKernel.fst (κ : kernel α (β × γ)) [IsSFiniteKernel κ] : IsSFiniteKernel (fst κ) :=
  by rw [kernel.fst]; infer_instance

/-- Define a `kernel α γ` from a `kernel α (β × γ)` by taking the map of the second projection. -/
noncomputable def snd (κ : kernel α (β × γ)) : kernel α γ :=
  map κ Prod.snd measurable_snd

theorem snd_apply (κ : kernel α (β × γ)) (a : α) : snd κ a = (κ a).map Prod.snd :=
  rfl

theorem snd_apply' (κ : kernel α (β × γ)) (a : α) {s : Set γ} (hs : MeasurableSet s) :
    snd κ a s = κ a {p | p.2 ∈ s} := by rw [snd_apply, Measure.map_apply measurable_snd hs]; rfl

theorem lintegral_snd (κ : kernel α (β × γ)) (a : α) {g : γ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ c, g c ∂snd κ a = ∫⁻ bc : β × γ, g bc.snd ∂κ a := by
  rw [snd, lintegral_map _ measurable_snd a hg]

instance IsMarkovKernel.snd (κ : kernel α (β × γ)) [IsMarkovKernel κ] : IsMarkovKernel (snd κ) := by
  rw [kernel.snd]; infer_instance

instance IsFiniteKernel.snd (κ : kernel α (β × γ)) [IsFiniteKernel κ] : IsFiniteKernel (snd κ) := by
  rw [kernel.snd]; infer_instance

instance IsSFiniteKernel.snd (κ : kernel α (β × γ)) [IsSFiniteKernel κ] : IsSFiniteKernel (snd κ) :=
  by rw [kernel.snd]; infer_instance

end FstSnd

section Comp

/-! ### Composition of two kernels -/


variable {γ : Type*} {mγ : MeasurableSpace γ} {f : β → γ} {g : γ → α}

/-- Composition of two kernels. -/
noncomputable def comp (η : kernel β γ) (κ : kernel α β) : kernel α γ where
  val a := (κ a).bind η
  property := (Measure.measurable_bind' (kernel.measurable _)).comp (kernel.measurable _)

scoped[ProbabilityTheory] infixl:100 " ∘ₖ " => ProbabilityTheory.kernel.comp

theorem comp_apply (η : kernel β γ) (κ : kernel α β) (a : α) : (η ∘ₖ κ) a = (κ a).bind η :=
  rfl

theorem comp_apply' (η : kernel β γ) (κ : kernel α β) (a : α) {s : Set γ} (hs : MeasurableSet s) :
    (η ∘ₖ κ) a s = ∫⁻ b, η b s ∂κ a := by
  rw [comp_apply, Measure.bind_apply hs (kernel.measurable _)]

theorem comp_eq_snd_compProd (η : kernel β γ) [IsSFiniteKernel η] (κ : kernel α β)
    [IsSFiniteKernel κ] : η ∘ₖ κ = snd (κ ⊗ₖ prodMkLeft α η) := by
  ext a s hs
  rw [comp_apply' _ _ _ hs, snd_apply' _ _ hs, compProd_apply]
  swap
  · exact measurable_snd hs
  simp only [Set.mem_setOf_eq, Set.setOf_mem_eq, prodMkLeft_apply' _ _ s]

theorem lintegral_comp (η : kernel β γ) (κ : kernel α β) (a : α) {g : γ → ℝ≥0∞}
    (hg : Measurable g) : ∫⁻ c, g c ∂(η ∘ₖ κ) a = ∫⁻ b, ∫⁻ c, g c ∂η b ∂κ a := by
  rw [comp_apply, Measure.lintegral_bind (kernel.measurable _) hg]

instance IsMarkovKernel.comp (η : kernel β γ) [IsMarkovKernel η] (κ : kernel α β)
    [IsMarkovKernel κ] : IsMarkovKernel (η ∘ₖ κ) := by rw [comp_eq_snd_compProd]; infer_instance

instance IsFiniteKernel.comp (η : kernel β γ) [IsFiniteKernel η] (κ : kernel α β)
    [IsFiniteKernel κ] : IsFiniteKernel (η ∘ₖ κ) := by rw [comp_eq_snd_compProd]; infer_instance

instance IsSFiniteKernel.comp (η : kernel β γ) [IsSFiniteKernel η] (κ : kernel α β)
    [IsSFiniteKernel κ] : IsSFiniteKernel (η ∘ₖ κ) := by rw [comp_eq_snd_compProd]; infer_instance

/-- Composition of kernels is associative. -/
theorem comp_assoc {δ : Type*} {mδ : MeasurableSpace δ} (ξ : kernel γ δ) [IsSFiniteKernel ξ]
    (η : kernel β γ) (κ : kernel α β) : ξ ∘ₖ η ∘ₖ κ = ξ ∘ₖ (η ∘ₖ κ) := by
  refine' ext_fun fun a f hf => _
  simp_rw [lintegral_comp _ _ _ hf, lintegral_comp _ _ _ hf.lintegral_kernel]

theorem deterministic_comp_eq_map (hf : Measurable f) (κ : kernel α β) :
    deterministic f hf ∘ₖ κ = map κ f hf := by
  ext a s hs
  simp_rw [map_apply' _ _ _ hs, comp_apply' _ _ _ hs, deterministic_apply' hf _ hs,
    lintegral_indicator_const_comp hf hs, one_mul]

theorem comp_deterministic_eq_comap (κ : kernel α β) (hg : Measurable g) :
    κ ∘ₖ deterministic g hg = comap κ g hg := by
  ext a s hs
  simp_rw [comap_apply' _ _ _ s, comp_apply' _ _ _ hs, deterministic_apply hg a,
    lintegral_dirac' _ (kernel.measurable_coe κ hs)]

end Comp

section Prod

/-! ### Product of two kernels -/


variable {γ : Type*} {mγ : MeasurableSpace γ}

/-- Product of two kernels. This is meaningful only when the kernels are s-finite. -/
noncomputable def prod (κ : kernel α β) (η : kernel α γ) : kernel α (β × γ) :=
  κ ⊗ₖ swapLeft (prodMkLeft β η)

scoped[ProbabilityTheory] infixl:100 " ×ₖ " => ProbabilityTheory.kernel.prod

theorem prod_apply (κ : kernel α β) [IsSFiniteKernel κ] (η : kernel α γ) [IsSFiniteKernel η] (a : α)
    {s : Set (β × γ)} (hs : MeasurableSet s) :
    (κ ×ₖ η) a s = ∫⁻ b : β, (η a) {c : γ | (b, c) ∈ s} ∂κ a := by
  simp_rw [prod, compProd_apply _ _ _ hs, swapLeft_apply _ _, prodMkLeft_apply, Prod.swap_prod_mk]

theorem lintegral_prod (κ : kernel α β) [IsSFiniteKernel κ] (η : kernel α γ) [IsSFiniteKernel η]
    (a : α) {g : β × γ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ c, g c ∂(κ ×ₖ η) a = ∫⁻ b, ∫⁻ c, g (b, c) ∂η a ∂κ a := by
  simp_rw [prod, lintegral_compProd _ _ _ hg, swapLeft_apply, prodMkLeft_apply, Prod.swap_prod_mk]

instance IsMarkovKernel.prod (κ : kernel α β) [IsMarkovKernel κ] (η : kernel α γ)
    [IsMarkovKernel η] : IsMarkovKernel (κ ×ₖ η) := by rw [kernel.prod]; infer_instance

instance IsFiniteKernel.prod (κ : kernel α β) [IsFiniteKernel κ] (η : kernel α γ)
    [IsFiniteKernel η] : IsFiniteKernel (κ ×ₖ η) := by rw [kernel.prod]; infer_instance

instance IsSFiniteKernel.prod (κ : kernel α β) (η : kernel α γ) :
    IsSFiniteKernel (κ ×ₖ η) := by rw [kernel.prod]; infer_instance

end Prod

end kernel

end ProbabilityTheory
