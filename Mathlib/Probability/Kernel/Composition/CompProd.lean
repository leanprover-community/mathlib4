/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.Probability.Kernel.Composition.ParallelComp

/-!
# Composition-product of kernels

We define the composition-product `κ ⊗ₖ η` of two s-finite kernels `κ : Kernel α β` and
`η : Kernel (α × β) γ`, a kernel from `α` to `β × γ`.

A note on names:
The composition-product `Kernel α β → Kernel (α × β) γ → Kernel α (β × γ)` is named composition in
[kallenberg2021] and product on the wikipedia article on transition kernels.
Most papers studying categories of kernels call composition the map we call composition. We adopt
that convention because it fits better with the use of the name `comp` elsewhere in mathlib.

## Main definitions

* `compProd (κ : Kernel α β) (η : Kernel (α × β) γ) : Kernel α (β × γ)`: composition-product of 2
  s-finite kernels. We define a notation `κ ⊗ₖ η = compProd κ η`.
  `∫⁻ bc, f bc ∂((κ ⊗ₖ η) a) = ∫⁻ b, ∫⁻ c, f (b, c) ∂(η (a, b)) ∂(κ a)`

## Main statements

* `lintegral_compProd`: Lebesgue integral of a function against a composition-product of kernels.
* Instances stating that `IsMarkovKernel`, `IsZeroOrMarkovKernel`, `IsFiniteKernel` and
  `IsSFiniteKernel` are stable by composition-product.

## Notation

* `κ ⊗ₖ η = ProbabilityTheory.Kernel.compProd κ η`

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section


open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

namespace Kernel

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

section CompositionProduct

/-!
### Composition-Product of kernels

We define a kernel composition-product
`compProd : Kernel α β → Kernel (α × β) γ → Kernel α (β × γ)`.
-/

variable {s : Set (β × γ)}

/-- Composition-Product of kernels. For s-finite kernels, it satisfies
`∫⁻ bc, f bc ∂(compProd κ η a) = ∫⁻ b, ∫⁻ c, f (b, c) ∂(η (a, b)) ∂(κ a)`
(see `ProbabilityTheory.Kernel.lintegral_compProd`).
If either of the kernels is not s-finite, `compProd` is given the junk value 0. -/
noncomputable irreducible_def compProd (κ : Kernel α β) (η : Kernel (α × β) γ) : Kernel α (β × γ) :=
  swap γ β ∘ₖ (η ∥ₖ Kernel.id)
    ∘ₖ deterministic MeasurableEquiv.prodAssoc.symm (MeasurableEquiv.measurable _)
    ∘ₖ (Kernel.id ∥ₖ copy β) ∘ₖ (Kernel.id ∥ₖ κ) ∘ₖ copy α

@[inherit_doc]
scoped[ProbabilityTheory] infixl:100 " ⊗ₖ " => ProbabilityTheory.Kernel.compProd

@[simp]
theorem compProd_of_not_isSFiniteKernel_left (κ : Kernel α β) (η : Kernel (α × β) γ)
    (h : ¬ IsSFiniteKernel κ) :
    κ ⊗ₖ η = 0 := by
  simp [compProd_def, h]

@[simp]
theorem compProd_of_not_isSFiniteKernel_right (κ : Kernel α β) (η : Kernel (α × β) γ)
    (h : ¬ IsSFiniteKernel η) :
    κ ⊗ₖ η = 0 := by
  simp [compProd_def, h]

theorem compProd_apply (hs : MeasurableSet s) (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel (α × β) γ) [IsSFiniteKernel η] (a : α) :
    (κ ⊗ₖ η) a s = ∫⁻ b, η (a, b) (Prod.mk b ⁻¹' s) ∂κ a := by
  rw [compProd_def, comp_apply, copy_apply, Measure.dirac_bind (by fun_prop), comp_apply,
    parallelComp_apply, Kernel.id_apply, Measure.bind_apply hs (by fun_prop),
    lintegral_prod _ (Kernel.measurable_coe _ hs).aemeasurable, lintegral_dirac']
  swap
  · suffices Measurable fun p : α × β ↦
      (swap γ β ∘ₖ (η ∥ₖ Kernel.id)
        ∘ₖ deterministic MeasurableEquiv.prodAssoc.symm (MeasurableEquiv.measurable _)
        ∘ₖ (Kernel.id ∥ₖ copy β)) p s by fun_prop
    exact Kernel.measurable_coe _ hs
  congr with b
  rw [comp_apply, parallelComp_apply, Kernel.id_apply, copy_apply, Measure.dirac_prod_dirac,
    Measure.dirac_bind (by fun_prop), comp_apply, deterministic_apply (by fun_prop),
    Measure.dirac_bind (by fun_prop), comp_apply]
  simp only [MeasurableEquiv.prodAssoc, MeasurableEquiv.symm_mk, MeasurableEquiv.coe_mk,
    Equiv.prodAssoc_symm_apply]
  rw [parallelComp_apply, Kernel.id_apply, Measure.bind_apply hs (by fun_prop),
    lintegral_prod _ (Kernel.measurable_coe _ hs).aemeasurable]
  classical
  have h_int x : ∫⁻ y, swap γ β (x, y) s ∂Measure.dirac b = (Prod.mk b ⁻¹' s).indicator 1 x := by
    rw [lintegral_dirac']
    · simp [swap_apply' _ hs, Set.indicator_apply]
    · simpa [swap_apply' _ hs, Prod.swap_prod_mk] using
        measurable_const.indicator (measurable_prodMk_right hs)
  simp_rw [h_int]
  rw [lintegral_indicator_one]
  exact measurable_prodMk_left hs

theorem le_compProd_apply (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ)
    [IsSFiniteKernel η] (a : α) (s : Set (β × γ)) :
    ∫⁻ b, η (a, b) {c | (b, c) ∈ s} ∂κ a ≤ (κ ⊗ₖ η) a s :=
  calc
    ∫⁻ b, η (a, b) {c | (b, c) ∈ s} ∂κ a ≤
        ∫⁻ b, η (a, b) {c | (b, c) ∈ toMeasurable ((κ ⊗ₖ η) a) s} ∂κ a :=
      lintegral_mono fun _ => measure_mono fun _ h_mem => subset_toMeasurable _ _ h_mem
    _ = (κ ⊗ₖ η) a (toMeasurable ((κ ⊗ₖ η) a) s) :=
      (compProd_apply (measurableSet_toMeasurable _ _) κ η a).symm
    _ = (κ ⊗ₖ η) a s := measure_toMeasurable s

@[simp]
lemma compProd_apply_univ {κ : Kernel α β} {η : Kernel (α × β) γ}
    [IsSFiniteKernel κ] [IsMarkovKernel η] {a : α} :
    (κ ⊗ₖ η) a Set.univ = κ a Set.univ := by
  rw [compProd_apply MeasurableSet.univ]
  simp

lemma compProd_apply_prod {κ : Kernel α β} {η : Kernel (α × β) γ}
    [IsSFiniteKernel κ] [IsSFiniteKernel η] {a : α}
    {s : Set β} {t : Set γ} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (κ ⊗ₖ η) a (s ×ˢ t) = ∫⁻ b in s, η (a, b) t ∂(κ a) := by
  rw [compProd_apply (hs.prod ht), ← lintegral_indicator hs]
  congr with a
  by_cases ha : a ∈ s <;> simp [ha]

lemma compProd_congr {κ : Kernel α β} {η η' : Kernel (α × β) γ}
    [IsSFiniteKernel η] [IsSFiniteKernel η'] (h : ∀ a, ∀ᵐ b ∂(κ a), η (a, b) = η' (a, b)) :
    κ ⊗ₖ η = κ ⊗ₖ η' := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp_rw [compProd_of_not_isSFiniteKernel_left _ _ hκ]
  ext a s hs
  rw [compProd_apply hs, compProd_apply hs]
  refine lintegral_congr_ae ?_
  filter_upwards [h a] with b hb using by rw [hb]

@[simp]
lemma compProd_zero_left (κ : Kernel (α × β) γ) :
    (0 : Kernel α β) ⊗ₖ κ = 0 := by
  by_cases h : IsSFiniteKernel κ
  · ext a s hs
    rw [Kernel.compProd_apply hs]
    simp
  · rw [Kernel.compProd_of_not_isSFiniteKernel_right _ _ h]

@[simp]
lemma compProd_zero_right (κ : Kernel α β) (γ : Type*) {mγ : MeasurableSpace γ} :
    κ ⊗ₖ (0 : Kernel (α × β) γ) = 0 := by
  by_cases h : IsSFiniteKernel κ
  · ext a s hs
    rw [Kernel.compProd_apply hs]
    simp
  · rw [Kernel.compProd_of_not_isSFiniteKernel_left _ _ h]

lemma compProd_eq_zero_iff {κ : Kernel α β} {η : Kernel (α × β) γ}
    [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    κ ⊗ₖ η = 0 ↔ ∀ a, ∀ᵐ b ∂(κ a), η (a, b) = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp_rw [← Measure.measure_univ_eq_zero]
    refine fun a ↦ (lintegral_eq_zero_iff ?_).mp ?_
    · exact (η.measurable_coe .univ).comp measurable_prodMk_left
    · rw [← setLIntegral_univ, ← Kernel.compProd_apply_prod .univ .univ, h]
      simp
  · rw [← Kernel.compProd_zero_right κ]
    exact Kernel.compProd_congr h

lemma compProd_preimage_fst {s : Set β} (hs : MeasurableSet s) (κ : Kernel α β)
    (η : Kernel (α × β) γ) [IsSFiniteKernel κ] [IsMarkovKernel η] (x : α) :
    (κ ⊗ₖ η) x (Prod.fst ⁻¹' s) = κ x s := by
  classical
  simp_rw [compProd_apply (measurable_fst hs), ← Set.preimage_comp, Prod.fst_comp_mk, Set.preimage,
    Function.const_apply]
  have : ∀ b : β, η (x, b) {_c | b ∈ s} = s.indicator (fun _ ↦ 1) b := by
    intro b
    by_cases hb : b ∈ s <;> simp [hb]
  simp_rw [this]
  rw [lintegral_indicator_const hs, one_mul]

lemma compProd_deterministic_apply [MeasurableSingletonClass γ] {f : α × β → γ} (hf : Measurable f)
    {s : Set (β × γ)} (hs : MeasurableSet s) (κ : Kernel α β) [IsSFiniteKernel κ] (x : α) :
    (κ ⊗ₖ deterministic f hf) x s = κ x {b | (b, f (x, b)) ∈ s} := by
  classical
  simp only [deterministic_apply, Measure.dirac_apply,
    Set.indicator_apply, Pi.one_apply, compProd_apply hs]
  let t := {b | (b, f (x, b)) ∈ s}
  have ht : MeasurableSet t := (measurable_id.prodMk (hf.comp measurable_prodMk_left)) hs
  rw [← lintegral_add_compl _ ht]
  convert add_zero _
  · suffices ∀ b ∈ tᶜ, (if f (x, b) ∈ Prod.mk b ⁻¹' s then (1 : ℝ≥0∞) else 0) = 0 by
      rw [setLIntegral_congr_fun ht.compl this, lintegral_zero]
    intro b hb
    simp only [t, Set.mem_compl_iff, Set.mem_setOf_eq] at hb
    simp [hb]
  · suffices ∀ b ∈ t, (if f (x, b) ∈ Prod.mk b ⁻¹' s then (1 : ℝ≥0∞) else 0) = 1 by
      rw [setLIntegral_congr_fun ht this, setLIntegral_one]
    intro b hb
    simp only [t, Set.mem_setOf_eq] at hb
    simp [hb]

section Ae

/-! ### `ae` filter of the composition-product -/


variable {κ : Kernel α β} [IsSFiniteKernel κ] {η : Kernel (α × β) γ} [IsSFiniteKernel η] {a : α}

theorem ae_kernel_lt_top (a : α) (h2s : (κ ⊗ₖ η) a s ≠ ∞) :
    ∀ᵐ b ∂κ a, η (a, b) (Prod.mk b ⁻¹' s) < ∞ := by
  let t := toMeasurable ((κ ⊗ₖ η) a) s
  have : ∀ b : β, η (a, b) (Prod.mk b ⁻¹' s) ≤ η (a, b) (Prod.mk b ⁻¹' t) := fun b =>
    measure_mono (Set.preimage_mono (subset_toMeasurable _ _))
  have ht : MeasurableSet t := measurableSet_toMeasurable _ _
  have h2t : (κ ⊗ₖ η) a t ≠ ∞ := by rwa [measure_toMeasurable]
  have ht_lt_top : ∀ᵐ b ∂κ a, η (a, b) (Prod.mk b ⁻¹' t) < ∞ := by
    rw [Kernel.compProd_apply ht] at h2t
    exact ae_lt_top (Kernel.measurable_kernel_prodMk_left' ht a) h2t
  filter_upwards [ht_lt_top] with b hb
  exact (this b).trans_lt hb

theorem compProd_null (a : α) (hs : MeasurableSet s) :
    (κ ⊗ₖ η) a s = 0 ↔ (fun b => η (a, b) (Prod.mk b ⁻¹' s)) =ᵐ[κ a] 0 := by
  rw [Kernel.compProd_apply hs, lintegral_eq_zero_iff]
  exact Kernel.measurable_kernel_prodMk_left' hs a

theorem ae_null_of_compProd_null (h : (κ ⊗ₖ η) a s = 0) :
    (fun b => η (a, b) (Prod.mk b ⁻¹' s)) =ᵐ[κ a] 0 := by
  obtain ⟨t, hst, mt, ht⟩ := exists_measurable_superset_of_null h
  simp_rw [compProd_null a mt] at ht
  rw [Filter.eventuallyLE_antisymm_iff]
  exact
    ⟨Filter.EventuallyLE.trans_eq
        (Filter.Eventually.of_forall fun x => measure_mono (Set.preimage_mono hst)) ht,
      Filter.Eventually.of_forall fun x => zero_le _⟩

theorem ae_ae_of_ae_compProd {p : β × γ → Prop} (h : ∀ᵐ bc ∂(κ ⊗ₖ η) a, p bc) :
    ∀ᵐ b ∂κ a, ∀ᵐ c ∂η (a, b), p (b, c) :=
  ae_null_of_compProd_null h

lemma ae_compProd_of_ae_ae {κ : Kernel α β} {η : Kernel (α × β) γ}
    {p : β × γ → Prop} (hp : MeasurableSet {x | p x})
    (h : ∀ᵐ b ∂κ a, ∀ᵐ c ∂η (a, b), p (b, c)) :
    ∀ᵐ bc ∂(κ ⊗ₖ η) a, p bc := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [compProd_of_not_isSFiniteKernel_left _ _ hκ]
  by_cases hη : IsSFiniteKernel η
  swap; · simp [compProd_of_not_isSFiniteKernel_right _ _ hη]
  simp_rw [ae_iff] at h ⊢
  rw [compProd_null]
  · exact h
  · exact hp.compl

lemma ae_compProd_iff {p : β × γ → Prop} (hp : MeasurableSet {x | p x}) :
    (∀ᵐ bc ∂(κ ⊗ₖ η) a, p bc) ↔ ∀ᵐ b ∂κ a, ∀ᵐ c ∂η (a, b), p (b, c) :=
  ⟨fun h ↦ ae_ae_of_ae_compProd h, fun h ↦ ae_compProd_of_ae_ae hp h⟩

end Ae

section Restrict

variable {κ : Kernel α β} [IsSFiniteKernel κ] {η : Kernel (α × β) γ} [IsSFiniteKernel η]

theorem compProd_restrict {s : Set β} {t : Set γ} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    Kernel.restrict κ hs ⊗ₖ Kernel.restrict η ht = Kernel.restrict (κ ⊗ₖ η) (hs.prod ht) := by
  ext a u hu
  rw [compProd_apply hu, restrict_apply' _ _ _ hu, compProd_apply (hu.inter (hs.prod ht))]
  simp only [restrict_apply, Set.preimage, Measure.restrict_apply' ht, Set.mem_inter_iff,
    Set.mem_prod]
  have (b : _) : η (a, b) {c : γ | (b, c) ∈ u ∧ b ∈ s ∧ c ∈ t} =
      s.indicator (fun b => η (a, b) ({c : γ | (b, c) ∈ u} ∩ t)) b := by
    classical
    rw [Set.indicator_apply]
    split_ifs with h
    · simp only [h, true_and, Set.inter_def, Set.mem_setOf]
    · simp only [h, false_and, and_false, Set.setOf_false, measure_empty]
  simp_rw [this]
  rw [lintegral_indicator hs]

theorem compProd_restrict_left {s : Set β} (hs : MeasurableSet s) :
    Kernel.restrict κ hs ⊗ₖ η = Kernel.restrict (κ ⊗ₖ η) (hs.prod MeasurableSet.univ) := by
  rw [← compProd_restrict hs MeasurableSet.univ]
  congr; exact Kernel.restrict_univ.symm

theorem compProd_restrict_right {t : Set γ} (ht : MeasurableSet t) :
    κ ⊗ₖ Kernel.restrict η ht = Kernel.restrict (κ ⊗ₖ η) (MeasurableSet.univ.prod ht) := by
  rw [← compProd_restrict MeasurableSet.univ ht]
  congr; exact Kernel.restrict_univ.symm

end Restrict

section Lintegral

/-! ### Lebesgue integral -/


/-- Lebesgue integral against the composition-product of two kernels. -/
theorem lintegral_compProd' (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ)
    [IsSFiniteKernel η] (a : α) {f : β → γ → ℝ≥0∞} (hf : Measurable (Function.uncurry f)) :
    ∫⁻ bc, f bc.1 bc.2 ∂(κ ⊗ₖ η) a = ∫⁻ b, ∫⁻ c, f b c ∂η (a, b) ∂κ a := by
  let F : ℕ → SimpleFunc (β × γ) ℝ≥0∞ := SimpleFunc.eapprox (Function.uncurry f)
  have h : ∀ a, ⨆ n, F n a = Function.uncurry f a := SimpleFunc.iSup_eapprox_apply hf
  simp only [Prod.forall, Function.uncurry_apply_pair] at h
  simp_rw [← h]
  have h_mono : Monotone F := fun i j hij b =>
    SimpleFunc.monotone_eapprox (Function.uncurry f) hij _
  rw [lintegral_iSup (fun n => (F n).measurable) h_mono]
  have : ∀ b, ∫⁻ c, ⨆ n, F n (b, c) ∂η (a, b) = ⨆ n, ∫⁻ c, F n (b, c) ∂η (a, b) := by
    intro a
    rw [lintegral_iSup]
    · exact fun n => (F n).measurable.comp measurable_prodMk_left
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
    fun_prop
  rw [lintegral_iSup]
  rotate_left
  · exact fun n => h_some_meas_integral (F n)
  · exact fun i j hij b => lintegral_mono fun c => h_mono hij _
  congr
  ext1 n
  refine SimpleFunc.induction ?_ ?_ (F n)
  · intro c s hs
    simp +unfoldPartialApp only [SimpleFunc.const_zero,
      SimpleFunc.coe_piecewise, SimpleFunc.coe_const, SimpleFunc.coe_zero,
      Set.piecewise_eq_indicator, Function.const, lintegral_indicator_const hs]
    rw [compProd_apply hs, ← lintegral_const_mul c _]
    swap
    · exact (measurable_kernel_prodMk_left ((measurable_fst.snd.prodMk measurable_snd) hs)).comp
        measurable_prodMk_left
    congr
    ext1 b
    rw [lintegral_indicator_const_comp measurable_prodMk_left hs]
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
    exact (SimpleFunc.measurable _).comp measurable_prodMk_left

/-- Lebesgue integral against the composition-product of two kernels. -/
theorem lintegral_compProd (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ)
    [IsSFiniteKernel η] (a : α) {f : β × γ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ bc, f bc ∂(κ ⊗ₖ η) a = ∫⁻ b, ∫⁻ c, f (b, c) ∂η (a, b) ∂κ a := by
  let g := Function.curry f
  change ∫⁻ bc, f bc ∂(κ ⊗ₖ η) a = ∫⁻ b, ∫⁻ c, g b c ∂η (a, b) ∂κ a
  rw [← lintegral_compProd']
  · simp_rw [g, Function.curry_apply]
  · simp_rw [g, Function.uncurry_curry]; exact hf

/-- Lebesgue integral against the composition-product of two kernels. -/
theorem lintegral_compProd₀ (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ)
    [IsSFiniteKernel η] (a : α) {f : β × γ → ℝ≥0∞} (hf : AEMeasurable f ((κ ⊗ₖ η) a)) :
    ∫⁻ z, f z ∂(κ ⊗ₖ η) a = ∫⁻ x, ∫⁻ y, f (x, y) ∂η (a, x) ∂κ a := by
  have A : ∫⁻ z, f z ∂(κ ⊗ₖ η) a = ∫⁻ z, hf.mk f z ∂(κ ⊗ₖ η) a := lintegral_congr_ae hf.ae_eq_mk
  have B : ∫⁻ x, ∫⁻ y, f (x, y) ∂η (a, x) ∂κ a = ∫⁻ x, ∫⁻ y, hf.mk f (x, y) ∂η (a, x) ∂κ a := by
    apply lintegral_congr_ae
    filter_upwards [ae_ae_of_ae_compProd hf.ae_eq_mk] with _ ha using lintegral_congr_ae ha
  rw [A, B, lintegral_compProd]
  exact hf.measurable_mk

theorem setLIntegral_compProd (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ)
    [IsSFiniteKernel η] (a : α) {f : β × γ → ℝ≥0∞} (hf : Measurable f) {s : Set β} {t : Set γ}
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    ∫⁻ z in s ×ˢ t, f z ∂(κ ⊗ₖ η) a = ∫⁻ x in s, ∫⁻ y in t, f (x, y) ∂η (a, x) ∂κ a := by
  simp_rw [← Kernel.restrict_apply (κ ⊗ₖ η) (hs.prod ht), ← compProd_restrict hs ht,
    lintegral_compProd _ _ _ hf, Kernel.restrict_apply]

theorem setLIntegral_compProd_univ_right (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel (α × β) γ) [IsSFiniteKernel η] (a : α) {f : β × γ → ℝ≥0∞} (hf : Measurable f)
    {s : Set β} (hs : MeasurableSet s) :
    ∫⁻ z in s ×ˢ Set.univ, f z ∂(κ ⊗ₖ η) a = ∫⁻ x in s, ∫⁻ y, f (x, y) ∂η (a, x) ∂κ a := by
  simp_rw [setLIntegral_compProd κ η a hf hs MeasurableSet.univ, Measure.restrict_univ]

theorem setLIntegral_compProd_univ_left (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ)
    [IsSFiniteKernel η] (a : α) {f : β × γ → ℝ≥0∞} (hf : Measurable f) {t : Set γ}
    (ht : MeasurableSet t) :
    ∫⁻ z in Set.univ ×ˢ t, f z ∂(κ ⊗ₖ η) a = ∫⁻ x, ∫⁻ y in t, f (x, y) ∂η (a, x) ∂κ a := by
  simp_rw [setLIntegral_compProd κ η a hf MeasurableSet.univ ht, Measure.restrict_univ]

end Lintegral

theorem compProd_eq_sum_compProd_left (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) :
    κ ⊗ₖ η = Kernel.sum fun n ↦ seq κ n ⊗ₖ η := by
  simp_rw [compProd_def]
  rw [← comp_sum_left, ← comp_sum_right, ← parallelComp_sum_right, kernel_sum_seq]

theorem compProd_eq_sum_compProd_right (κ : Kernel α β) (η : Kernel (α × β) γ)
    [IsSFiniteKernel η] : κ ⊗ₖ η = Kernel.sum fun n => κ ⊗ₖ seq η n := by
  simp_rw [compProd_def]
  rw [← comp_sum_left, ← comp_sum_left, ← comp_sum_left, ← comp_sum_left, ← comp_sum_right,
    ← parallelComp_sum_left, kernel_sum_seq]

theorem compProd_eq_sum_compProd (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ)
    [IsSFiniteKernel η] : κ ⊗ₖ η = Kernel.sum fun n ↦ Kernel.sum fun m ↦ seq κ n ⊗ₖ seq η m := by
  simp_rw [← compProd_eq_sum_compProd_right, ← compProd_eq_sum_compProd_left]

theorem compProd_eq_tsum_compProd (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ)
    [IsSFiniteKernel η] (a : α) (hs : MeasurableSet s) :
    (κ ⊗ₖ η) a s = ∑' (n : ℕ) (m : ℕ), (seq κ n ⊗ₖ seq η m) a s := by
  rw [compProd_eq_sum_compProd]
  simp_rw [sum_apply' _ _ hs]

instance IsMarkovKernel.compProd (κ : Kernel α β) [IsMarkovKernel κ] (η : Kernel (α × β) γ)
    [IsMarkovKernel η] : IsMarkovKernel (κ ⊗ₖ η) where
  isProbabilityMeasure a := ⟨by simp [compProd_apply]⟩

instance IsZeroOrMarkovKernel.compProd (κ : Kernel α β) [IsZeroOrMarkovKernel κ]
    (η : Kernel (α × β) γ) [IsZeroOrMarkovKernel η] : IsZeroOrMarkovKernel (κ ⊗ₖ η) := by
  rw [compProd_def]
  infer_instance

theorem compProd_apply_univ_le (κ : Kernel α β) (η : Kernel (α × β) γ) [IsFiniteKernel η] (a : α) :
    (κ ⊗ₖ η) a Set.univ ≤ κ a Set.univ * η.bound := by
  by_cases hκ : IsSFiniteKernel κ
  swap
  · rw [compProd_of_not_isSFiniteKernel_left _ _ hκ]
    simp
  rw [compProd_apply .univ]
  let Cη := η.bound
  calc
    ∫⁻ b, η (a, b) Set.univ ∂κ a ≤ ∫⁻ _, Cη ∂κ a :=
      lintegral_mono fun b => measure_le_bound η (a, b) Set.univ
    _ = Cη * κ a Set.univ := MeasureTheory.lintegral_const Cη
    _ = κ a Set.univ * Cη := mul_comm _ _

instance IsFiniteKernel.compProd (κ : Kernel α β) [IsFiniteKernel κ] (η : Kernel (α × β) γ)
    [IsFiniteKernel η] : IsFiniteKernel (κ ⊗ₖ η) := by
  rw [compProd_def]
  infer_instance

instance IsSFiniteKernel.compProd (κ : Kernel α β) (η : Kernel (α × β) γ) :
    IsSFiniteKernel (κ ⊗ₖ η) := by
  rw [compProd_def]
  infer_instance

/-- `Kernel.compProd` is associative. We have to insert `MeasurableEquiv.prodAssoc` in two places
because the products of types `α × β × γ` and `(α × β) × γ` are different. -/
lemma compProd_assoc {δ : Type*} {mδ : MeasurableSpace δ}
    {κ : Kernel α β} {η : Kernel (α × β) γ} {ξ : Kernel (α × β × γ) δ} :
    (κ ⊗ₖ (η ⊗ₖ (ξ.comap MeasurableEquiv.prodAssoc (MeasurableEquiv.measurable _)))).map
        MeasurableEquiv.prodAssoc.symm
      = κ ⊗ₖ η ⊗ₖ ξ := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  by_cases hη : IsSFiniteKernel η
  swap; · simp [hη]
  by_cases hξ : IsSFiniteKernel ξ
  swap
  · have : ¬ IsSFiniteKernel
        (ξ.comap MeasurableEquiv.prodAssoc (MeasurableEquiv.measurable _)) := by
      refine fun h_sfin ↦ hξ ?_
      have : ξ = (ξ.comap MeasurableEquiv.prodAssoc (MeasurableEquiv.measurable _)).comap
          MeasurableEquiv.prodAssoc.symm (MeasurableEquiv.measurable _) := by
        simp [← comap_comp_right]
      rw [this]
      infer_instance
    simp [hξ, this]
  ext a s hs
  rw [compProd_apply hs, map_apply' _ (by fun_prop) _ hs,
    compProd_apply (hs.preimage (by fun_prop)), lintegral_compProd]
  swap; · exact measurable_kernel_prodMk_left' hs a
  congr with b
  rw [compProd_apply]
  · congr
  · exact hs.preimage (by fun_prop)

lemma compProd_add_left (μ κ : Kernel α β) (η : Kernel (α × β) γ)
    [IsSFiniteKernel μ] [IsSFiniteKernel κ] :
    (μ + κ) ⊗ₖ η = μ ⊗ₖ η + κ ⊗ₖ η := by
  by_cases hη : IsSFiniteKernel η
  · ext _ _ hs
    simp [compProd_apply hs]
  · simp [hη]

lemma compProd_add_right (μ : Kernel α β) (κ η : Kernel (α × β) γ)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    μ ⊗ₖ (κ + η) = μ ⊗ₖ κ + μ ⊗ₖ η := by
  by_cases hμ : IsSFiniteKernel μ
  swap; · simp [hμ]
  ext a s hs
  simp only [compProd_apply hs, coe_add, Pi.add_apply, Measure.coe_add]
  rw [lintegral_add_left]
  exact measurable_kernel_prodMk_left' hs a

lemma compProd_sum_left {ι : Type*} [Countable ι]
    {κ : ι → Kernel α β} {η : Kernel (α × β) γ} [∀ i, IsSFiniteKernel (κ i)] :
    Kernel.sum κ ⊗ₖ η = Kernel.sum (fun i ↦ (κ i) ⊗ₖ η) := by
  by_cases hη : IsSFiniteKernel η
  · ext a s hs
    simp_rw [sum_apply, compProd_apply hs, sum_apply, lintegral_sum_measure, Measure.sum_apply _ hs,
    compProd_apply hs]
  · simp [hη]

lemma compProd_sum_right {ι : Type*} [Countable ι]
    {κ : Kernel α β} {η : ι → Kernel (α × β) γ} [∀ i, IsSFiniteKernel (η i)] :
    κ ⊗ₖ Kernel.sum η = Kernel.sum (fun i ↦ κ ⊗ₖ (η i)) := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  ext a s hs
  simp_rw [sum_apply, compProd_apply hs, Measure.sum_apply _ hs, sum_apply, compProd_apply hs]
  rw [← lintegral_tsum]
  · congr with i
    rw [Measure.sum_apply]
    exact measurable_prodMk_left hs
  · exact fun _ ↦ (measurable_kernel_prodMk_left' hs a).aemeasurable

lemma comapRight_compProd_id_prod {δ : Type*} {mδ : MeasurableSpace δ}
    (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKernel η]
    {f : δ → γ} (hf : MeasurableEmbedding f) :
    comapRight (κ ⊗ₖ η) (MeasurableEmbedding.id.prodMap hf) = κ ⊗ₖ (comapRight η hf) := by
  ext a t ht
  rw [comapRight_apply' _ _ _ ht, compProd_apply, compProd_apply ht]
  · refine lintegral_congr fun b ↦ ?_
    rw [comapRight_apply']
    · congr with x
      grind
    · exact measurable_prodMk_left ht
  · exact (MeasurableEmbedding.id.prodMap hf).measurableSet_image.mpr ht

end CompositionProduct

open scoped ProbabilityTheory

section FstSnd

variable {δ : Type*} {mδ : MeasurableSpace δ}

/-- If `η` is a Markov kernel, use instead `fst_compProd` to get `(κ ⊗ₖ η).fst = κ`. -/
lemma fst_compProd_apply (κ : Kernel α β) (η : Kernel (α × β) γ)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] (x : α) {s : Set β} (hs : MeasurableSet s) :
    (κ ⊗ₖ η).fst x s = ∫⁻ b, s.indicator (fun b ↦ η (x, b) Set.univ) b ∂(κ x) := by
  rw [Kernel.fst_apply' _ _ hs, Kernel.compProd_apply]
  swap; · exact measurable_fst hs
  have h_eq b : η (x, b) {c | b ∈ s} = s.indicator (fun b ↦ η (x, b) Set.univ) b := by
    by_cases hb : b ∈ s <;> simp [hb]
  simp_rw [Set.preimage, Set.mem_setOf_eq, h_eq]

@[simp]
lemma fst_compProd (κ : Kernel α β) (η : Kernel (α × β) γ) [IsSFiniteKernel κ] [IsMarkovKernel η] :
    fst (κ ⊗ₖ η) = κ := by
  ext x s hs; simp [fst_compProd_apply, hs]

end FstSnd

end Kernel
end ProbabilityTheory
