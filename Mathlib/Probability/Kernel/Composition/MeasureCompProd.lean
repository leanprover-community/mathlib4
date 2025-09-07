/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Kernel.Composition.CompProd

/-!
# Composition-Product of a measure and a kernel

This operation, denoted by `⊗ₘ`, takes `μ : Measure α` and `κ : Kernel α β` and creates
`μ ⊗ₘ κ : Measure (α × β)`. The integral of a function against `μ ⊗ₘ κ` is
`∫⁻ x, f x ∂(μ ⊗ₘ κ) = ∫⁻ a, ∫⁻ b, f (a, b) ∂(κ a) ∂μ`.

`μ ⊗ₘ κ` is defined as `((Kernel.const Unit μ) ⊗ₖ (Kernel.prodMkLeft Unit κ)) ()`.

## Main definitions

* `Measure.compProd`: from `μ : Measure α` and `κ : Kernel α β`, get a `Measure (α × β)`.

## Notations

* `μ ⊗ₘ κ = μ.compProd κ`
-/

open scoped ENNReal

open ProbabilityTheory Set

namespace MeasureTheory.Measure

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {κ η : Kernel α β}

/-- The composition-product of a measure and a kernel. -/
noncomputable
def compProd (μ : Measure α) (κ : Kernel α β) : Measure (α × β) :=
  (Kernel.const Unit μ ⊗ₖ Kernel.prodMkLeft Unit κ) ()

@[inherit_doc]
scoped[ProbabilityTheory] infixl:100 " ⊗ₘ " => MeasureTheory.Measure.compProd

@[simp]
lemma compProd_of_not_sfinite (μ : Measure α) (κ : Kernel α β) (h : ¬ SFinite μ) :
    μ ⊗ₘ κ = 0 := by
  rw [compProd, Kernel.compProd_of_not_isSFiniteKernel_left, Kernel.zero_apply]
  rwa [Kernel.isSFiniteKernel_const]

@[simp]
lemma compProd_of_not_isSFiniteKernel (μ : Measure α) (κ : Kernel α β) (h : ¬ IsSFiniteKernel κ) :
    μ ⊗ₘ κ = 0 := by
  rw [compProd, Kernel.compProd_of_not_isSFiniteKernel_right, Kernel.zero_apply]
  rwa [Kernel.isSFiniteKernel_prodMkLeft_unit]

lemma compProd_apply [SFinite μ] [IsSFiniteKernel κ] {s : Set (α × β)} (hs : MeasurableSet s) :
    (μ ⊗ₘ κ) s = ∫⁻ a, κ a (Prod.mk a ⁻¹' s) ∂μ := by
  simp_rw [compProd, Kernel.compProd_apply hs, Kernel.const_apply, Kernel.prodMkLeft_apply']

@[simp]
lemma compProd_apply_univ [SFinite μ] [IsMarkovKernel κ] : (μ ⊗ₘ κ) univ = μ univ := by
  simp [compProd]

lemma compProd_apply_prod [SFinite μ] [IsSFiniteKernel κ]
    {s : Set α} {t : Set β} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (μ ⊗ₘ κ) (s ×ˢ t) = ∫⁻ a in s, κ a t ∂μ := by
  simp [compProd, Kernel.compProd_apply_prod hs ht]

lemma compProd_congr [IsSFiniteKernel κ] [IsSFiniteKernel η] (h : κ =ᵐ[μ] η) :
    μ ⊗ₘ κ = μ ⊗ₘ η := by
  rw [compProd, compProd]
  congr 1
  refine Kernel.compProd_congr ?_
  simpa

@[simp] lemma compProd_zero_left (κ : Kernel α β) : (0 : Measure α) ⊗ₘ κ = 0 := by simp [compProd]

@[simp] lemma compProd_zero_right (μ : Measure α) : μ ⊗ₘ (0 : Kernel α β) = 0 := by simp [compProd]

lemma compProd_eq_zero_iff [SFinite μ] [IsSFiniteKernel κ] :
    μ ⊗ₘ κ = 0 ↔ ∀ᵐ a ∂μ, κ a = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp_rw [← measure_univ_eq_zero]
    refine (lintegral_eq_zero_iff (Kernel.measurable_coe _ .univ)).mp ?_
    rw [← setLIntegral_univ, ← compProd_apply_prod .univ .univ, h]
    simp
  · rw [← compProd_zero_right μ]
    exact compProd_congr h

lemma _root_.ProbabilityTheory.Kernel.compProd_apply_eq_compProd_sectR {γ : Type*}
    {mγ : MeasurableSpace γ} (κ : Kernel α β) (η : Kernel (α × β) γ)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] (a : α) :
    (κ ⊗ₖ η) a = (κ a) ⊗ₘ (Kernel.sectR η a) := by
  ext s hs
  simp_rw [Kernel.compProd_apply hs, compProd_apply hs, Kernel.sectR_apply]

lemma compProd_id [SFinite μ] : μ ⊗ₘ Kernel.id = μ.map (fun x ↦ (x, x)) := by
  ext s hs
  rw [compProd_apply hs, map_apply (measurable_id.prod measurable_id) hs]
  have h_meas a : MeasurableSet (Prod.mk a ⁻¹' s) := measurable_prodMk_left hs
  simp_rw [Kernel.id_apply, dirac_apply' _ (h_meas _)]
  calc ∫⁻ a, (Prod.mk a ⁻¹' s).indicator 1 a ∂μ
  _ = ∫⁻ a, ((fun x ↦ (x, x)) ⁻¹' s).indicator 1 a ∂μ := rfl
  _ = μ ((fun x ↦ (x, x)) ⁻¹' s) := by
    rw [lintegral_indicator_one]
    exact (measurable_id.prod measurable_id) hs

lemma ae_compProd_of_ae_ae {p : α × β → Prop}
    (hp : MeasurableSet {x | p x}) (h : ∀ᵐ a ∂μ, ∀ᵐ b ∂(κ a), p (a, b)) :
    ∀ᵐ x ∂(μ ⊗ₘ κ), p x :=
  Kernel.ae_compProd_of_ae_ae hp h

lemma ae_ae_of_ae_compProd [SFinite μ] [IsSFiniteKernel κ] {p : α × β → Prop}
    (h : ∀ᵐ x ∂(μ ⊗ₘ κ), p x) :
    ∀ᵐ a ∂μ, ∀ᵐ b ∂κ a, p (a, b) := by
  convert Kernel.ae_ae_of_ae_compProd h -- Much faster with `convert`

lemma ae_compProd_iff [SFinite μ] [IsSFiniteKernel κ] {p : α × β → Prop}
    (hp : MeasurableSet {x | p x}) :
    (∀ᵐ x ∂(μ ⊗ₘ κ), p x) ↔ ∀ᵐ a ∂μ, ∀ᵐ b ∂(κ a), p (a, b) :=
  Kernel.ae_compProd_iff hp

/-- The composition product of a measure and a constant kernel is the product between the two
measures. -/
@[simp]
lemma compProd_const {ν : Measure β} [SFinite μ] [SFinite ν] :
    μ ⊗ₘ (Kernel.const α ν) = μ.prod ν := by
  ext s hs
  simp_rw [compProd_apply hs, prod_apply hs, Kernel.const_apply]

lemma compProd_add_left (μ ν : Measure α) [SFinite μ] [SFinite ν] (κ : Kernel α β) :
    (μ + ν) ⊗ₘ κ = μ ⊗ₘ κ + ν ⊗ₘ κ := by
  by_cases hκ : IsSFiniteKernel κ
  · simp_rw [Measure.compProd, Kernel.const_add, Kernel.compProd_add_left, Kernel.add_apply]
  · simp [hκ]

lemma compProd_add_right (μ : Measure α) (κ η : Kernel α β)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    μ ⊗ₘ (κ + η) = μ ⊗ₘ κ + μ ⊗ₘ η := by
  by_cases hμ : SFinite μ
  · simp_rw [Measure.compProd, Kernel.prodMkLeft_add, Kernel.compProd_add_right, Kernel.add_apply]
  · simp [hμ]

lemma compProd_sum_left {ι : Type*} [Countable ι] {μ : ι → Measure α} [∀ i, SFinite (μ i)] :
    (sum μ) ⊗ₘ κ = sum (fun i ↦ (μ i) ⊗ₘ κ) := by
  rw [compProd, ← Kernel.sum_const, Kernel.compProd_sum_left]
  rfl

lemma compProd_sum_right {ι : Type*} [Countable ι] {κ : ι → Kernel α β}
    [h : ∀ i, IsSFiniteKernel (κ i)] :
    μ ⊗ₘ (Kernel.sum κ) = sum (fun i ↦ μ ⊗ₘ (κ i)) := by
  rw [compProd, ← Kernel.sum_prodMkLeft, Kernel.compProd_sum_right]
  rfl

@[simp]
lemma fst_compProd (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsMarkovKernel κ] :
    (μ ⊗ₘ κ).fst = μ := by
  ext s
  rw [compProd, Measure.fst, ← Kernel.fst_apply, Kernel.fst_compProd, Kernel.const_apply]

lemma compProd_smul_left (a : ℝ≥0∞) [SFinite μ] [IsSFiniteKernel κ] :
    (a • μ) ⊗ₘ κ = a • (μ ⊗ₘ κ) := by
  ext s hs
  simp only [compProd_apply hs, lintegral_smul_measure, smul_apply, smul_eq_mul]

section Integral

lemma lintegral_compProd [SFinite μ] [IsSFiniteKernel κ]
    {f : α × β → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂(μ ⊗ₘ κ) = ∫⁻ a, ∫⁻ b, f (a, b) ∂(κ a) ∂μ := by
  rw [compProd, Kernel.lintegral_compProd _ _ _ hf]
  simp

lemma setLIntegral_compProd [SFinite μ] [IsSFiniteKernel κ]
    {f : α × β → ℝ≥0∞} (hf : Measurable f)
    {s : Set α} (hs : MeasurableSet s) {t : Set β} (ht : MeasurableSet t) :
    ∫⁻ x in s ×ˢ t, f x ∂(μ ⊗ₘ κ) = ∫⁻ a in s, ∫⁻ b in t, f (a, b) ∂(κ a) ∂μ := by
  rw [compProd, Kernel.setLIntegral_compProd _ _ _ hf hs ht]
  simp

end Integral

lemma dirac_compProd_apply [MeasurableSingletonClass α] {a : α} [IsSFiniteKernel κ]
    {s : Set (α × β)} (hs : MeasurableSet s) :
    (Measure.dirac a ⊗ₘ κ) s = κ a (Prod.mk a ⁻¹' s) := by
  rw [compProd_apply hs, lintegral_dirac]

lemma dirac_unit_compProd (κ : Kernel Unit β) [IsSFiniteKernel κ] :
    Measure.dirac () ⊗ₘ κ = (κ ()).map (Prod.mk ()) := by
  ext s hs; rw [dirac_compProd_apply hs, Measure.map_apply measurable_prodMk_left hs]

lemma dirac_unit_compProd_const (μ : Measure β) [SFinite μ] :
    Measure.dirac () ⊗ₘ Kernel.const Unit μ = μ.map (Prod.mk ()) := by
  rw [dirac_unit_compProd, Kernel.const_apply]

lemma snd_dirac_unit_compProd_const (μ : Measure β) [SFinite μ] :
    snd (Measure.dirac () ⊗ₘ Kernel.const Unit μ) = μ := by simp

instance : SFinite (μ ⊗ₘ κ) := by rw [compProd]; infer_instance

instance [IsFiniteMeasure μ] [IsFiniteKernel κ] : IsFiniteMeasure (μ ⊗ₘ κ) := by
  rw [compProd]; infer_instance

instance [IsProbabilityMeasure μ] [IsMarkovKernel κ] : IsProbabilityMeasure (μ ⊗ₘ κ) := by
  rw [compProd]; infer_instance

instance [IsZeroOrProbabilityMeasure μ] [IsZeroOrMarkovKernel κ] :
    IsZeroOrProbabilityMeasure (μ ⊗ₘ κ) := by
  rw [compProd]
  exact IsZeroOrMarkovKernel.isZeroOrProbabilityMeasure ()

section AbsolutelyContinuous

lemma AbsolutelyContinuous.compProd_left [SFinite ν] (hμν : μ ≪ ν) (κ : Kernel α β) :
    μ ⊗ₘ κ ≪ ν ⊗ₘ κ := by
  by_cases hκ : IsSFiniteKernel κ
  · have : SFinite μ := sFinite_of_absolutelyContinuous hμν
    refine Measure.AbsolutelyContinuous.mk fun s hs hs_zero ↦ ?_
    rw [Measure.compProd_apply hs, lintegral_eq_zero_iff (Kernel.measurable_kernel_prodMk_left hs)]
      at hs_zero ⊢
    exact hμν.ae_eq hs_zero
  · simp [compProd_of_not_isSFiniteKernel _ _ hκ]

lemma AbsolutelyContinuous.compProd_right [SFinite μ] [IsSFiniteKernel η]
    (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    μ ⊗ₘ κ ≪ μ ⊗ₘ η := by
  by_cases hκ : IsSFiniteKernel κ
  · refine Measure.AbsolutelyContinuous.mk fun s hs hs_zero ↦ ?_
    rw [Measure.compProd_apply hs, lintegral_eq_zero_iff (Kernel.measurable_kernel_prodMk_left hs)]
      at hs_zero ⊢
    filter_upwards [hs_zero, hκη] with a ha_zero ha_ac using ha_ac ha_zero
  · simp [compProd_of_not_isSFiniteKernel _ _ hκ]

lemma AbsolutelyContinuous.compProd [SFinite ν] [IsSFiniteKernel η]
    (hμν : μ ≪ ν) (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    μ ⊗ₘ κ ≪ ν ⊗ₘ η :=
  have : SFinite μ := sFinite_of_absolutelyContinuous hμν
  (Measure.AbsolutelyContinuous.compProd_right hκη).trans (hμν.compProd_left _)

lemma absolutelyContinuous_of_compProd [SFinite μ] [IsSFiniteKernel κ] [h_zero : ∀ a, NeZero (κ a)]
    (h : μ ⊗ₘ κ ≪ ν ⊗ₘ η) :
    μ ≪ ν := by
  refine Measure.AbsolutelyContinuous.mk (fun s hs hs0 ↦ ?_)
  have h1 : (ν ⊗ₘ η) (s ×ˢ univ) = 0 := by
    by_cases hν : SFinite ν
    swap; · simp [compProd_of_not_sfinite _ _ hν]
    by_cases hη : IsSFiniteKernel η
    swap; · simp [compProd_of_not_isSFiniteKernel _ _ hη]
    rw [Measure.compProd_apply_prod hs MeasurableSet.univ]
    exact setLIntegral_measure_zero _ _ hs0
  have h2 : (μ ⊗ₘ κ) (s ×ˢ univ) = 0 := h h1
  rw [Measure.compProd_apply_prod hs MeasurableSet.univ, lintegral_eq_zero_iff] at h2
  swap; · exact Kernel.measurable_coe _ MeasurableSet.univ
  by_contra hμs
  have : Filter.NeBot (ae (μ.restrict s)) := by simp [hμs]
  obtain ⟨a, ha⟩ : ∃ a, κ a univ = 0 := h2.exists
  refine absurd ha ?_
  simp only [Measure.measure_univ_eq_zero]
  exact (h_zero a).out

lemma absolutelyContinuous_compProd_left_iff [SFinite μ] [SFinite ν]
    [IsSFiniteKernel κ] [∀ a, NeZero (κ a)] :
    μ ⊗ₘ κ ≪ ν ⊗ₘ κ ↔ μ ≪ ν :=
  ⟨absolutelyContinuous_of_compProd, fun h ↦ h.compProd_left κ⟩

lemma AbsolutelyContinuous.compProd_of_compProd [SFinite ν] [IsSFiniteKernel η]
    (hμν : μ ≪ ν) (hκη : μ ⊗ₘ κ ≪ μ ⊗ₘ η) :
    μ ⊗ₘ κ ≪ ν ⊗ₘ η := by
  by_cases hμ : SFinite μ
  swap; · rw [compProd_of_not_sfinite _ _ hμ]; simp
  refine AbsolutelyContinuous.mk fun s hs hs_zero ↦ ?_
  suffices (μ ⊗ₘ η) s = 0 from hκη this
  rw [measure_zero_iff_ae_notMem, ae_compProd_iff hs.compl] at hs_zero ⊢
  exact hμν.ae_le hs_zero

end AbsolutelyContinuous

section MutuallySingular

lemma MutuallySingular.compProd_of_left (hμν : μ ⟂ₘ ν) (κ η : Kernel α β) :
    μ ⊗ₘ κ ⟂ₘ ν ⊗ₘ η := by
  by_cases hμ : SFinite μ
  swap; · rw [compProd_of_not_sfinite _ _ hμ]; simp
  by_cases hν : SFinite ν
  swap; · rw [compProd_of_not_sfinite _ _ hν]; simp
  by_cases hκ : IsSFiniteKernel κ
  swap; · rw [compProd_of_not_isSFiniteKernel _ _ hκ]; simp
  by_cases hη : IsSFiniteKernel η
  swap; · rw [compProd_of_not_isSFiniteKernel _ _ hη]; simp
  refine ⟨hμν.nullSet ×ˢ univ, hμν.measurableSet_nullSet.prod .univ, ?_⟩
  rw [compProd_apply_prod hμν.measurableSet_nullSet .univ, compl_prod_eq_union]
  simp only [MutuallySingular.restrict_nullSet, lintegral_zero_measure, compl_univ,
    prod_empty, union_empty, true_and]
  rw [compProd_apply_prod hμν.measurableSet_nullSet.compl .univ]
  simp

lemma mutuallySingular_of_mutuallySingular_compProd {ξ : Measure α}
    [SFinite μ] [SFinite ν] [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (h : μ ⊗ₘ κ ⟂ₘ ν ⊗ₘ η) (hμ : ξ ≪ μ) (hν : ξ ≪ ν) :
    ∀ᵐ x ∂ξ, κ x ⟂ₘ η x := by
  have hs : MeasurableSet h.nullSet := h.measurableSet_nullSet
  have hμ_zero : (μ ⊗ₘ κ) h.nullSet = 0 := h.measure_nullSet
  have hν_zero : (ν ⊗ₘ η) h.nullSetᶜ = 0 := h.measure_compl_nullSet
  rw [compProd_apply, lintegral_eq_zero_iff'] at hμ_zero hν_zero
  · filter_upwards [hμ hμ_zero, hν hν_zero] with x hxμ hxν
    exact ⟨Prod.mk x ⁻¹' h.nullSet, measurable_prodMk_left hs, ⟨hxμ, hxν⟩⟩
  · exact (Kernel.measurable_kernel_prodMk_left hs.compl).aemeasurable
  · exact (Kernel.measurable_kernel_prodMk_left hs).aemeasurable
  · exact hs.compl
  · exact hs

lemma mutuallySingular_compProd_left_iff [SFinite μ] [SigmaFinite ν]
    [IsSFiniteKernel κ] [hκ : ∀ x, NeZero (κ x)] :
    μ ⊗ₘ κ ⟂ₘ ν ⊗ₘ κ ↔ μ ⟂ₘ ν := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.compProd_of_left _ _⟩
  rw [← withDensity_rnDeriv_eq_zero]
  have hh := mutuallySingular_of_mutuallySingular_compProd h ?_ ?_
    (ξ := ν.withDensity (μ.rnDeriv ν))
  rotate_left
  · exact absolutelyContinuous_of_le (μ.withDensity_rnDeriv_le ν)
  · exact withDensity_absolutelyContinuous _ _
  simp_rw [MutuallySingular.self_iff, (hκ _).ne] at hh
  exact ae_eq_bot.mp (Filter.eventually_false_iff_eq_bot.mp hh)

lemma AbsolutelyContinuous.mutuallySingular_compProd_iff [SigmaFinite μ] [SigmaFinite ν]
    (hμν : μ ≪ ν) :
    μ ⊗ₘ κ ⟂ₘ ν ⊗ₘ η ↔ μ ⊗ₘ κ ⟂ₘ μ ⊗ₘ η := by
  conv_lhs => rw [ν.haveLebesgueDecomposition_add μ]
  rw [compProd_add_left, MutuallySingular.add_right_iff]
  simp only [(mutuallySingular_singularPart ν μ).symm.compProd_of_left κ η, true_and]
  refine ⟨fun h ↦ h.mono_ac .rfl ?_, fun h ↦ h.mono_ac .rfl ?_⟩
  · exact (absolutelyContinuous_withDensity_rnDeriv hμν).compProd_left _
  · exact (withDensity_absolutelyContinuous μ (ν.rnDeriv μ)).compProd_left _

lemma mutuallySingular_compProd_iff [SigmaFinite μ] [SigmaFinite ν] :
    μ ⊗ₘ κ ⟂ₘ ν ⊗ₘ η ↔ ∀ ξ, SFinite ξ → ξ ≪ μ → ξ ≪ ν → ξ ⊗ₘ κ ⟂ₘ ξ ⊗ₘ η := by
  conv_lhs => rw [μ.haveLebesgueDecomposition_add ν]
  rw [compProd_add_left, MutuallySingular.add_left_iff]
  simp only [(mutuallySingular_singularPart μ ν).compProd_of_left κ η, true_and]
  rw [(withDensity_absolutelyContinuous ν (μ.rnDeriv ν)).mutuallySingular_compProd_iff]
  refine ⟨fun h ξ hξ hξμ hξν ↦ ?_, fun h ↦ ?_⟩
  · exact h.mono_ac ((hξμ.withDensity_rnDeriv hξν).compProd_left _)
      ((hξμ.withDensity_rnDeriv hξν).compProd_left _)
  · refine h _ ?_ ?_ ?_
    · infer_instance
    · exact absolutelyContinuous_of_le (withDensity_rnDeriv_le _ _)
    · exact withDensity_absolutelyContinuous ν (μ.rnDeriv ν)

end MutuallySingular

lemma absolutelyContinuous_compProd_of_compProd [SigmaFinite μ] [SigmaFinite ν]
    (hκη : μ ⊗ₘ κ ≪ ν ⊗ₘ η) :
    μ ⊗ₘ κ ≪ μ ⊗ₘ η := by
  rw [ν.haveLebesgueDecomposition_add μ, compProd_add_left, add_comm] at hκη
  have h := absolutelyContinuous_of_add_of_mutuallySingular hκη
    ((mutuallySingular_singularPart _ _).symm.compProd_of_left _ _)
  refine h.trans (AbsolutelyContinuous.compProd_left ?_ _)
  exact withDensity_absolutelyContinuous _ _

lemma absolutelyContinuous_compProd_iff
    [SigmaFinite μ] [SigmaFinite ν] [IsSFiniteKernel κ] [IsSFiniteKernel η] [∀ x, NeZero (κ x)] :
    μ ⊗ₘ κ ≪ ν ⊗ₘ η ↔ μ ≪ ν ∧ μ ⊗ₘ κ ≪ μ ⊗ₘ η :=
  ⟨fun h ↦ ⟨absolutelyContinuous_of_compProd h, absolutelyContinuous_compProd_of_compProd h⟩,
    fun h ↦ h.1.compProd_of_compProd h.2⟩

end MeasureTheory.Measure
