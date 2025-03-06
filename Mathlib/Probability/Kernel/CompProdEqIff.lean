/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous

/-!
# Condition for two kernels to be equal almost everywhere

We prove that two kernels `κ` and `η` are `μ`-a.e. equal iff the composition-products `μ ⊗ₘ κ`
and `μ ⊗ₘ η` are equal.

## Main statements

* `compProd_withDensity`: `μ ⊗ₘ (κ.withDensity f) = (μ ⊗ₘ κ).withDensity (fun p ↦ f p.1 p.2)`
* `compProd_eq_iff`: `μ ⊗ₘ κ = μ ⊗ₘ η ↔ κ =ᵐ[μ] η`

-/

open ProbabilityTheory MeasureTheory

open scoped ENNReal

namespace MeasureTheory.Measure

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ : Measure α} {κ : Kernel α β}
  {f : α → β → ℝ≥0∞}

lemma compProd_withDensity_apply_prod [SFinite μ] [IsSFiniteKernel κ]
    [IsSFiniteKernel (κ.withDensity f)] (hf : Measurable (Function.uncurry f))
    {s : Set α} {t : Set β} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (μ ⊗ₘ (κ.withDensity f)) (s ×ˢ t)
      = ((μ ⊗ₘ κ).withDensity (fun p ↦ f p.1 p.2)) (s ×ˢ t) := by
  rw [Measure.compProd_apply (hs.prod ht), withDensity_apply _ (hs.prod ht),
    Measure.setLIntegral_compProd _ hs ht]
  swap; · exact hf
  have h_indicator a : ((κ.withDensity f) a) (Prod.mk a ⁻¹' s ×ˢ t)
      = s.indicator (fun a ↦ ∫⁻ b in t, f a b ∂(κ a)) a := by
    rw [Kernel.withDensity_apply _ hf, withDensity_apply]
    · by_cases has : a ∈ s <;> simp [has]
    · exact measurable_prod_mk_left (hs.prod ht)
  simp_rw [h_indicator]
  rw [lintegral_indicator hs]

/-- Auxiliary lemma for `compProd_withDensity`. -/
lemma compProd_withDensity_of_isFiniteMeasure [IsFiniteMeasure μ] [IsSFiniteKernel κ]
    [IsFiniteKernel (κ.withDensity f)] (hf : Measurable (Function.uncurry f)) :
    μ ⊗ₘ (κ.withDensity f) = (μ ⊗ₘ κ).withDensity (fun p ↦ f p.1 p.2) := by
  ext s hs
  refine MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod ?_ ?_ ?_ ?_ s hs
  · simp
  · rintro u ⟨s, hs, t, ht, rfl⟩
    simp only [Set.mem_setOf_eq] at hs ht ⊢
    exact compProd_withDensity_apply_prod hf hs ht
  · intro t ht h
    rw [measure_compl ht, measure_compl ht, h]
    rotate_left
    · suffices IsFiniteMeasure ((μ ⊗ₘ κ).withDensity (fun p ↦ f p.1 p.2)) from measure_ne_top _ _
      constructor
      rw [← Set.univ_prod_univ, ← compProd_withDensity_apply_prod hf .univ .univ]
      exact measure_lt_top _ _
    · exact measure_ne_top _ _
    congr 1
    rw [← Set.univ_prod_univ, compProd_withDensity_apply_prod hf .univ .univ]
  · intro f h_disj hf h
    simp_rw [measure_iUnion h_disj hf, h]

/-- A composition-product of a measure with a kernel defined with `withDensity` is equal to the
`withDensity` of the composition-product.

TODO: can we weaken the `IsFiniteKernel (κ.withDensity f)` hypothesis? -/
lemma compProd_withDensity [SFinite μ] [IsSFiniteKernel κ] [IsFiniteKernel (κ.withDensity f)]
    (hf : Measurable (Function.uncurry f)) :
    μ ⊗ₘ (κ.withDensity f) = (μ ⊗ₘ κ).withDensity (fun p ↦ f p.1 p.2) := by
  rw [← sum_sfiniteSeq μ, compProd_sum_left, compProd_sum_left, withDensity_sum]
  congr with n : 1
  exact compProd_withDensity_of_isFiniteMeasure hf

end MeasureTheory.Measure

namespace ProbabilityTheory.Kernel

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ : Measure α} {κ η : Kernel α β}
  [MeasurableSpace.CountableOrCountablyGenerated α β]

lemma ae_eq_of_compProd_eq [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (h : μ ⊗ₘ κ = μ ⊗ₘ η) :
    κ =ᵐ[μ] η := by
  have h_ac : ∀ᵐ a ∂μ, κ a ≪ η a := (Measure.absolutelyContinuous_of_eq h).kernel_of_compProd
  have hκ_eq : ∀ᵐ a ∂μ, κ a = η.withDensity (κ.rnDeriv η) a := by
    filter_upwards [h_ac] with a ha using (Kernel.withDensity_rnDeriv_eq ha).symm
  suffices ∀ᵐ a ∂μ, ∀ᵐ b ∂(η a), κ.rnDeriv η a b = 1 by
    filter_upwards [h_ac, this] with a h_ac h using (rnDeriv_eq_one_iff_eq h_ac).mp h
  refine Measure.ae_ae_of_ae_compProd (p := fun x ↦ κ.rnDeriv η x.1 x.2 = 1) ?_
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (by fun_prop) (by fun_prop) fun s hs _ ↦ ?_
  simp only [MeasureTheory.lintegral_const, MeasurableSet.univ, Measure.restrict_apply,
    Set.univ_inter, one_mul]
  calc ∫⁻ x in s, κ.rnDeriv η x.1 x.2 ∂μ ⊗ₘ η
  _ = (μ ⊗ₘ κ) s := by
    rw [Measure.compProd_congr hκ_eq, Measure.compProd_withDensity, withDensity_apply _ hs]
    fun_prop
  _ = (μ ⊗ₘ η) s := by rw [h]

/-- Two finite kernels `κ` and `η` are `μ`-a.e. equal iff the composition-products `μ ⊗ₘ κ`
and `μ ⊗ₘ η` are equal. -/
lemma compProd_eq_iff [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
    μ ⊗ₘ κ = μ ⊗ₘ η ↔ κ =ᵐ[μ] η :=
  ⟨Kernel.ae_eq_of_compProd_eq, Measure.compProd_congr⟩

end ProbabilityTheory.Kernel
