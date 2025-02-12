/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.RadonNikodym

open MeasureTheory Filter

open scoped ENNReal

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {κ η : Kernel α β}

lemma compProd_withDensity_apply_prod [IsFiniteMeasure μ] [IsFiniteKernel κ] {f : α → β → ℝ≥0∞}
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

lemma compProd_withDensity [IsFiniteMeasure μ] [IsFiniteKernel κ] {f : α → β → ℝ≥0∞}
    [IsFiniteKernel (κ.withDensity f)]
    (hf : Measurable (Function.uncurry f)) :
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

lemma compProd_congr_right [SFinite μ] [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (h : κ =ᵐ[μ] η) :
    μ ⊗ₘ κ = μ ⊗ₘ η := by
  ext s hs
  rw [Measure.compProd_apply hs, Measure.compProd_apply hs]
  refine lintegral_congr_ae ?_
  filter_upwards [h] with a ha
  rw [ha]

lemma Kernel.ae_eq_of_rnDeriv_eq_one [MeasurableSpace.CountableOrCountablyGenerated α β]
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (h_ac : ∀ᵐ a ∂μ, κ a ≪ η a) (h : ∀ᵐ a ∂μ, ∀ᵐ b ∂(η a), κ.rnDeriv η a b = 1) :
    κ =ᵐ[μ] η := by
  have hκ_eq : ∀ᵐ a ∂μ, κ a = η.withDensity (κ.rnDeriv η) a := by
    filter_upwards [h_ac] with a ha using (Kernel.withDensity_rnDeriv_eq ha).symm
  filter_upwards [hκ_eq, h] with a h_eq h_one
  rw [h_eq]
  ext s hs
  rw [Kernel.withDensity_apply, withDensity_apply _ hs, setLIntegral_congr_fun (g := 1) hs]
  · simp
  · filter_upwards [h_one] with b hb _ using hb
  · fun_prop

lemma mutuallySingular_compProd_right [MeasurableSpace.CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteKernel κ] [IsFiniteKernel η]
    (hκη : ∀ᵐ a ∂μ, κ a ⟂ₘ η a) :
    μ ⊗ₘ κ ⟂ₘ ν ⊗ₘ η := by
  by_cases hμ : SFinite μ
  swap; · rw [Measure.compProd_of_not_sfinite _ _ hμ]; simp
  by_cases hν : SFinite ν
  swap; · rw [Measure.compProd_of_not_sfinite _ _ hν]; simp
  let s := κ.mutuallySingularSet η
  have hs : MeasurableSet s := Kernel.measurableSet_mutuallySingularSet κ η
  symm
  refine ⟨s, hs, ?_⟩
  rw [Measure.compProd_apply hs, Measure.compProd_apply hs.compl]
  have h_eq a : Prod.mk a ⁻¹' s = Kernel.mutuallySingularSetSlice κ η a := rfl
  have h1 a : η a (Prod.mk a ⁻¹' s) = 0 := by rw [h_eq, Kernel.measure_mutuallySingularSetSlice]
  have h2 : ∀ᵐ a ∂μ, κ a (Prod.mk a ⁻¹' s)ᶜ = 0 := by
    filter_upwards [hκη] with a ha
    rw [h_eq, ← Kernel.withDensity_rnDeriv_eq_zero_iff_measure_eq_zero κ η a,
      Kernel.withDensity_rnDeriv_eq_zero_iff_mutuallySingular]
    exact ha
  simp [h1, lintegral_congr_ae h2]

lemma absolutelyContinuous_kernel_of_compProd [MeasurableSpace.CountableOrCountablyGenerated α β]
    [SFinite μ] [SFinite ν] [IsFiniteKernel κ] [IsFiniteKernel η]
    (h : μ ⊗ₘ κ ≪ ν ⊗ₘ η) :
    ∀ᵐ a ∂μ, κ a ≪ η a := by
  suffices ∀ᵐ a ∂μ, κ.singularPart η a = 0 by
    filter_upwards [this] with a ha
    rwa [Kernel.singularPart_eq_zero_iff_absolutelyContinuous] at ha
  rw [← κ.rnDeriv_add_singularPart η, Measure.compProd_add_right,
    Measure.AbsolutelyContinuous.add_left_iff] at h
  have : μ ⊗ₘ κ.singularPart η ⟂ₘ ν ⊗ₘ η :=
    mutuallySingular_compProd_right μ ν (.of_forall <| Kernel.mutuallySingular_singularPart _ _)
  have h_zero : μ ⊗ₘ κ.singularPart η = 0 :=
    Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular h.2 this
  simp_rw [← Measure.measure_univ_eq_zero]
  refine (lintegral_eq_zero_iff (Kernel.measurable_coe _ .univ)).mp ?_
  rw [← setLIntegral_univ, ← Measure.compProd_apply_prod .univ .univ, h_zero]
  simp

lemma Kernel.ae_eq_of_compProd_eq [MeasurableSpace.CountableOrCountablyGenerated α β]
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (h : μ ⊗ₘ κ = μ ⊗ₘ η) :
    κ =ᵐ[μ] η := by
  have h_ac : ∀ᵐ a ∂μ, κ a ≪ η a :=
    absolutelyContinuous_kernel_of_compProd (Measure.absolutelyContinuous_of_eq h)
  have hκ_eq : ∀ᵐ a ∂μ, κ a = η.withDensity (κ.rnDeriv η) a := by
    filter_upwards [h_ac] with a ha using (Kernel.withDensity_rnDeriv_eq ha).symm
  refine Kernel.ae_eq_of_rnDeriv_eq_one h_ac ?_
  refine Measure.ae_ae_of_ae_compProd (p := fun x ↦ κ.rnDeriv η x.1 x.2 = 1) ?_
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (by fun_prop) (by fun_prop) fun s hs _ ↦ ?_
  simp only [MeasureTheory.lintegral_const, MeasurableSet.univ, Measure.restrict_apply,
    Set.univ_inter, one_mul]
  calc ∫⁻ x in s, κ.rnDeriv η x.1 x.2 ∂μ ⊗ₘ η
  _ = (μ ⊗ₘ κ) s := by
    rw [compProd_congr_right hκ_eq, compProd_withDensity, withDensity_apply _ hs]
    fun_prop
  _ = (μ ⊗ₘ η) s := by rw [h]

/-- Two finite kernels `κ` and `η` are `μ`-a.e. equal iff the composition-products `μ ⊗ₘ κ`
and `μ ⊗ₘ η` are equal. -/
lemma Kernel.ae_eq_iff_compProd_eq [MeasurableSpace.CountableOrCountablyGenerated α β]
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
    κ =ᵐ[μ] η ↔ μ ⊗ₘ κ = μ ⊗ₘ η :=
  ⟨compProd_congr_right, Kernel.ae_eq_of_compProd_eq⟩

end ProbabilityTheory
