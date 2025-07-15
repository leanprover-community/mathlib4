/-
Copyright (c) 2023 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rémy Degenne
-/
import Mathlib.Probability.Kernel.Disintegration.Integral

/-!
# Uniqueness of the conditional kernel

We prove that the conditional kernels `ProbabilityTheory.Kernel.condKernel` and
`MeasureTheory.Measure.condKernel` are almost everywhere unique.

## Main statements

* `ProbabilityTheory.eq_condKernel_of_kernel_eq_compProd`: a.e. uniqueness of
  `ProbabilityTheory.Kernel.condKernel`
* `ProbabilityTheory.eq_condKernel_of_measure_eq_compProd`: a.e. uniqueness of
  `MeasureTheory.Measure.condKernel`
* `ProbabilityTheory.Kernel.condKernel_apply_eq_condKernel`: the kernel `condKernel` is almost
  everywhere equal to the measure `condKernel`.
-/

open MeasureTheory Set Filter MeasurableSpace

open scoped ENNReal MeasureTheory Topology ProbabilityTheory

namespace ProbabilityTheory

variable {α β Ω : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]

section Measure

variable {ρ : Measure (α × Ω)} [IsFiniteMeasure ρ]

/-! ### Uniqueness of `Measure.condKernel`

The conditional kernel of a measure is unique almost everywhere. -/

/-- A s-finite kernel which satisfy the disintegration property of the given measure `ρ` is almost
everywhere equal to the disintegration kernel of `ρ` when evaluated on a measurable set.

This theorem in the case of finite kernels is weaker than `eq_condKernel_of_measure_eq_compProd`
which asserts that the kernels are equal almost everywhere and not just on a given measurable
set. -/
theorem eq_condKernel_of_measure_eq_compProd' (κ : Kernel α Ω) [IsSFiniteKernel κ]
    (hκ : ρ = ρ.fst ⊗ₘ κ) {s : Set Ω} (hs : MeasurableSet s) :
    ∀ᵐ x ∂ρ.fst, κ x s = ρ.condKernel x s := by
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
    (Kernel.measurable_coe κ hs) (Kernel.measurable_coe ρ.condKernel hs) (fun t ht _ ↦ ?_)
  conv_rhs => rw [Measure.setLIntegral_condKernel_eq_measure_prod ht hs, hκ]
  simp only [Measure.compProd_apply (ht.prod hs), ← lintegral_indicator ht]
  congr with x
  by_cases hx : x ∈ t <;> simp [hx]

/-- Auxiliary lemma for `eq_condKernel_of_measure_eq_compProd`.
Uniqueness of the disintegration kernel on ℝ. -/
lemma eq_condKernel_of_measure_eq_compProd_real {ρ : Measure (α × ℝ)} [IsFiniteMeasure ρ]
    (κ : Kernel α ℝ) [IsFiniteKernel κ] (hκ : ρ = ρ.fst ⊗ₘ κ) :
    ∀ᵐ x ∂ρ.fst, κ x = ρ.condKernel x := by
  have huniv : ∀ᵐ x ∂ρ.fst, κ x Set.univ = ρ.condKernel x Set.univ :=
    eq_condKernel_of_measure_eq_compProd' κ hκ MeasurableSet.univ
  suffices ∀ᵐ x ∂ρ.fst, ∀ ⦃t⦄, MeasurableSet t → κ x t = ρ.condKernel x t by
    filter_upwards [this] with x hx
    ext t ht; exact hx ht
  apply MeasurableSpace.ae_induction_on_inter Real.borel_eq_generateFrom_Iic_rat
    Real.isPiSystem_Iic_rat
  · simp
  · simp only [iUnion_singleton_eq_range, mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    exact ae_all_iff.2 fun q ↦ eq_condKernel_of_measure_eq_compProd' κ hκ measurableSet_Iic
  · filter_upwards [huniv] with x hxuniv t ht heq
    rw [measure_compl ht <| measure_ne_top _ _, heq, hxuniv, measure_compl ht <| measure_ne_top _ _]
  · refine ae_of_all _ (fun x f hdisj hf heq ↦ ?_)
    rw [measure_iUnion hdisj hf, measure_iUnion hdisj hf]
    exact tsum_congr heq

/-- A finite kernel which satisfies the disintegration property is almost everywhere equal to the
disintegration kernel. -/
theorem eq_condKernel_of_measure_eq_compProd (κ : Kernel α Ω) [IsFiniteKernel κ]
    (hκ : ρ = ρ.fst ⊗ₘ κ) :
    ∀ᵐ x ∂ρ.fst, κ x = ρ.condKernel x := by
  -- The idea is to transport the question to `ℝ` from `Ω` using `embeddingReal`
  -- and then construct a measure on `α × ℝ`
  let f := embeddingReal Ω
  have hf := measurableEmbedding_embeddingReal Ω
  set ρ' : Measure (α × ℝ) := ρ.map (Prod.map id f) with hρ'def
  have hρ' : ρ'.fst = ρ.fst := by
    ext s hs
    rw [hρ'def, Measure.fst_apply, Measure.fst_apply, Measure.map_apply]
    exacts [rfl, Measurable.prod measurable_fst <| hf.measurable.comp measurable_snd,
      measurable_fst hs, hs, hs]
  have hρ'' : ∀ᵐ x ∂ρ.fst, Kernel.map κ f x = ρ'.condKernel x := by
    rw [← hρ']
    refine eq_condKernel_of_measure_eq_compProd_real (Kernel.map κ f) ?_
    ext s hs
    conv_lhs => rw [hρ'def, hκ]
    rw [Measure.map_apply (measurable_id.prodMap hf.measurable) hs, hρ',
      Measure.compProd_apply hs, Measure.compProd_apply (measurable_id.prodMap hf.measurable hs)]
    congr with a
    rw [Kernel.map_apply' _ hf.measurable]
    exacts [rfl, measurable_prodMk_left hs]
  suffices ∀ᵐ x ∂ρ.fst, ∀ s, MeasurableSet s → ρ'.condKernel x s = ρ.condKernel x (f ⁻¹' s) by
    filter_upwards [hρ'', this] with x hx h
    rw [Kernel.map_apply _ hf.measurable] at hx
    ext s hs
    rw [← Set.preimage_image_eq s hf.injective,
      ← Measure.map_apply hf.measurable <| hf.measurableSet_image.2 hs, hx,
      h _ <| hf.measurableSet_image.2 hs]
  suffices ρ.map (Prod.map id f) = (ρ.fst ⊗ₘ (Kernel.map ρ.condKernel f)) by
    rw [← hρ'] at this
    have heq := eq_condKernel_of_measure_eq_compProd_real _ this
    rw [hρ'] at heq
    filter_upwards [heq] with x hx s hs
    rw [← hx, Kernel.map_apply _ hf.measurable, Measure.map_apply hf.measurable hs]
  ext s hs
  conv_lhs => rw [← ρ.disintegrate ρ.condKernel]
  rw [Measure.compProd_apply hs, Measure.map_apply (measurable_id.prodMap hf.measurable) hs,
    Measure.compProd_apply]
  · congr with a
    rw [Kernel.map_apply' _ hf.measurable]
    exacts [rfl, measurable_prodMk_left hs]
  · exact measurable_id.prodMap hf.measurable hs

lemma condKernel_compProd (μ : Measure α) [IsFiniteMeasure μ] (κ : Kernel α Ω) [IsMarkovKernel κ] :
    (μ ⊗ₘ κ).condKernel =ᵐ[μ] κ := by
  suffices κ =ᵐ[(μ ⊗ₘ κ).fst] (μ ⊗ₘ κ).condKernel by symm; rwa [Measure.fst_compProd] at this
  refine eq_condKernel_of_measure_eq_compProd _ ?_
  rw [Measure.fst_compProd]

end Measure

section KernelAndMeasure

lemma Kernel.apply_eq_measure_condKernel_of_compProd_eq
    {ρ : Kernel α (β × Ω)} [IsFiniteKernel ρ] {κ : Kernel (α × β) Ω} [IsFiniteKernel κ]
    (hκ : Kernel.fst ρ ⊗ₖ κ = ρ) (a : α) :
    (fun b ↦ κ (a, b)) =ᵐ[Kernel.fst ρ a] (ρ a).condKernel := by
  have : ρ a = (ρ a).fst ⊗ₘ Kernel.comap κ (fun b ↦ (a, b)) measurable_prodMk_left := by
    ext s hs
    conv_lhs => rw [← hκ]
    rw [Measure.compProd_apply hs, Kernel.compProd_apply hs]
    rfl
  have h := eq_condKernel_of_measure_eq_compProd _ this
  rw [Kernel.fst_apply]
  filter_upwards [h] with b hb
  rw [← hb, Kernel.comap_apply]

/-- For `fst κ a`-almost all `b`, the conditional kernel `Kernel.condKernel κ` applied to `(a, b)`
is equal to the conditional kernel of the measure `κ a` applied to `b`. -/
lemma Kernel.condKernel_apply_eq_condKernel [CountableOrCountablyGenerated α β]
    (κ : Kernel α (β × Ω)) [IsFiniteKernel κ] (a : α) :
    (fun b ↦ Kernel.condKernel κ (a, b)) =ᵐ[Kernel.fst κ a] (κ a).condKernel :=
  Kernel.apply_eq_measure_condKernel_of_compProd_eq (κ.disintegrate _) a

lemma condKernel_const [CountableOrCountablyGenerated α β] (ρ : Measure (β × Ω)) [IsFiniteMeasure ρ]
    (a : α) :
    (fun b ↦ Kernel.condKernel (Kernel.const α ρ) (a, b)) =ᵐ[ρ.fst] ρ.condKernel := by
  have h := Kernel.condKernel_apply_eq_condKernel (Kernel.const α ρ) a
  simp_rw [Kernel.fst_apply, Kernel.const_apply] at h
  filter_upwards [h] with b hb using hb

end KernelAndMeasure

section Kernel

/-! ### Uniqueness of `Kernel.condKernel`

The conditional kernel is unique almost everywhere. -/

/-- A finite kernel which satisfies the disintegration property is almost everywhere equal to the
disintegration kernel. -/
theorem eq_condKernel_of_kernel_eq_compProd [CountableOrCountablyGenerated α β]
    {ρ : Kernel α (β × Ω)} [IsFiniteKernel ρ] {κ : Kernel (α × β) Ω} [IsFiniteKernel κ]
    (hκ : Kernel.fst ρ ⊗ₖ κ = ρ) (a : α) :
    ∀ᵐ x ∂(Kernel.fst ρ a), κ (a, x) = Kernel.condKernel ρ (a, x) := by
  filter_upwards [Kernel.condKernel_apply_eq_condKernel ρ a,
    Kernel.apply_eq_measure_condKernel_of_compProd_eq hκ a] with a h1 h2
  rw [h1, h2]

end Kernel

end ProbabilityTheory
