/-
Copyright (c) 2023 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rémy Degenne
-/
import Mathlib.Probability.Kernel.Disintegration.Integral

/-!
# Disintegration of measures on product spaces

## Main statements

* `ProbabilityTheory.eq_condKernel_of_measure_eq_compProd`: a.e. uniqueness of `Measure.condKernel`

-/


open MeasureTheory Set Filter

open scoped ENNReal MeasureTheory Topology ProbabilityTheory

namespace ProbabilityTheory

variable {α β Ω : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]

section Kernel

variable [CountableOrCountablyGenerated α β] {ρ : kernel α (β × Ω)} [IsFiniteKernel ρ]

/-! ### Uniqueness

This section will prove that the conditional kernel is unique almost everywhere. -/

/-- A s-finite kernel which satisfy the disintegration property of the given measure `ρ` is almost
everywhere equal to the disintegration kernel of `ρ` when evaluated on a measurable set.

This theorem in the case of finite kernels is weaker than `eq_condKernel_of_measure_eq_compProd`
which asserts that the kernels are equal almost everywhere and not just on a given measurable
set. -/
theorem eq_condKernel_of_measure_eq_compProd' {κ : kernel (α × β) Ω} [IsSFiniteKernel κ]
    (hκ : ρ = kernel.fst ρ ⊗ₖ κ) {s : Set Ω} (hs : MeasurableSet s) (a : α) :
    ∀ᵐ x ∂(kernel.fst ρ a), κ (a, x) s = kernel.condKernel ρ (a, x) s := by
  refine ae_eq_of_forall_set_lintegral_eq_of_sigmaFinite ?_ ?_ ?_
  · exact (kernel.measurable_coe κ hs).comp measurable_prod_mk_left
  · exact (kernel.measurable_coe _ hs).comp measurable_prod_mk_left
  intros t ht _
  conv_rhs => rw [set_lintegral_condKernel_eq_measure_prod _ ht hs, hκ]
  simp only [kernel.compProd_apply _ _ _ (ht.prod hs), Set.mem_prod, ← lintegral_indicator _ ht]
  congr with x
  by_cases hx : x ∈ t
  all_goals simp [hx]

-- This lemma establishes uniqueness of the disintegration kernel on ℝ
lemma eq_condKernel_of_measure_eq_compProd_real {ρ : kernel α (β × ℝ)} [IsFiniteKernel ρ]
    {κ : kernel (α × β) ℝ} [IsFiniteKernel κ] (hκ : ρ = kernel.fst ρ ⊗ₖ κ) (a : α) :
    ∀ᵐ x ∂(kernel.fst ρ a), κ (a, x) = kernel.condKernel ρ (a, x) := by
  have huniv : ∀ᵐ x ∂(kernel.fst ρ a), κ (a, x) Set.univ = kernel.condKernel ρ (a, x) Set.univ :=
    eq_condKernel_of_measure_eq_compProd' hκ MeasurableSet.univ a
  suffices ∀ᵐ x ∂(kernel.fst ρ a),
      ∀ ⦃t⦄, MeasurableSet t → κ (a, x) t = kernel.condKernel ρ (a, x) t by
    filter_upwards [this] with x hx
    ext t ht; exact hx ht
  apply MeasurableSpace.ae_induction_on_inter Real.borel_eq_generateFrom_Iic_rat
    Real.isPiSystem_Iic_rat
  · simp only [OuterMeasure.empty', Filter.eventually_true]
  · simp only [iUnion_singleton_eq_range, mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    exact ae_all_iff.2 fun q => eq_condKernel_of_measure_eq_compProd' hκ measurableSet_Iic a
  · filter_upwards [huniv] with x hxuniv t ht heq
    rw [measure_compl ht <| measure_ne_top _ _, heq, hxuniv, measure_compl ht <| measure_ne_top _ _]
  · refine ae_of_all _ (fun x f hdisj hf heq ↦ ?_)
    rw [measure_iUnion hdisj hf, measure_iUnion hdisj hf]
    exact tsum_congr heq

/-- A finite kernel which satisfies the disintegration property is almost everywhere equal to the
disintegration kernel. -/
theorem eq_condKernel_of_kernel_eq_compProd (κ : kernel (α × β) Ω) [IsFiniteKernel κ]
    (hκ : ρ = kernel.fst ρ ⊗ₖ κ) (a : α) :
    ∀ᵐ x ∂(kernel.fst ρ a), κ (a, x) = kernel.condKernel ρ (a, x) := by
-- The idea is to transporting the question to `ℝ` from `Ω` using `exists_embeddingReal`
-- and then constructing a measure on `α × ℝ` using the obtained measurable embedding
  let f := embeddingReal Ω
  let hf := measurableEmbedding_embeddingReal Ω
  set ρ' : kernel α (β × ℝ) := kernel.map ρ (Prod.map id f)
    (measurable_id.prod_map hf.measurable) with hρ'def
  have hρ' : kernel.fst ρ' = kernel.fst ρ := by
    ext a s hs
    rw [hρ'def, kernel.fst_apply' _ _ hs, kernel.fst_apply' _ _ hs, kernel.map_apply']
    exacts [rfl, measurable_fst hs]
  have hρ'' : ∀ᵐ x ∂(kernel.fst ρ a),
      kernel.map κ f hf.measurable (a, x) = kernel.condKernel ρ' (a, x) := by
    rw [← hρ']
    refine eq_condKernel_of_measure_eq_compProd_real ?_ a
    ext a s hs
    conv_lhs => rw [hρ'def, hκ]
    rw [kernel.map_apply' _ _ _ hs, kernel.compProd_apply _ _ _ hs, kernel.compProd_apply]
    swap; · exact measurable_id.prod_map hf.measurable hs
    congr with b
    · congr with a t ht
      rw [kernel.fst_apply' _ _ ht, kernel.fst_apply' _ _ ht, kernel.map_apply']
      exacts [rfl, measurable_fst ht]
    · rw [kernel.map_apply']
      exacts [rfl, measurable_prod_mk_left hs]
  suffices ∀ᵐ x ∂(kernel.fst ρ a), ∀ s, MeasurableSet s →
      kernel.condKernel ρ' (a, x) s = kernel.condKernel ρ (a, x) (f ⁻¹' s) by
    filter_upwards [hρ'', this] with x hx h
    rw [kernel.map_apply] at hx
    ext s hs
    rw [← Set.preimage_image_eq s hf.injective,
      ← Measure.map_apply hf.measurable <| hf.measurableSet_image.2 hs, hx,
      h _ <| hf.measurableSet_image.2 hs]
  suffices ρ' = (kernel.fst ρ ⊗ₖ (kernel.map (kernel.condKernel ρ) f hf.measurable)) by
    rw [← hρ'] at this
    have heq := eq_condKernel_of_measure_eq_compProd_real this a
    rw [hρ'] at heq
    filter_upwards [heq] with x hx s hs
    rw [← hx, kernel.map_apply, Measure.map_apply hf.measurable hs]
  ext a s hs
  rw [hρ'def, kernel.map_apply' _ _ _ hs, kernel.compProd_apply _ _ _ hs,
    ← lintegral_condKernel_mem]
  swap; · exact measurable_id.prod_map hf.measurable hs
  congr with b
  rw [kernel.map_apply']
  exacts [rfl, measurable_prod_mk_left hs]

end Kernel

section Measure

variable {ρ : Measure (α × Ω)} [IsFiniteMeasure ρ]

/-! ### Uniqueness

This section will prove that the conditional kernel is unique almost everywhere. -/

/-- A s-finite kernel which satisfy the disintegration property of the given measure `ρ` is almost
everywhere equal to the disintegration kernel of `ρ` when evaluated on a measurable set.

This theorem in the case of finite kernels is weaker than `eq_condKernel_of_measure_eq_compProd`
which asserts that the kernels are equal almost everywhere and not just on a given measurable
set. -/
theorem Measure.eq_condKernel_of_measure_eq_compProd' (κ : kernel α Ω) [IsSFiniteKernel κ]
    (hκ : ρ = ρ.fst ⊗ₘ κ) {s : Set Ω} (hs : MeasurableSet s) :
    ∀ᵐ x ∂ρ.fst, κ x s = ρ.condKernel x s := by
  refine ae_eq_of_forall_set_lintegral_eq_of_sigmaFinite
    (kernel.measurable_coe κ hs) (kernel.measurable_coe ρ.condKernel hs) (fun t ht _ ↦ ?_)
  conv_rhs => rw [Measure.set_lintegral_condKernel_eq_measure_prod ht hs, hκ]
  simp only [Measure.compProd_apply (ht.prod hs), Set.mem_prod, ← lintegral_indicator _ ht]
  congr with x
  by_cases hx : x ∈ t
  all_goals simp [hx]

-- This lemma establishes uniqueness of the disintegration kernel on ℝ
lemma Measure.eq_condKernel_of_measure_eq_compProd_real {ρ : Measure (α × ℝ)} [IsFiniteMeasure ρ]
    (κ : kernel α ℝ) [IsFiniteKernel κ] (hκ : ρ = ρ.fst ⊗ₘ κ) :
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
theorem Measure.eq_condKernel_of_measure_eq_compProd (κ : kernel α Ω) [IsFiniteKernel κ]
    (hκ : ρ = ρ.fst ⊗ₘ κ) :
    ∀ᵐ x ∂ρ.fst, κ x = ρ.condKernel x := by
  -- The idea is to transporting the question to `ℝ` from `Ω` using
  -- `exists_embeddingReal` and then constructing a measure on `α × ℝ` using
  -- the obtained measurable embedding
  let f := embeddingReal Ω
  let hf := measurableEmbedding_embeddingReal Ω
  set ρ' : Measure (α × ℝ) := ρ.map (Prod.map id f) with hρ'def
  have hρ' : ρ'.fst = ρ.fst := by
    ext s hs
    rw [hρ'def, Measure.fst_apply, Measure.fst_apply, Measure.map_apply]
    exacts [rfl, Measurable.prod measurable_fst <| hf.measurable.comp measurable_snd,
      measurable_fst hs, hs, hs]
  have hρ'' : ∀ᵐ x ∂ρ.fst, kernel.map κ f hf.measurable x = ρ'.condKernel x := by
    rw [← hρ']
    refine eq_condKernel_of_measure_eq_compProd_real (kernel.map κ f hf.measurable) ?_
    ext s hs
    conv_lhs => rw [hρ'def, hκ]
    rw [Measure.map_apply (measurable_id.prod_map hf.measurable) hs, hρ',
      Measure.compProd_apply hs, Measure.compProd_apply (measurable_id.prod_map hf.measurable hs)]
    congr with a
    rw [kernel.map_apply']
    exacts [rfl, measurable_prod_mk_left hs]
  suffices ∀ᵐ x ∂ρ.fst, ∀ s, MeasurableSet s → ρ'.condKernel x s = ρ.condKernel x (f ⁻¹' s) by
    filter_upwards [hρ'', this] with x hx h
    rw [kernel.map_apply] at hx
    ext s hs
    rw [← Set.preimage_image_eq s hf.injective,
      ← Measure.map_apply hf.measurable <| hf.measurableSet_image.2 hs, hx,
      h _ <| hf.measurableSet_image.2 hs]
  suffices ρ.map (Prod.map id f) = (ρ.fst ⊗ₘ (kernel.map ρ.condKernel f hf.measurable)) by
    rw [← hρ'] at this
    have heq := eq_condKernel_of_measure_eq_compProd_real _ this
    rw [hρ'] at heq
    filter_upwards [heq] with x hx s hs
    rw [← hx, kernel.map_apply, Measure.map_apply hf.measurable hs]
  ext s hs
  conv_lhs => rw [← ρ.compProd_fst_condKernel]
  rw [Measure.compProd_apply hs, Measure.map_apply (measurable_id.prod_map hf.measurable) hs,
    Measure.compProd_apply]
  · congr with a
    rw [kernel.map_apply']
    exacts [rfl, measurable_prod_mk_left hs]
  · exact measurable_id.prod_map hf.measurable hs

end Measure

section KernelAndMeasure

lemma kernel.condKernel_apply_eq_condKernel [CountableOrCountablyGenerated α β]
    (κ : kernel α (β × Ω)) [IsFiniteKernel κ] (a : α) :
    ∀ᵐ b ∂(kernel.fst κ a), kernel.condKernel κ (a, b) = (κ a).condKernel b := by
  have : κ a = (κ a).fst
      ⊗ₘ kernel.comap (kernel.condKernel κ) (fun b ↦ (a, b)) measurable_prod_mk_left := by
    ext s hs
    conv_lhs => rw [← compProd_fst_condKernel κ]
    rw [Measure.compProd_apply hs, kernel.compProd_apply _ _ _ hs]
    rfl
  have h := Measure.eq_condKernel_of_measure_eq_compProd _ this
  rw [kernel.fst_apply]
  filter_upwards [h] with b hb
  rw [← hb, kernel.comap_apply]

lemma condKernel_const [CountableOrCountablyGenerated α β] (ρ : Measure (β × Ω)) [IsFiniteMeasure ρ]
    (a : α) :
    ∀ᵐ b ∂ρ.fst, kernel.condKernel (kernel.const α ρ) (a, b) = ρ.condKernel b := by
  have h := kernel.condKernel_apply_eq_condKernel (kernel.const α ρ) a
  simp_rw [kernel.fst_apply, kernel.const_apply] at h
  filter_upwards [h] with b hb using hb

end KernelAndMeasure

end ProbabilityTheory
