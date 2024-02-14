/-
Copyright (c) 2023 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathlib.Probability.Kernel.Disintegration

/-!
# Disintegration of measures on product spaces

Let `ρ` be a finite measure on `α × Ω`, where `Ω` is a standard Borel space. In mathlib terms, `Ω`
verifies `[Nonempty Ω] [MeasurableSpace Ω] [StandardBorelSpace Ω]`.
Then there exists a kernel `ρ.condKernel : kernel α Ω` such that for any measurable set
`s : Set (α × Ω)`, `ρ s = ∫⁻ a, ρ.condKernel a {x | (a, x) ∈ s} ∂ρ.fst`.

In terms of kernels, `ρ.condKernel` is such that for any measurable space `γ`, we
have a disintegration of the constant kernel from `γ` with value `ρ`:
`kernel.const γ ρ = (kernel.const γ ρ.fst) ⊗ₖ (kernel.prodMkLeft γ (condKernel ρ))`,
where `ρ.fst` is the marginal measure of `ρ` on `α`. In particular, `ρ = ρ.fst ⊗ₘ ρ.condKernel`.

In order to obtain a disintegration for any standard Borel space, we use that these spaces embed
measurably into `ℝ`: it then suffices to define a suitable kernel for `Ω = ℝ`. In the real case,
we define a conditional kernel by taking for each `a : α` the measure associated to the Stieltjes
function `condCDF ρ a` (the conditional cumulative distribution function).

## Main statements

* `ProbabilityTheory.eq_condKernel_of_measure_eq_compProd`: a.e. uniqueness of `Measure.condKernel`

-/


open MeasureTheory Set Filter

open scoped ENNReal MeasureTheory Topology ProbabilityTheory

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α}

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [Nonempty Ω] (ρ : Measure (α × Ω)) [IsFiniteMeasure ρ]

/-! ### Uniqueness

This section will prove that the conditional kernel is unique almost everywhere. -/

/-- A s-finite kernel which satisfy the disintegration property of the given measure `ρ` is almost
everywhere equal to the disintegration kernel of `ρ` when evaluated on a measurable set.

This theorem in the case of finite kernels is weaker than `eq_condKernel_of_measure_eq_compProd`
which asserts that the kernels are equal almost everywhere and not just on a given measurable
set. -/
theorem eq_condKernel_of_measure_eq_compProd' (κ : kernel α Ω) [IsSFiniteKernel κ]
    (hκ : ρ = ρ.fst ⊗ₘ κ) {s : Set Ω} (hs : MeasurableSet s) :
    ∀ᵐ x ∂ρ.fst, κ x s = ρ.condKernel x s := by
  refine' ae_eq_of_forall_set_lintegral_eq_of_sigmaFinite
    (kernel.measurable_coe κ hs) (kernel.measurable_coe ρ.condKernel hs) _
  intros t ht _
  conv_rhs => rw [set_lintegral_condKernel_eq_measure_prod _ ht hs, hκ]
  simp only [Measure.compProd_apply (ht.prod hs), Set.mem_prod, ← lintegral_indicator _ ht]
  congr; ext x
  by_cases hx : x ∈ t
  all_goals simp [hx]

-- This lemma establishes uniqueness of the disintegration kernel on ℝ
lemma eq_condKernel_of_measure_eq_compProd_real (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ]
    (κ : kernel α ℝ) [IsFiniteKernel κ] (hκ : ρ = ρ.fst ⊗ₘ κ) :
    ∀ᵐ x ∂ρ.fst, κ x = ρ.condKernel x := by
  have huniv : ∀ᵐ x ∂ρ.fst, κ x Set.univ = ρ.condKernel x Set.univ :=
    eq_condKernel_of_measure_eq_compProd' ρ κ hκ MeasurableSet.univ
  suffices : ∀ᵐ x ∂ρ.fst, ∀ ⦃t⦄, MeasurableSet t → κ x t = ρ.condKernel x t
  · filter_upwards [this] with x hx
    ext t ht; exact hx ht
  apply MeasurableSpace.ae_induction_on_inter Real.borel_eq_generateFrom_Iic_rat
    Real.isPiSystem_Iic_rat
  · simp only [OuterMeasure.empty', Filter.eventually_true]
  · simp only [iUnion_singleton_eq_range, mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    exact ae_all_iff.2 fun q => eq_condKernel_of_measure_eq_compProd' ρ κ hκ measurableSet_Iic
  · filter_upwards [huniv] with x hxuniv t ht heq
    rw [measure_compl ht <| measure_ne_top _ _, heq, hxuniv, measure_compl ht <| measure_ne_top _ _]
  · refine' ae_of_all _ (fun x f hdisj hf heq => _)
    rw [measure_iUnion hdisj hf, measure_iUnion hdisj hf]
    exact tsum_congr heq

/-- A finite kernel which satisfies the disintegration property is almost everywhere equal to the
disintegration kernel. -/
theorem eq_condKernel_of_measure_eq_compProd (κ : kernel α Ω) [IsFiniteKernel κ]
    (hκ : ρ = ρ.fst ⊗ₘ κ) :
    ∀ᵐ x ∂ρ.fst, κ x = ρ.condKernel x := by
-- The idea is to transporting the question to `ℝ` from `Ω` using `exists_measurableEmbedding_real`
-- and then constructing a measure on `α × ℝ` using the obtained measurable embedding
  obtain ⟨f, hf⟩ := exists_measurableEmbedding_real Ω
  set ρ' : Measure (α × ℝ) := ρ.map (Prod.map id f) with hρ'def
  have hρ' : ρ'.fst = ρ.fst
  · ext s hs
    rw [hρ'def, Measure.fst_apply, Measure.fst_apply, Measure.map_apply]
    exacts [rfl, Measurable.prod measurable_fst <| hf.measurable.comp measurable_snd,
      measurable_fst hs, hs, hs]
  have hρ'' : ∀ᵐ x ∂ρ'.fst, kernel.map κ f hf.measurable x = ρ'.condKernel x
  · refine' eq_condKernel_of_measure_eq_compProd_real ρ' (kernel.map κ f hf.measurable) _
    ext s hs
    simp only [Measure.map_apply (measurable_id.prod_map hf.measurable) hs]
    conv_lhs => congr; rw [hκ]
    rw [Measure.compProd_apply hs, Measure.compProd_apply
      (measurable_id.prod_map hf.measurable hs), (_ : (ρ.map (Prod.map id f)).fst = ρ.fst)]
    · congr
      ext x
      simp only [Set.mem_preimage, Prod_map, id_eq, kernel.prodMkLeft_apply, kernel.map_apply]
      rw [Measure.map_apply hf.measurable]
      · rfl
      · exact measurable_prod_mk_left hs
    · rw [Measure.fst_map_prod_mk]
      · simp only [Prod_map, id_eq]; rfl
      · exact (hf.measurable.comp measurable_snd)
  rw [hρ'] at hρ''
  suffices : ∀ᵐ x ∂ρ.fst, ∀ s, MeasurableSet s →
    ((ρ.map (Prod.map id f)).condKernel x) s = (ρ.condKernel x) (f ⁻¹' s)
  · filter_upwards [hρ'', this] with x hx h
    rw [kernel.map_apply] at hx
    ext s hs
    rw [← Set.preimage_image_eq s hf.injective,
      ← Measure.map_apply hf.measurable <| hf.measurableSet_image.2 hs, hx,
      h _ <| hf.measurableSet_image.2 hs]
  have hprod : (ρ.map (Prod.map id f)).fst = ρ.fst
  · ext s hs
    rw [Measure.fst_apply hs,
      Measure.map_apply (measurable_id.prod_map hf.measurable) (measurable_fst hs),
      ← Set.preimage_comp, Measure.fst_apply hs]
    rfl
  suffices : ρ.map (Prod.map id f) =
    ((ρ.map (Prod.map id f)).fst ⊗ₘ (kernel.map (Measure.condKernel ρ) f hf.measurable))
  · have heq := eq_condKernel_of_measure_eq_compProd_real _ _ this
    rw [hprod] at heq
    filter_upwards [heq] with x hx s hs
    rw [← hx, kernel.map_apply, Measure.map_apply hf.measurable hs]
  ext s hs
  simp only [hprod, Measure.compProd_apply hs, kernel.map_apply _ hf.measurable]
  rw [Measure.map_apply (measurable_id.prod_map hf.measurable) hs, ← lintegral_condKernel_mem]
  · simp only [mem_preimage, Prod_map, id_eq]
    congr with a
    rw [Measure.map_apply hf.measurable (measurable_prod_mk_left hs)]
    rfl
  · exact measurable_id.prod_map hf.measurable hs

end ProbabilityTheory
