/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Kexing Ying
-/
import Mathlib.Probability.Kernel.CondCdf
import Mathlib.Probability.Kernel.Disintegration.KernelCDFBorel

/-!
# Disintegration of kernels and measures

-/

open MeasureTheory Set Filter

open scoped ENNReal MeasureTheory Topology ProbabilityTheory

namespace ProbabilityTheory

variable {α β Ω Ω': Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
  [MeasurableSpace Ω'] [StandardBorelSpace Ω'] [Nonempty Ω']

section BorelSnd

noncomputable
def condKernelBorelSnd (κ : kernel α (β × Ω')) [IsMarkovKernel κ]
    {f : α × β → StieltjesFunction}
    (hf : IsKernelCDF f
      (kernel.map κ (Prod.map (id : β → β) (measurableEmbedding_real Ω'))
        (measurable_id.prod_map (measurableEmbedding_measurableEmbedding_real Ω').measurable))
      (kernel.fst (kernel.map κ (Prod.map (id : β → β) (measurableEmbedding_real Ω'))
        (measurable_id.prod_map (measurableEmbedding_measurableEmbedding_real Ω').measurable)))) :
    kernel (α × β) Ω' :=
  let e := measurableEmbedding_real Ω'
  let he := measurableEmbedding_measurableEmbedding_real Ω'
  let x₀ := (range_nonempty e).choose
  kernel.comapRight
    (kernel.piecewise (measurableSet_eq_one hf he.measurableSet_range)
      (cdfKernel f hf) (kernel.deterministic (fun _ ↦ x₀) measurable_const))
    he

instance instIsMarkovKernel_condKernelBorelSnd (κ : kernel α (β × Ω')) [IsMarkovKernel κ]
    {f : α × β → StieltjesFunction}
    (hf : IsKernelCDF f
      (kernel.map κ (Prod.map (id : β → β) (measurableEmbedding_real Ω'))
        (measurable_id.prod_map (measurableEmbedding_measurableEmbedding_real Ω').measurable))
      (kernel.fst (kernel.map κ (Prod.map (id : β → β) (measurableEmbedding_real Ω'))
        (measurable_id.prod_map (measurableEmbedding_measurableEmbedding_real Ω').measurable)))) :
    IsMarkovKernel (condKernelBorelSnd κ hf) := by
  rw [condKernelBorelSnd]
  refine kernel.IsMarkovKernel.comapRight _ _ fun a ↦ ?_
  rw [kernel.piecewise_apply']
  split_ifs with h_mem
  · exact h_mem
  · classical
    rw [kernel.deterministic_apply' _ _
        (measurableEmbedding_measurableEmbedding_real Ω').measurableSet_range,
      Set.indicator_apply, if_pos]
    exact (range_nonempty (measurableEmbedding_real Ω')).choose_spec

lemma compProd_fst_condKernelBorelSnd (κ : kernel α (β × Ω')) [IsMarkovKernel κ]
    {f : α × β → StieltjesFunction}
    (hf : IsKernelCDF f
      (kernel.map κ (Prod.map (id : β → β) (measurableEmbedding_real Ω'))
        (measurable_id.prod_map (measurableEmbedding_measurableEmbedding_real Ω').measurable))
      (kernel.fst (kernel.map κ (Prod.map (id : β → β) (measurableEmbedding_real Ω'))
        (measurable_id.prod_map (measurableEmbedding_measurableEmbedding_real Ω').measurable)))) :
    kernel.fst κ ⊗ₖ condKernelBorelSnd κ hf = κ := by
  let e := measurableEmbedding_real Ω'
  let he := measurableEmbedding_measurableEmbedding_real Ω'
  let κ' := kernel.map κ (Prod.map (id : β → β) e) (measurable_id.prod_map he.measurable)
  have h_prod_embed : MeasurableEmbedding (Prod.map (id : β → β) e) :=
    MeasurableEmbedding.id.prod_mk he
  have h_fst : kernel.fst κ' = kernel.fst κ := by
    ext a u hu
    unfold_let κ'
    rw [kernel.fst_apply' _ _ hu, kernel.fst_apply' _ _ hu,
      kernel.map_apply' κ h_prod_embed.measurable]
    · rfl
    · exact measurable_fst hu
  have : κ = kernel.comapRight κ' h_prod_embed := by
    ext c t ht : 2
    unfold_let κ'
    rw [kernel.comapRight_apply' _ _ _ ht, kernel.map_apply' κ h_prod_embed.measurable
      _ (h_prod_embed.measurableSet_image.mpr ht)]
    congr with x : 1
    rw [← @Prod.mk.eta _ _ x]
    simp only [id.def, mem_preimage, Prod.map_mk, mem_image, Prod.mk.inj_iff, Prod.exists]
    refine' ⟨fun h => ⟨x.1, x.2, h, rfl, rfl⟩, _⟩
    rintro ⟨a, b, h_mem, rfl, he_eq⟩
    rwa [he.injective he_eq] at h_mem
  conv_rhs => rw [this]
  unfold_let κ'
  conv_rhs => rw [kernel.eq_compProd_cdfKernel hf]
  change kernel.fst κ ⊗ₖ condKernelBorelSnd κ hf
    = kernel.comapRight (kernel.fst κ' ⊗ₖ cdfKernel f hf) h_prod_embed
  ext c t ht : 2
  rw [kernel.comapRight_apply' _ _ _ ht,
    kernel.compProd_apply _ _ _ (h_prod_embed.measurableSet_image.mpr ht)]
  simp_rw [h_fst, kernel.compProd_apply _ _ _ ht]
  refine lintegral_congr_ae ?_
  let ρ_set := {p : α × β | cdfKernel f hf p (range e) = 1}
  have h_ae : ∀ a, ∀ᵐ t ∂(kernel.fst κ a), (a, t) ∈ ρ_set := by
    intro a
    rw [← h_fst]
    refine ae_cdfKernel_eq_one hf a he.measurableSet_range ?_
    simp only [mem_compl_iff, mem_range, not_exists]
    rw [kernel.map_apply']
    · have h_empty : {a : β × Ω' | ∀ (x : Ω'), ¬e x = e a.2} = ∅ := by
        ext x
        simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_forall, not_not,
          exists_apply_eq_apply]
      simp [h_empty]
    · have : {x : β × ℝ | ∀ (y : Ω'), ¬ e y = x.2} = univ ×ˢ (range e)ᶜ := by
        ext x
        simp only [mem_setOf_eq, mem_prod, mem_univ, mem_compl_iff, mem_range, not_exists, true_and]
      rw [this]
      exact MeasurableSet.univ.prod he.measurableSet_range.compl
  filter_upwards [h_ae c] with a ha
  rw [condKernelBorelSnd, kernel.comapRight_apply']
  swap; · exact measurable_prod_mk_left ht
  have h1 : {c : ℝ | (a, c) ∈ Prod.map id e '' t} = e '' {c : Ω' | (a, c) ∈ t} := by
    ext1 x
    simp only [Prod_map, id.def, mem_image, Prod.mk.inj_iff, Prod.exists, mem_setOf_eq]
    constructor
    · rintro ⟨a', b, h_mem, rfl, hf_eq⟩
      exact ⟨b, h_mem, hf_eq⟩
    · rintro ⟨b, h_mem, hf_eq⟩
      exact ⟨a, b, h_mem, rfl, hf_eq⟩
  rw [h1, kernel.piecewise_apply, if_pos ha]
  rfl

end BorelSnd

section StandardBorel

noncomputable
def kernel.condKernelReal (κ : kernel α (ℝ × ℝ)) [IsMarkovKernel κ] : kernel (α × ℝ) ℝ :=
  cdfKernel _ (isKernelCDF_mLimsupCDF κ)

instance (κ : kernel α (ℝ × ℝ)) [IsMarkovKernel κ] : IsMarkovKernel (kernel.condKernelReal κ) := by
  unfold kernel.condKernelReal; infer_instance

lemma kernel.eq_compProd_condKernelReal (κ : kernel α (ℝ × ℝ)) [IsMarkovKernel κ] :
    κ = kernel.fst κ ⊗ₖ kernel.condKernelReal κ :=
  kernel.eq_compProd_cdfKernel (isKernelCDF_mLimsupCDF κ)

noncomputable
def condKernelBorelAux (κ : kernel α (ℝ × Ω')) [IsMarkovKernel κ] : kernel (α × ℝ) Ω' :=
  let f := measurableEmbedding_real Ω'
  let hf := measurableEmbedding_measurableEmbedding_real Ω'
  let κ' := kernel.map κ (Prod.map (id : ℝ → ℝ) f) (measurable_id.prod_map hf.measurable)
  condKernelBorelSnd κ (isKernelCDF_mLimsupCDF κ')

instance instIsMarkovKernel_condKernelBorelAux (κ : kernel α (ℝ × Ω')) [IsMarkovKernel κ] :
    IsMarkovKernel (condKernelBorelAux κ) := by
  rw [condKernelBorelAux]
  infer_instance

lemma compProd_fst_condKernelBorelAux (κ : kernel α (ℝ × Ω')) [IsMarkovKernel κ] :
    kernel.fst κ ⊗ₖ condKernelBorelAux κ = κ := by
  rw [condKernelBorelAux, compProd_fst_condKernelBorelSnd]

noncomputable
def condKernelBorel (κ : kernel α (Ω × Ω')) [IsMarkovKernel κ] : kernel (α × Ω) Ω' :=
  let f := measurableEmbedding_real Ω
  let hf := measurableEmbedding_measurableEmbedding_real Ω
  let κ' := kernel.map κ (Prod.map f (id : Ω' → Ω')) (hf.measurable.prod_map measurable_id)
  kernel.comap (condKernelBorelAux κ') (Prod.map (id : α → α) f)
    (measurable_id.prod_map hf.measurable)

instance instIsMarkovKernel_condKernelBorel (κ : kernel α (Ω × Ω')) [IsMarkovKernel κ] :
    IsMarkovKernel (condKernelBorel κ) := by rw [condKernelBorel]; infer_instance

lemma compProd_fst_condKernel (κ : kernel α (Ω × Ω')) [IsMarkovKernel κ] :
    kernel.fst κ ⊗ₖ condKernelBorel κ = κ := by
  let f := measurableEmbedding_real Ω
  let hf := measurableEmbedding_measurableEmbedding_real Ω
  let κ' : kernel α (ℝ × Ω') :=
    kernel.map κ (Prod.map f (id : Ω' → Ω')) (hf.measurable.prod_map measurable_id)
  have h_condKernel : condKernelBorel κ
    = kernel.comap (condKernelBorelAux κ') (Prod.map (id : α → α) f)
      (measurable_id.prod_map hf.measurable) := rfl
  have h_compProd := compProd_fst_condKernelBorelAux κ'
  have h_prod_embed : MeasurableEmbedding (Prod.map f (id : Ω' → Ω')) :=
    hf.prod_mk MeasurableEmbedding.id
  have : κ = kernel.comapRight κ' h_prod_embed := by
    ext c t ht : 2
    unfold_let κ'
    rw [kernel.comapRight_apply' _ _ _ ht, kernel.map_apply' κ h_prod_embed.measurable
      _ (h_prod_embed.measurableSet_image.mpr ht)]
    congr with x : 1
    rw [← @Prod.mk.eta _ _ x]
    simp only [Prod.mk.eta, Prod_map, id_eq, mem_preimage, mem_image, Prod.mk.injEq, Prod.exists,
      exists_eq_right_right]
    refine ⟨fun h ↦ ⟨x.1, h, rfl⟩, ?_⟩
    rintro ⟨ω, h_mem, h⟩
    rwa [hf.injective h] at h_mem
  have h_fst : kernel.fst κ' = kernel.map (kernel.fst κ) f hf.measurable := by
    ext a s hs
    unfold_let κ'
    rw [kernel.map_apply' _ _ _ hs, kernel.fst_apply', kernel.fst_apply', kernel.map_apply']
    · congr
    · exact measurable_fst hs
    · exact hf.measurable hs
    · exact hs
  conv_rhs => rw [this, ← h_compProd]
  ext a s hs
  rw [h_condKernel, h_fst]
  rw [kernel.comapRight_apply' _ _ _ hs, kernel.compProd_apply _ _ _ hs, kernel.compProd_apply]
  swap; · exact h_prod_embed.measurableSet_image.mpr hs
  rw [kernel.map_apply, lintegral_map]
  congr with ω
  rw [kernel.comap_apply']
  · congr with ω'
    simp only [mem_setOf_eq, Prod_map, id_eq, mem_image, Prod.mk.injEq, Prod.exists,
      exists_eq_right_right]
    refine ⟨fun h ↦ ⟨ω, h, rfl⟩, ?_⟩
    rintro ⟨a, h_mem, h⟩
    rwa [hf.injective h] at h_mem
  · exact kernel.measurable_kernel_prod_mk_left' (h_prod_embed.measurableSet_image.mpr hs) _
  · exact hf.measurable

end StandardBorel

section Countable

section Unit



end Unit

end Countable

end ProbabilityTheory
