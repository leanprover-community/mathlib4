/-
Copyright (c) 2026 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
module

public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
public import Mathlib.Topology.Algebra.WithZeroTopology
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic

/-!
# Extending Valuation to Completion

- Completion of valuation
- Completion of valuative relation
- compatibility IsValuativeTopology
- compatibility Valuation.Compatible

Valued Field should be in another file. Completabletopfield,
-/

@[expose] public section

open Valuation ValuativeRel IsValuativeTopology UniformSpace MonoidWithZeroHom ValueGroup₀ Set

variable {R K Γ₀ : Type*}

section Valuation

variable [Ring R] [ValuativeRel R] [LinearOrderedCommGroupWithZero Γ₀]

local instance (v : Valuation R Γ₀) : TopologicalSpace (ValueGroup₀ (.ofClass v)) :=
  WithZeroTopology.topologicalSpace

namespace WithZeroTopology

open Filter

variable (Γ₀) in
def filterBasis : FilterBasis (Γ₀ × Γ₀) where
  sets := {{(α, β) : Γ₀ × Γ₀ | α = β ∨ (α < γ ∧ β < γ)} | γ : Γ₀}
  nonempty := ⟨{(α, β) : Γ₀ × Γ₀ | α = β ∨ (α < 1 ∧ β < 1)}, 1, rfl⟩
  inter_sets := fun ⟨γ1, s1⟩ ⟨γ2, s2⟩ ↦ by
    let γ := min γ1 γ2
    use {(α, β) : Γ₀ × Γ₀ | α = β ∨ (α < γ ∧ β < γ)}
    simp [← s1, ← s2]
    grind

scoped instance (priority := 100) : UniformSpace Γ₀ where
  uniformity := (filterBasis Γ₀).filter
  symm _ hU := by
    rw [FilterBasis.mem_filter_iff] at hU
    obtain ⟨V, ⟨γ, hγ⟩, h⟩ := hU
    exact ⟨V, ⟨γ, hγ⟩, by grind⟩
  comp U hU := by
    obtain ⟨V, ⟨γ, hγ⟩, h⟩ := hU
    rw [Filter.mem_lift'_sets]
    · refine ⟨V, ⟨(filterBasis Γ₀).mem_filter_of_mem ⟨γ, hγ⟩, ?_⟩⟩
      simp [← hγ, SetRel.comp]
      grind
    · exact Monotone.relComp monotone_id monotone_id
  nhds_eq_comap_uniformity γ := by
    ext U
    by_cases h : γ = 0
    · rw [h]
      simp only [nhds_zero, ne_eq, mem_comap]
      refine ⟨fun hU ↦ ?_, fun hU ↦ ?_⟩
      · rw [Filter.mem_biInf_principal] at hU
        obtain ⟨s, hs1, hs2, hs3⟩ := hU
        by_cases h : s.Nonempty
        · let γ : Γ₀ := Finset.min' hs1.toFinset (by simpa)
          use {(α, β) : Γ₀ × Γ₀ | α = β ∨ (α < γ ∧ β < γ)}
          constructor
          · apply (filterBasis Γ₀).mem_filter_of_mem
            use γ
          · simp
            have : 0 < γ := sorry
            simp [this]
            convert! hs3
            sorry
        · rw [Set.not_nonempty_iff_eq_empty] at h
          simp_all only [finite_empty, mem_empty_iff_false, IsEmpty.forall_iff, implies_true,
            iInter_of_empty, iInter_univ, univ_subset_iff, subset_univ, and_true]
          obtain ⟨s, h⟩ := (filterBasis Γ₀).nonempty
          exact ⟨s, (filterBasis Γ₀).mem_filter_of_mem h⟩
      · sorry
    · refine ⟨fun hU ↦ ?_, fun hU ↦ ?_⟩
      · sorry
      · sorry

end WithZeroTopology

section TopologicalSpace

variable [TopologicalSpace R] [IsValuativeTopology R] (v : Valuation R Γ₀) [v.Compatible]

theorem Valuation.continuous_restrict :
    Continuous v.restrict := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases eq_or_ne (v.restrict x) 0 with (h | h)
  · rw [ContinuousAt, h, WithZeroTopology.tendsto_zero]
    intro γ hγ
    rw [Filter.Eventually, v.mem_nhds_iff]
    use Units.mk0 γ hγ
    simp only [Units.val_mk0, Set.setOf_subset_setOf]
    intro a ha
    calc
    _ ≤ max (v.restrict (a - x)) (v.restrict x) := by simpa using v.restrict.map_add (a - x) x
    _ < γ := by simp [h, ha]
  · rw [ContinuousAt, WithZeroTopology.tendsto_of_ne_zero h]
    simp_rw [v.restrict_inj]
    apply Valuation.locally_const
    simpa [restrict₀_apply] using h

end TopologicalSpace

section UniformSpace

variable [UniformSpace R] [IsValuativeTopology R] [IsUniformAddGroup R] (v : Valuation R Γ₀) [v.Compatible]

open WithZeroTopology

theorem Valuation.uniformContinuous_restrict : UniformContinuous v.restrict := sorry

noncomputable def Valuation.restrictCompletionFun : Completion R → ValueGroup₀ (.ofClass v) :=
  Completion.extension v.restrict

@[simp]
theorem Valuation.restrictCompletionFun.apply_coe (x : R) :
    v.restrictCompletionFun x = v.restrict x :=
  Completion.extension_coe v.uniformContinuous_restrict x

-- multiplication is continuous
#synth MonoidWithZeroHomClass (Valuation R Γ₀) R Γ₀

lemma valuation_isClosedMap : IsClosedMap v.restrict := by
  refine IsClosedMap.of_nonempty ?_
  intro U hU hU'
  simp only [← isOpen_compl_iff, isOpen_iff_mem_nhds, mem_compl_iff, v.mem_nhds_iff, subset_compl_comm,
    compl_setOf, not_lt] at hU
  simp only [isClosed_iff, mem_image, map_eq_zero v.restrict, exists_eq_right, ne_eq, image_subset_iff]
  by_cases h : 0 ∈ U
  · left
    use 0
  refine (em _).imp_right fun h ↦ ?_
  obtain ⟨γ, h⟩ := hU _ h
  simp only [sub_zero] at h
  refine ⟨γ.1, γ.ne_zero, h.trans ?_⟩
  intro
  simp

noncomputable def Valuation.restrictCompletion :
    Valuation (Completion R) (ValueGroup₀ (.ofClass v)) where
  toFun := v.restrictCompletionFun
  map_zero' := sorry
  map_one' := sorry
  map_mul' x y := by
    refine Completion.induction_on₂ x y ?_ ?_
    · sorry
    · sorry
  map_add_le_max' := sorry

noncomputable
def Valuation.completion (v : Valuation R Γ₀) [v.Compatible] : Valuation (Completion R) Γ₀ :=
  v.restrictCompletion.map embedding embedding_strictMono.monotone

end UniformSpace

end Valuation

section ValuativeRel

variable [Ring R] [UniformSpace R] [IsTopologicalRing R] [IsUniformAddGroup R] [ValuativeRel R]
  [IsValuativeTopology R]

instance UniformSpace.Completion.valuativeRel : ValuativeRel R := sorry
-- UniformSpace.Completion.extension₂ for relations

instance UniformSpace.Completion.isValuativeTopology : IsValuativeTopology R := sorry

end ValuativeRel

section Compatible

variable [Ring R] [UniformSpace R] [IsTopologicalRing R] [IsUniformAddGroup R] [ValuativeRel R]
  [IsValuativeTopology R] [LinearOrderedCommGroupWithZero Γ₀]

instance Valuation.compatible_completion (v : Valuation R Γ₀) [v.Compatible] :
    v.completion.Compatible := sorry

end Compatible
