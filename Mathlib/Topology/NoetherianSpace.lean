/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module topology.noetherian_space
! leanprover-community/mathlib commit dc6c365e751e34d100e80fe6e314c3c3e0fd2988
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.CompactlyGenerated
import Mathbin.Topology.Sets.Closeds

/-!
# Noetherian space

A Noetherian space is a topological space that satisfies any of the following equivalent conditions:
- `well_founded ((>) : opens α → opens α → Prop)`
- `well_founded ((<) : closeds α → closeds α → Prop)`
- `∀ s : set α, is_compact s`
- `∀ s : opens α, is_compact s`

The first is chosen as the definition, and the equivalence is shown in
`topological_space.noetherian_space_tfae`.

Many examples of noetherian spaces come from algebraic topology. For example, the underlying space
of a noetherian scheme (e.g., the spectrum of a noetherian ring) is noetherian.

## Main Results
- `noetherian_space.set`: Every subspace of a noetherian space is noetherian.
- `noetherian_space.is_compact`: Every subspace of a noetherian space is compact.
- `noetherian_space_tfae`: Describes the equivalent definitions of noetherian spaces.
- `noetherian_space.range`: The image of a noetherian space under a continuous map is noetherian.
- `noetherian_space.Union`: The finite union of noetherian spaces is noetherian.
- `noetherian_space.discrete`: A noetherian and hausdorff space is discrete.
- `noetherian_space.exists_finset_irreducible` : Every closed subset of a noetherian space is a
  finite union of irreducible closed subsets.
- `noetherian_space.finite_irreducible_components `: The number of irreducible components of a
  noetherian space is finite.

-/


variable (α β : Type _) [TopologicalSpace α] [TopologicalSpace β]

namespace TopologicalSpace

/-- Type class for noetherian spaces. It is defined to be spaces whose open sets satisfies ACC. -/
@[mk_iff]
class NoetherianSpace : Prop where
  WellFounded : WellFounded ((· > ·) : Opens α → Opens α → Prop)
#align topological_space.noetherian_space TopologicalSpace.NoetherianSpace

theorem noetherianSpace_iff_opens : NoetherianSpace α ↔ ∀ s : Opens α, IsCompact (s : Set α) :=
  by
  rw [noetherian_space_iff, CompleteLattice.wellFounded_iff_isSupFiniteCompact,
    CompleteLattice.isSupFiniteCompact_iff_all_elements_compact]
  exact forall_congr' opens.is_compact_element_iff
#align topological_space.noetherian_space_iff_opens TopologicalSpace.noetherianSpace_iff_opens

instance (priority := 100) NoetherianSpace.compactSpace [h : NoetherianSpace α] : CompactSpace α :=
  ⟨(noetherianSpace_iff_opens α).mp h ⊤⟩
#align topological_space.noetherian_space.compact_space TopologicalSpace.NoetherianSpace.compactSpace

variable {α β}

protected theorem NoetherianSpace.isCompact [NoetherianSpace α] (s : Set α) : IsCompact s :=
  by
  refine' isCompact_iff_finite_subcover.2 fun ι U hUo hs => _
  rcases((noetherian_space_iff_opens α).mp ‹_› ⟨⋃ i, U i, isOpen_unionᵢ hUo⟩).elim_finite_subcover U
      hUo Set.Subset.rfl with
    ⟨t, ht⟩
  exact ⟨t, hs.trans ht⟩
#align topological_space.noetherian_space.is_compact TopologicalSpace.NoetherianSpace.isCompact

protected theorem Inducing.noetherianSpace [NoetherianSpace α] {i : β → α} (hi : Inducing i) :
    NoetherianSpace β :=
  (noetherianSpace_iff_opens _).2 fun s => hi.isCompact_iff.1 (NoetherianSpace.isCompact _)
#align topological_space.inducing.noetherian_space TopologicalSpace.Inducing.noetherianSpace

instance NoetherianSpace.set [h : NoetherianSpace α] (s : Set α) : NoetherianSpace s :=
  inducing_subtype_val.NoetherianSpace
#align topological_space.noetherian_space.set TopologicalSpace.NoetherianSpace.set

variable (α)

example (α : Type _) : Set α ≃o (Set α)ᵒᵈ := by refine' OrderIso.compl (Set α)

theorem noetherianSpace_tFAE :
    TFAE
      [NoetherianSpace α, WellFounded fun s t : Closeds α => s < t, ∀ s : Set α, IsCompact s,
        ∀ s : Opens α, IsCompact (s : Set α)] :=
  by
  tfae_have 1 ↔ 2
  · refine' (noetherian_space_iff _).trans (Surjective.wellFounded_iff opens.compl_bijective.2 _)
    exact fun s t => (OrderIso.compl (Set α)).lt_iff_lt.symm
  tfae_have 1 ↔ 4
  · exact noetherian_space_iff_opens α
  tfae_have 1 → 3
  · exact @noetherian_space.is_compact _ _
  tfae_have 3 → 4
  · exact fun H s => H s
  tfae_finish
#align topological_space.noetherian_space_tfae TopologicalSpace.noetherianSpace_tFAE

variable {α β}

instance {α} : NoetherianSpace (CofiniteTopology α) :=
  by
  simp only [noetherian_space_iff_opens, isCompact_iff_ultrafilter_le_nhds,
    CofiniteTopology.nhds_eq, Ultrafilter.le_sup_iff]
  intro s f hs
  rcases f.le_cofinite_or_eq_pure with (hf | ⟨a, rfl⟩)
  · rcases Filter.nonempty_of_mem (Filter.le_principal_iff.1 hs) with ⟨a, ha⟩
    exact ⟨a, ha, Or.inr hf⟩
  · exact ⟨a, filter.le_principal_iff.mp hs, Or.inl le_rfl⟩

theorem noetherianSpace_of_surjective [NoetherianSpace α] (f : α → β) (hf : Continuous f)
    (hf' : Function.Surjective f) : NoetherianSpace β :=
  by
  rw [noetherian_space_iff_opens]
  intro s
  obtain ⟨t, e⟩ := set.image_surjective.mpr hf' s
  exact e ▸ (noetherian_space.is_compact t).image hf
#align topological_space.noetherian_space_of_surjective TopologicalSpace.noetherianSpace_of_surjective

theorem noetherianSpace_iff_of_homeomorph (f : α ≃ₜ β) : NoetherianSpace α ↔ NoetherianSpace β :=
  ⟨fun h => @noetherianSpace_of_surjective _ _ h f f.Continuous f.Surjective, fun h =>
    @noetherianSpace_of_surjective _ _ h f.symm f.symm.Continuous f.symm.Surjective⟩
#align topological_space.noetherian_space_iff_of_homeomorph TopologicalSpace.noetherianSpace_iff_of_homeomorph

theorem NoetherianSpace.range [NoetherianSpace α] (f : α → β) (hf : Continuous f) :
    NoetherianSpace (Set.range f) :=
  noetherianSpace_of_surjective (Set.codRestrict f _ Set.mem_range_self) (by continuity)
    fun ⟨a, b, h⟩ => ⟨b, Subtype.ext h⟩
#align topological_space.noetherian_space.range TopologicalSpace.NoetherianSpace.range

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (t «expr ⊆ » s) -/
theorem noetherianSpace_set_iff (s : Set α) : NoetherianSpace s ↔ ∀ (t) (_ : t ⊆ s), IsCompact t :=
  by
  rw [(noetherian_space_tfae s).out 0 2]
  constructor
  · intro H t ht
    have := embedding_subtype_coe.is_compact_iff_is_compact_image.mp (H (coe ⁻¹' t))
    simpa [set.inter_eq_left_iff_subset.mpr ht] using this
  · intro H t
    refine' embedding_subtype_coe.is_compact_iff_is_compact_image.mpr (H (coe '' t) _)
    simp
#align topological_space.noetherian_space_set_iff TopologicalSpace.noetherianSpace_set_iff

@[simp]
theorem noetherian_univ_iff : NoetherianSpace (Set.univ : Set α) ↔ NoetherianSpace α :=
  noetherianSpace_iff_of_homeomorph (Homeomorph.Set.univ α)
#align topological_space.noetherian_univ_iff TopologicalSpace.noetherian_univ_iff

theorem NoetherianSpace.unionᵢ {ι : Type _} (f : ι → Set α) [Finite ι]
    [hf : ∀ i, NoetherianSpace (f i)] : NoetherianSpace (⋃ i, f i) :=
  by
  cases nonempty_fintype ι
  simp_rw [noetherian_space_set_iff] at hf⊢
  intro t ht
  rw [← set.inter_eq_left_iff_subset.mpr ht, Set.inter_unionᵢ]
  exact isCompact_unionᵢ fun i => hf i _ (Set.inter_subset_right _ _)
#align topological_space.noetherian_space.Union TopologicalSpace.NoetherianSpace.unionᵢ

-- This is not an instance since it makes a loop with `t2_space_discrete`.
theorem NoetherianSpace.discrete [NoetherianSpace α] [T2Space α] : DiscreteTopology α :=
  ⟨eq_bot_iff.mpr fun U _ => isClosed_compl_iff.mp (NoetherianSpace.isCompact _).IsClosed⟩
#align topological_space.noetherian_space.discrete TopologicalSpace.NoetherianSpace.discrete

attribute [local instance] noetherian_space.discrete

/-- Spaces that are both Noetherian and Hausdorff is finite. -/
theorem NoetherianSpace.finite [NoetherianSpace α] [T2Space α] : Finite α :=
  by
  letI : Fintype α :=
    Set.fintypeOfFiniteUniv (noetherian_space.is_compact Set.univ).finite_of_discrete
  infer_instance
#align topological_space.noetherian_space.finite TopologicalSpace.NoetherianSpace.finite

instance (priority := 100) Finite.to_noetherianSpace [Finite α] : NoetherianSpace α :=
  ⟨Finite.wellFounded_of_trans_of_irrefl _⟩
#align topological_space.finite.to_noetherian_space TopologicalSpace.Finite.to_noetherianSpace

theorem NoetherianSpace.exists_finset_irreducible [NoetherianSpace α] (s : Closeds α) :
    ∃ S : Finset (Closeds α), (∀ k : S, IsIrreducible (k : Set α)) ∧ s = S.sup id := by
  classical
    have := ((noetherian_space_tfae α).out 0 1).mp inferInstance
    apply WellFounded.induction this s
    clear s
    intro s H
    by_cases h₁ : IsPreirreducible s.1
    cases h₂ : s.1.eq_empty_or_nonempty
    · use ∅
      refine' ⟨fun k => k.2.elim, _⟩
      rw [Finset.sup_empty]
      ext1
      exact h
    · use {s}
      simp only [coe_coe, Finset.sup_singleton, id.def, eq_self_iff_true, and_true_iff]
      rintro ⟨k, hk⟩
      cases finset.mem_singleton.mp hk
      exact ⟨h, h₁⟩
    · rw [isPreirreducible_iff_closed_union_closed] at h₁
      push_neg  at h₁
      obtain ⟨z₁, z₂, hz₁, hz₂, h, hz₁', hz₂'⟩ := h₁
      obtain ⟨S₁, hS₁, hS₁'⟩ := H (s ⊓ ⟨z₁, hz₁⟩) (inf_lt_left.2 hz₁')
      obtain ⟨S₂, hS₂, hS₂'⟩ := H (s ⊓ ⟨z₂, hz₂⟩) (inf_lt_left.2 hz₂')
      refine' ⟨S₁ ∪ S₂, fun k => _, _⟩
      · cases' finset.mem_union.mp k.2 with h' h'
        exacts[hS₁ ⟨k, h'⟩, hS₂ ⟨k, h'⟩]
      · rwa [Finset.sup_union, ← hS₁', ← hS₂', ← inf_sup_left, left_eq_inf]
#align topological_space.noetherian_space.exists_finset_irreducible TopologicalSpace.NoetherianSpace.exists_finset_irreducible

theorem NoetherianSpace.finite_irreducibleComponents [NoetherianSpace α] :
    (irreducibleComponents α).Finite := by
  classical
    obtain ⟨S, hS₁, hS₂⟩ := noetherian_space.exists_finset_irreducible (⊤ : closeds α)
    suffices irreducibleComponents α ⊆ coe '' (S : Set <| closeds α) by
      exact Set.Finite.subset ((Set.Finite.intro inferInstance).image _) this
    intro K hK
    obtain ⟨z, hz, hz'⟩ : ∃ (z : Set α)(H : z ∈ Finset.image coe S), K ⊆ z :=
      by
      convert is_irreducible_iff_sUnion_closed.mp hK.1 (S.image coe) _ _
      · simp only [Finset.mem_image, exists_prop, forall_exists_index, and_imp]
        rintro _ z hz rfl
        exact z.2
      · exact (Set.subset_univ _).trans ((congr_arg coe hS₂).trans <| by simp).Subset
    obtain ⟨s, hs, e⟩ := finset.mem_image.mp hz
    rw [← e] at hz'
    refine' ⟨s, hs, _⟩
    symm
    suffices K ≤ s by exact this.antisymm (hK.2 (hS₁ ⟨s, hs⟩) this)
    simpa
#align topological_space.noetherian_space.finite_irreducible_components TopologicalSpace.NoetherianSpace.finite_irreducibleComponents

end TopologicalSpace

