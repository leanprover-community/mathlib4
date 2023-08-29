/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Order.CompactlyGenerated
import Mathlib.Topology.Sets.Closeds

#align_import topology.noetherian_space from "leanprover-community/mathlib"@"dc6c365e751e34d100e80fe6e314c3c3e0fd2988"

/-!
# Noetherian space

A Noetherian space is a topological space that satisfies any of the following equivalent conditions:
- `WellFounded ((· > ·) : TopologicalSpace.Opens α → TopologicalSpace.Opens α → Prop)`
- `WellFounded ((· < ·) : TopologicalSpace.Closeds α → TopologicalSpace.Closeds α → Prop)`
- `∀ s : Set α, IsCompact s`
- `∀ s : TopologicalSpace.Opens α, IsCompact s`

The first is chosen as the definition, and the equivalence is shown in
`TopologicalSpace.noetherianSpace_TFAE`.

Many examples of noetherian spaces come from algebraic topology. For example, the underlying space
of a noetherian scheme (e.g., the spectrum of a noetherian ring) is noetherian.

## Main Results

- `TopologicalSpace.NoetherianSpace.set`: Every subspace of a noetherian space is noetherian.
- `TopologicalSpace.NoetherianSpace.isCompact`: Every set in a noetherian space is a compact set.
- `TopologicalSpace.noetherianSpace_TFAE`: Describes the equivalent definitions of noetherian
  spaces.
- `TopologicalSpace.NoetherianSpace.range`: The image of a noetherian space under a continuous map
  is noetherian.
- `TopologicalSpace.NoetherianSpace.iUnion`: The finite union of noetherian spaces is noetherian.
- `TopologicalSpace.NoetherianSpace.discrete`: A noetherian and Hausdorff space is discrete.
- `TopologicalSpace.NoetherianSpace.exists_finset_irreducible` : Every closed subset of a noetherian
  space is a finite union of irreducible closed subsets.
- `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents `: The number of irreducible
  components of a noetherian space is finite.

-/


variable (α β : Type*) [TopologicalSpace α] [TopologicalSpace β]

namespace TopologicalSpace

/-- Type class for noetherian spaces. It is defined to be spaces whose open sets satisfies ACC. -/
@[mk_iff noetherianSpace_iff]
class NoetherianSpace : Prop where
  wellFounded_opens : WellFounded ((· > ·) : Opens α → Opens α → Prop)
#align topological_space.noetherian_space TopologicalSpace.NoetherianSpace

theorem noetherianSpace_iff_opens : NoetherianSpace α ↔ ∀ s : Opens α, IsCompact (s : Set α) := by
  rw [noetherianSpace_iff, CompleteLattice.wellFounded_iff_isSupFiniteCompact,
    CompleteLattice.isSupFiniteCompact_iff_all_elements_compact]
  exact forall_congr' Opens.isCompactElement_iff
  -- 🎉 no goals
#align topological_space.noetherian_space_iff_opens TopologicalSpace.noetherianSpace_iff_opens

instance (priority := 100) NoetherianSpace.compactSpace [h : NoetherianSpace α] : CompactSpace α :=
  ⟨(noetherianSpace_iff_opens α).mp h ⊤⟩
#align topological_space.noetherian_space.compact_space TopologicalSpace.NoetherianSpace.compactSpace

variable {α β}

/-- In a Noetherian space, all sets are compact. -/
protected theorem NoetherianSpace.isCompact [NoetherianSpace α] (s : Set α) : IsCompact s := by
  refine isCompact_iff_finite_subcover.2 fun U hUo hs => ?_
  -- ⊢ ∃ t, s ⊆ ⋃ (i : ι✝) (_ : i ∈ t), U i
  rcases ((noetherianSpace_iff_opens α).mp ‹_› ⟨⋃ i, U i, isOpen_iUnion hUo⟩).elim_finite_subcover U
    hUo Set.Subset.rfl with ⟨t, ht⟩
  exact ⟨t, hs.trans ht⟩
  -- 🎉 no goals
#align topological_space.noetherian_space.is_compact TopologicalSpace.NoetherianSpace.isCompact

-- porting note: fixed NS
protected theorem _root_.Inducing.noetherianSpace [NoetherianSpace α] {i : β → α}
    (hi : Inducing i) : NoetherianSpace β :=
  (noetherianSpace_iff_opens _).2 fun _ => hi.isCompact_iff.1 (NoetherianSpace.isCompact _)
#align topological_space.inducing.noetherian_space Inducing.noetherianSpace

instance NoetherianSpace.set [NoetherianSpace α] (s : Set α) : NoetherianSpace s :=
  inducing_subtype_val.noetherianSpace
#align topological_space.noetherian_space.set TopologicalSpace.NoetherianSpace.set

variable (α)

open List in
theorem noetherianSpace_TFAE :
    TFAE [NoetherianSpace α,
      WellFounded fun s t : Closeds α => s < t,
      ∀ s : Set α, IsCompact s,
      ∀ s : Opens α, IsCompact (s : Set α)] := by
  tfae_have 1 ↔ 2
  -- ⊢ NoetherianSpace α ↔ WellFounded fun s t => s < t
  · refine' (noetherianSpace_iff α).trans (Surjective.wellFounded_iff Opens.compl_bijective.2 _)
    -- ⊢ ∀ {a b : Opens α}, a > b ↔ Opens.compl a < Opens.compl b
    exact (@OrderIso.compl (Set α)).lt_iff_lt.symm
    -- 🎉 no goals
  tfae_have 1 ↔ 4
  -- ⊢ NoetherianSpace α ↔ ∀ (s : Opens α), IsCompact ↑s
  · exact noetherianSpace_iff_opens α
    -- 🎉 no goals
  tfae_have 1 → 3
  -- ⊢ NoetherianSpace α → ∀ (s : Set α), IsCompact s
  · exact @NoetherianSpace.isCompact α _
    -- 🎉 no goals
  tfae_have 3 → 4
  -- ⊢ (∀ (s : Set α), IsCompact s) → ∀ (s : Opens α), IsCompact ↑s
  · exact fun h s => h s
    -- 🎉 no goals
  tfae_finish
  -- 🎉 no goals
#align topological_space.noetherian_space_tfae TopologicalSpace.noetherianSpace_TFAE

variable {α}

theorem noetherianSpace_iff_isCompact : NoetherianSpace α ↔ ∀ s : Set α, IsCompact s :=
  (noetherianSpace_TFAE α).out 0 2

theorem NoetherianSpace.wellFounded_closeds [NoetherianSpace α] :
    WellFounded fun s t : Closeds α => s < t :=
  Iff.mp ((noetherianSpace_TFAE α).out 0 1) ‹_›

instance {α} : NoetherianSpace (CofiniteTopology α) := by
  simp only [noetherianSpace_iff_isCompact, isCompact_iff_ultrafilter_le_nhds,
    CofiniteTopology.nhds_eq, Ultrafilter.le_sup_iff, Filter.le_principal_iff]
  intro s f hs
  -- ⊢ ∃ a, a ∈ s ∧ (↑f ≤ pure a ∨ ↑f ≤ Filter.cofinite)
  rcases f.le_cofinite_or_eq_pure with (hf | ⟨a, rfl⟩)
  -- ⊢ ∃ a, a ∈ s ∧ (↑f ≤ pure a ∨ ↑f ≤ Filter.cofinite)
  · rcases Filter.nonempty_of_mem hs with ⟨a, ha⟩
    -- ⊢ ∃ a, a ∈ s ∧ (↑f ≤ pure a ∨ ↑f ≤ Filter.cofinite)
    exact ⟨a, ha, Or.inr hf⟩
    -- 🎉 no goals
  · exact ⟨a, hs, Or.inl le_rfl⟩
    -- 🎉 no goals

theorem noetherianSpace_of_surjective [NoetherianSpace α] (f : α → β) (hf : Continuous f)
    (hf' : Function.Surjective f) : NoetherianSpace β :=
  noetherianSpace_iff_isCompact.2 $ (Set.image_surjective.mpr hf').forall.2 $ fun s =>
    (NoetherianSpace.isCompact s).image hf
#align topological_space.noetherian_space_of_surjective TopologicalSpace.noetherianSpace_of_surjective

theorem noetherianSpace_iff_of_homeomorph (f : α ≃ₜ β) : NoetherianSpace α ↔ NoetherianSpace β :=
  ⟨fun _ => noetherianSpace_of_surjective f f.continuous f.surjective,
    fun _ => noetherianSpace_of_surjective f.symm f.symm.continuous f.symm.surjective⟩
#align topological_space.noetherian_space_iff_of_homeomorph TopologicalSpace.noetherianSpace_iff_of_homeomorph

theorem NoetherianSpace.range [NoetherianSpace α] (f : α → β) (hf : Continuous f) :
    NoetherianSpace (Set.range f) :=
  noetherianSpace_of_surjective (Set.rangeFactorization f) (hf.subtype_mk _)
    Set.surjective_onto_range
#align topological_space.noetherian_space.range TopologicalSpace.NoetherianSpace.range

theorem noetherianSpace_set_iff (s : Set α) :
    NoetherianSpace s ↔ ∀ t, t ⊆ s → IsCompact t := by
  simp only [noetherianSpace_iff_isCompact, embedding_subtype_val.isCompact_iff_isCompact_image,
    Subtype.forall_set_subtype]
#align topological_space.noetherian_space_set_iff TopologicalSpace.noetherianSpace_set_iff

@[simp]
theorem noetherian_univ_iff : NoetherianSpace (Set.univ : Set α) ↔ NoetherianSpace α :=
  noetherianSpace_iff_of_homeomorph (Homeomorph.Set.univ α)
#align topological_space.noetherian_univ_iff TopologicalSpace.noetherian_univ_iff

theorem NoetherianSpace.iUnion {ι : Type*} (f : ι → Set α) [Finite ι]
    [hf : ∀ i, NoetherianSpace (f i)] : NoetherianSpace (⋃ i, f i) := by
  simp_rw [noetherianSpace_set_iff] at hf ⊢
  -- ⊢ ∀ (t : Set α), t ⊆ ⋃ (i : ι), f i → IsCompact t
  intro t ht
  -- ⊢ IsCompact t
  rw [← Set.inter_eq_left_iff_subset.mpr ht, Set.inter_iUnion]
  -- ⊢ IsCompact (⋃ (i : ι), t ∩ f i)
  exact isCompact_iUnion fun i => hf i _ (Set.inter_subset_right _ _)
  -- 🎉 no goals
#align topological_space.noetherian_space.Union TopologicalSpace.NoetherianSpace.iUnion

-- This is not an instance since it makes a loop with `t2_space_discrete`.
theorem NoetherianSpace.discrete [NoetherianSpace α] [T2Space α] : DiscreteTopology α :=
  ⟨eq_bot_iff.mpr fun _ _ => isClosed_compl_iff.mp (NoetherianSpace.isCompact _).isClosed⟩
#align topological_space.noetherian_space.discrete TopologicalSpace.NoetherianSpace.discrete

attribute [local instance] NoetherianSpace.discrete

/-- Spaces that are both Noetherian and Hausdorff are finite. -/
theorem NoetherianSpace.finite [NoetherianSpace α] [T2Space α] : Finite α :=
  Finite.of_finite_univ (NoetherianSpace.isCompact Set.univ).finite_of_discrete
#align topological_space.noetherian_space.finite TopologicalSpace.NoetherianSpace.finite

instance (priority := 100) Finite.to_noetherianSpace [Finite α] : NoetherianSpace α :=
  ⟨Finite.wellFounded_of_trans_of_irrefl _⟩
#align topological_space.finite.to_noetherian_space TopologicalSpace.Finite.to_noetherianSpace

/-- In a Noetherian space, every closed set is a finite union of irreducible closed sets. -/
theorem NoetherianSpace.exists_finite_set_closeds_irreducible [NoetherianSpace α] (s : Closeds α) :
    ∃ S : Set (Closeds α), S.Finite ∧ (∀ t ∈ S, IsIrreducible (t : Set α)) ∧ s = sSup S := by
  apply wellFounded_closeds.induction s; clear s
  -- ⊢ ∀ (x : Closeds α), (∀ (y : Closeds α), y < x → ∃ S, Set.Finite S ∧ (∀ (t : C …
                                         -- ⊢ ∀ (x : Closeds α), (∀ (y : Closeds α), y < x → ∃ S, Set.Finite S ∧ (∀ (t : C …
  intro s H
  -- ⊢ ∃ S, Set.Finite S ∧ (∀ (t : Closeds α), t ∈ S → IsIrreducible ↑t) ∧ s = sSup S
  rcases eq_or_ne s ⊥ with rfl | h₀
  -- ⊢ ∃ S, Set.Finite S ∧ (∀ (t : Closeds α), t ∈ S → IsIrreducible ↑t) ∧ ⊥ = sSup S
  · use ∅; simp
    -- ⊢ Set.Finite ∅ ∧ (∀ (t : Closeds α), t ∈ ∅ → IsIrreducible ↑t) ∧ ⊥ = sSup ∅
           -- 🎉 no goals
  · by_cases h₁ : IsPreirreducible (s : Set α)
    -- ⊢ ∃ S, Set.Finite S ∧ (∀ (t : Closeds α), t ∈ S → IsIrreducible ↑t) ∧ s = sSup S
    · replace h₁ : IsIrreducible (s : Set α) := ⟨Closeds.coe_nonempty.2 h₀, h₁⟩
      -- ⊢ ∃ S, Set.Finite S ∧ (∀ (t : Closeds α), t ∈ S → IsIrreducible ↑t) ∧ s = sSup S
      use {s}; simp [h₁]
      -- ⊢ Set.Finite {s} ∧ (∀ (t : Closeds α), t ∈ {s} → IsIrreducible ↑t) ∧ s = sSup  …
               -- 🎉 no goals
    · simp only [isPreirreducible_iff_closed_union_closed, not_forall, not_or] at h₁
      -- ⊢ ∃ S, Set.Finite S ∧ (∀ (t : Closeds α), t ∈ S → IsIrreducible ↑t) ∧ s = sSup S
      obtain ⟨z₁, z₂, hz₁, hz₂, h, hz₁', hz₂'⟩ := h₁
      -- ⊢ ∃ S, Set.Finite S ∧ (∀ (t : Closeds α), t ∈ S → IsIrreducible ↑t) ∧ s = sSup S
      lift z₁ to Closeds α using hz₁
      -- ⊢ ∃ S, Set.Finite S ∧ (∀ (t : Closeds α), t ∈ S → IsIrreducible ↑t) ∧ s = sSup S
      lift z₂ to Closeds α using hz₂
      -- ⊢ ∃ S, Set.Finite S ∧ (∀ (t : Closeds α), t ∈ S → IsIrreducible ↑t) ∧ s = sSup S
      rcases H (s ⊓ z₁) (inf_lt_left.2 hz₁') with ⟨S₁, hSf₁, hS₁, h₁⟩
      -- ⊢ ∃ S, Set.Finite S ∧ (∀ (t : Closeds α), t ∈ S → IsIrreducible ↑t) ∧ s = sSup S
      rcases H (s ⊓ z₂) (inf_lt_left.2 hz₂') with ⟨S₂, hSf₂, hS₂, h₂⟩
      -- ⊢ ∃ S, Set.Finite S ∧ (∀ (t : Closeds α), t ∈ S → IsIrreducible ↑t) ∧ s = sSup S
      refine ⟨S₁ ∪ S₂, hSf₁.union hSf₂, Set.union_subset_iff.2 ⟨hS₁, hS₂⟩, ?_⟩
      -- ⊢ s = sSup (S₁ ∪ S₂)
      rwa [sSup_union, ← h₁, ← h₂, ← inf_sup_left, left_eq_inf]
      -- 🎉 no goals

/-- In a Noetherian space, every closed set is a finite union of irreducible closed sets. -/
theorem NoetherianSpace.exists_finite_set_isClosed_irreducible [NoetherianSpace α]
    {s : Set α} (hs : IsClosed s) : ∃ S : Set (Set α), S.Finite ∧
      (∀ t ∈ S, IsClosed t) ∧ (∀ t ∈ S, IsIrreducible t) ∧ s = ⋃₀ S := by
  lift s to Closeds α using hs
  -- ⊢ ∃ S, Set.Finite S ∧ (∀ (t : Set α), t ∈ S → IsClosed t) ∧ (∀ (t : Set α), t  …
  rcases NoetherianSpace.exists_finite_set_closeds_irreducible s with ⟨S, hSf, hS, rfl⟩
  -- ⊢ ∃ S_1, Set.Finite S_1 ∧ (∀ (t : Set α), t ∈ S_1 → IsClosed t) ∧ (∀ (t : Set  …
  refine ⟨(↑) '' S, hSf.image _, Set.ball_image_iff.2 fun S _ => S.2, Set.ball_image_iff.2 hS, ?_⟩
  -- ⊢ ↑(sSup S) = ⋃₀ (SetLike.coe '' S)
  lift S to Finset (Closeds α) using hSf
  -- ⊢ ↑(sSup ↑S) = ⋃₀ (SetLike.coe '' ↑S)
  simp [← Finset.sup_id_eq_sSup, Closeds.coe_finset_sup]
  -- 🎉 no goals

/-- In a Noetherian space, every closed set is a finite union of irreducible closed sets. -/
theorem NoetherianSpace.exists_finset_irreducible [NoetherianSpace α] (s : Closeds α) :
    ∃ S : Finset (Closeds α), (∀ k : S, IsIrreducible (k : Set α)) ∧ s = S.sup id := by
  simpa [Set.exists_finite_iff_finset, Finset.sup_id_eq_sSup]
    using NoetherianSpace.exists_finite_set_closeds_irreducible s
#align topological_space.noetherian_space.exists_finset_irreducible TopologicalSpace.NoetherianSpace.exists_finset_irreducible

theorem NoetherianSpace.finite_irreducibleComponents [NoetherianSpace α] :
    (irreducibleComponents α).Finite := by
  obtain ⟨S : Set (Set α), hSf, hSc, hSi, hSU⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible isClosed_univ (α := α)
  refine hSf.subset fun s hs => ?_
  -- ⊢ s ∈ S
  lift S to Finset (Set α) using hSf
  -- ⊢ s ∈ ↑S
  rcases isIrreducible_iff_sUnion_closed.1 hs.1 S hSc (hSU ▸ Set.subset_univ _) with ⟨t, htS, ht⟩
  -- ⊢ s ∈ ↑S
  rwa [ht.antisymm (hs.2 (hSi _ htS) ht)]
  -- 🎉 no goals
#align topological_space.noetherian_space.finite_irreducible_components TopologicalSpace.NoetherianSpace.finite_irreducibleComponents

end TopologicalSpace
