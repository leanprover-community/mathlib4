/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Dagur Asgeirsson
-/
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact

/-!
# Topological bases in compact sets and compact spaces
-/

open Set TopologicalSpace

variable {X ι : Type*} [TopologicalSpace X]

lemma eq_finite_iUnion_of_isTopologicalBasis_of_isCompact_open (b : ι → Set X)
    (hb : IsTopologicalBasis (Set.range b)) (U : Set X) (hUc : IsCompact U) (hUo : IsOpen U) :
    ∃ s : Set ι, s.Finite ∧ U = ⋃ i ∈ s, b i := by
  obtain ⟨Y, f, e, hf⟩ := hb.open_eq_iUnion hUo
  choose f' hf' using hf
  have : b ∘ f' = f := funext hf'
  subst this
  obtain ⟨t, ht⟩ :=
    hUc.elim_finite_subcover (b ∘ f') (fun i => hb.isOpen (Set.mem_range_self _)) (by rw [e])
  classical
  refine ⟨t.image f', Set.toFinite _, le_antisymm ?_ ?_⟩
  · refine Set.Subset.trans ht ?_
    simp only [Set.iUnion_subset_iff]
    intro i hi
    simpa using subset_iUnion₂ (s := fun i _ => b (f' i)) i hi
  · apply Set.iUnion₂_subset
    rintro i hi
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
    rw [e]
    exact Set.subset_iUnion (b ∘ f') j

lemma eq_sUnion_finset_of_isTopologicalBasis_of_isCompact_open (b : Set (Set X))
    (hb : IsTopologicalBasis b) (U : Set X) (hUc : IsCompact U) (hUo : IsOpen U) :
    ∃ s : Finset b, U = (s : Set b).sUnion := by
  have hb' : b = range (fun i ↦ i : b → Set X) := by simp
  rw [hb'] at hb
  choose s hs hU using eq_finite_iUnion_of_isTopologicalBasis_of_isCompact_open _ hb U hUc hUo
  have : Finite s := hs
  let _ : Fintype s := Fintype.ofFinite _
  use s.toFinset
  simp [hU]

/-- If `X` has a basis consisting of compact opens, then an open set in `X` is compact open iff
  it is a finite union of some elements in the basis -/
theorem isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis (b : ι → Set X)
    (hb : IsTopologicalBasis (Set.range b)) (hb' : ∀ i, IsCompact (b i)) (U : Set X) :
    IsCompact U ∧ IsOpen U ↔ ∃ s : Set ι, s.Finite ∧ U = ⋃ i ∈ s, b i := by
  constructor
  · exact fun ⟨h₁, h₂⟩ ↦ eq_finite_iUnion_of_isTopologicalBasis_of_isCompact_open _ hb U h₁ h₂
  · rintro ⟨s, hs, rfl⟩
    constructor
    · exact hs.isCompact_biUnion fun i _ => hb' i
    · exact isOpen_biUnion fun i _ => hb.isOpen (Set.mem_range_self _)
