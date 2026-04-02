/-
Copyright (c) 2026 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li
-/
module

public import Mathlib.Topology.Bases

/-!
# Closed bases and closed subbases of topologies.

This file defines closed bases and closed subbases of topologies, and proves some basic properties
of them.

## Main definitions

* `TopologicalSpace.IsClosedBasis s`: A closed basis of a topological space `α` is a collection of
  closed sets `s : Set (Set α)` such that every closed subset of `α` can be written as an
  intersection of elements of `s`.
* `TopologicalSpace.IsClosedSubbasis s`: Given a topological space `α`, `s : Set (Set α)` is a
  closed subbasis if the topology on `α` equals `generateFrom { uᶜ | u ∈ s }`.
-/

@[expose] public section

open Set

variable {α : Type*} [t : TopologicalSpace α]

namespace TopologicalSpace

/-- A closed basis is a collection of closed sets `s : Set (Set α)` such that every closed subset
of `α` can be written as an intersection of elements of `s`. -/
structure IsClosedBasis (s : Set (Set α)) : Prop where
  exists_union_subset : ∀ t₁ ∈ s, ∀ t₂ ∈ s, ∀ x ∉ t₁ ∪ t₂, ∃ t₃ ∈ s, x ∉ t₃ ∧ t₁ ∪ t₂ ⊆ t₃
  sInter_eq : ⋂₀ s = ∅
  eq_generateFrom : t = generateFrom (compl '' s)

theorem isClosedBasis_iff (s : Set (Set α)) :
    IsClosedBasis s ↔ IsTopologicalBasis (compl '' s) := by
  refine ⟨fun ⟨hs1, hs2, hts⟩ => ⟨?_, ?_, hts⟩, fun ⟨hs1, hs2, hts⟩ => ⟨?_, ?_, hts⟩⟩
  · simpa using hs1
  · exact (s.compl_sInter ▸ eq_compl_comm.1 (compl_univ ▸ hs2)).symm
  · simpa using hs1
  · exact compl_univ ▸ eq_compl_comm.2 (s.compl_sInter ▸ hs2.symm)

theorem IsClosedBasis.isClosed {u : Set α} {s : Set (Set α)}
    (hs : IsClosedBasis s) (hus : u ∈ s) : IsClosed u := by
  rw [hs.eq_generateFrom]
  simp_rw [← isOpen_compl_iff]
  exact isOpen_generateFrom_of_mem ⟨u, hus, rfl⟩

/-- `IsClosedSubbasis s` means that the topology on `α` equals `generateFrom { uᶜ | u ∈ s }`. -/
def IsClosedSubbasis (s : Set (Set α)) := t = generateFrom (compl '' s)

theorem IsClosedSubbasis.isClosed {u : Set α} {s : Set (Set α)}
    (hs : IsClosedSubbasis s) (hus : u ∈ s) : IsClosed u :=
  isOpen_compl_iff.1 <| hs ▸ isOpen_generateFrom_of_mem ⟨u, hus, rfl⟩

theorem isClosedSubbasis_iff_isTopologicalBasis_sInter_compl (s : Set (Set α)) :
    IsClosedSubbasis s ↔
      IsTopologicalBasis ((fun f => ⋂₀ f) '' { f : Set (Set α) | f.Finite ∧ f ⊆ compl '' s }) :=
  subbasis_iff_isTopologicalBasis_sInter (compl '' s)

theorem isClosedSubbasis_iff_isClosedBasis_sUnion (s : Set (Set α)) :
    IsClosedSubbasis s ↔
      IsClosedBasis ((fun f => ⋃₀ f) '' { f : Set (Set α) | f.Finite ∧ f ⊆ s }) := by
  refine (isClosedSubbasis_iff_isTopologicalBasis_sInter_compl s).trans
    ((isClosedBasis_iff _).trans <| iff_of_eq <| compl_image_set_of ▸ ?_).symm
  congr
  ext t
  refine ⟨fun ⟨f, ⟨hf, hfs⟩, hft⟩ => ?_, fun ⟨f, ⟨hf, hfs⟩, hft⟩ => ?_⟩
  · exact ⟨compl '' f, ⟨hf.image compl, image_mono hfs⟩,
      (f.compl_sUnion ▸ eq_compl_comm.1 hft).symm⟩
  · exact ⟨compl '' f, ⟨hf.image compl, s.compl_compl_image ▸ image_mono hfs⟩,
      eq_compl_comm.2 (compl_sUnion _ ▸ f.compl_compl_image.symm ▸ hft.symm)⟩

theorem isClosedBasis_of_isClosedSubbasis_of_union {s : Set (Set α)} (hs1 : IsClosedSubbasis s)
    (hs2 : ∀ u ∈ s, ∀ v ∈ s, u ∪ v ∈ s) : IsClosedBasis (insert ∅ s) :=
  (isClosedBasis_iff (insert ∅ s)).2 <| s.image_insert_eq ▸
    compl_empty ▸ isTopologicalBasis_of_subbasis_of_inter hs1
      fun _ ⟨u, hus, hu⟩ _ ⟨v, hvs, hv⟩ => hu ▸ hv ▸ ⟨u ∪ v, hs2 u hus v hvs, u.compl_union v⟩

theorem IsClosedBasis.closed_iff_eq_sInter {s : Set (Set α)} (hs : IsClosedBasis s)
    (u : Set α) : IsClosed u ↔ ∃ s' ⊆ s, u = ⋂₀ s' := by
  refine isOpen_compl_iff.symm.trans <| ((isClosedBasis_iff s).1 hs).open_iff_eq_sUnion.trans
    ⟨fun ⟨s', hs's, hus'⟩ => ?_, fun ⟨s', hs's, hus'⟩ => ?_⟩
  · exact ⟨compl '' s', s.compl_compl_image ▸ s'.image_mono hs's,
      (compl_sUnion _ ▸ compl_eq_comm.1 hus').symm⟩
  · exact ⟨compl '' s', s'.image_mono hs's,
      compl_eq_comm.1 <| compl_sUnion _ ▸ s'.compl_compl_image.symm ▸ hus'.symm⟩

theorem isClosedBasis_iff_and (s : Set (Set α)) :
    IsClosedBasis s ↔
      (∀ u ∈ s, IsClosed u) ∧ (∀ u : Set α, IsClosed u → ∃ s' ⊆ s, u = ⋂₀ s') := by
  refine ⟨fun hs => ⟨fun u hus => hs.isClosed hus, fun u hu => (hs.closed_iff_eq_sInter u).1 hu⟩,
    fun ⟨hs1, hs2⟩ => ⟨fun t₁ ht₁s t₂ ht₂s x hxt => ?_, ?_, ?_⟩⟩
  · obtain ⟨s', hs's, hts'⟩ := hs2 (t₁ ∪ t₂) <| (hs1 t₁ ht₁s).union (hs1 t₂ ht₂s)
    obtain ⟨t₃, ht₃s', hxt₃⟩ : ∃ t₃ ∈ s', x ∉ t₃ := by simpa using (hts' ▸ hxt : x ∉ ⋂₀ s')
    exact ⟨t₃,  hs's ht₃s', hxt₃, hts' ▸ s'.sInter_subset_of_mem ht₃s'⟩
  · obtain ⟨s', hs's, hs'⟩ := hs2 ∅ isClosed_empty
    exact subset_eq_empty (hs' ▸ sInter_subset_sInter hs's) rfl
  · refine eq_of_le_of_ge (le_generateFrom fun u ⟨v, hvs, hvu⟩ => hvu ▸ (hs1 v hvs).isOpen_compl)
      (fun u hu => ?_)
    obtain ⟨s', hs's, hus'⟩ := hs2 uᶜ (isClosed_compl_iff.2 hu)
    exact compl_eq_comm.1 hus' ▸ s'.compl_sInter ▸
      @isOpen_sUnion _ (generateFrom (compl '' s)) _ fun v hvs' =>
        isOpen_generateFrom_of_mem <| s'.image_mono hs's hvs'

end TopologicalSpace
