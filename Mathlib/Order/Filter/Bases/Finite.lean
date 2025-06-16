/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import Mathlib.Order.Filter.Bases.Basic
import Mathlib.Order.Filter.Finite

/-!
# Finiteness results on filter bases

A filter basis `B : FilterBasis α` on a type `α` is a nonempty collection of sets of `α`
such that the intersection of two elements of this collection contains some element of
the collection.
-/

open Set Filter

variable {α β γ : Type*} {ι ι' : Sort*}

namespace Filter

section SameType

variable {l l' : Filter α} {p : ι → Prop} {s : ι → Set α} {t : Set α} {i : ι} {p' : ι' → Prop}
  {s' : ι' → Set α} {i' : ι'}

theorem hasBasis_generate (s : Set (Set α)) :
    (generate s).HasBasis (fun t => Set.Finite t ∧ t ⊆ s) fun t => ⋂₀ t :=
  ⟨fun U => by simp only [mem_generate_iff, exists_prop, and_assoc, and_left_comm]⟩

/-- The smallest filter basis containing a given collection of sets. -/
def FilterBasis.ofSets (s : Set (Set α)) : FilterBasis α where
  sets := sInter '' { t | Set.Finite t ∧ t ⊆ s }
  nonempty := ⟨univ, ∅, ⟨⟨finite_empty, empty_subset s⟩, sInter_empty⟩⟩
  inter_sets := by
    rintro _ _ ⟨a, ⟨fina, suba⟩, rfl⟩ ⟨b, ⟨finb, subb⟩, rfl⟩
    exact ⟨⋂₀ (a ∪ b), mem_image_of_mem _ ⟨fina.union finb, union_subset suba subb⟩,
        (sInter_union _ _).subset⟩

lemma FilterBasis.ofSets_sets (s : Set (Set α)) :
    (FilterBasis.ofSets s).sets = sInter '' { t | Set.Finite t ∧ t ⊆ s } :=
  rfl

theorem generate_eq_generate_inter (s : Set (Set α)) :
    generate s = generate (sInter '' { t | Set.Finite t ∧ t ⊆ s }) := by
  rw [← FilterBasis.ofSets_sets, FilterBasis.generate, ← (hasBasis_generate s).filter_eq]; rfl

theorem ofSets_filter_eq_generate (s : Set (Set α)) :
    (FilterBasis.ofSets s).filter = generate s := by
  rw [← (FilterBasis.ofSets s).generate, FilterBasis.ofSets_sets, ← generate_eq_generate_inter]

theorem generate_neBot_iff {s : Set (Set α)} :
    NeBot (generate s) ↔ ∀ t, t ⊆ s → t.Finite → (⋂₀ t).Nonempty :=
  (hasBasis_generate s).neBot_iff.trans <| by simp only [← and_imp, and_comm]

protected theorem HasBasis.iInf' {ι : Type*} {ι' : ι → Type*} {l : ι → Filter α}
    {p : ∀ i, ι' i → Prop} {s : ∀ i, ι' i → Set α} (hl : ∀ i, (l i).HasBasis (p i) (s i)) :
    (⨅ i, l i).HasBasis (fun If : Set ι × ∀ i, ι' i => If.1.Finite ∧ ∀ i ∈ If.1, p i (If.2 i))
      fun If : Set ι × ∀ i, ι' i => ⋂ i ∈ If.1, s i (If.2 i) :=
  ⟨by
    intro t
    constructor
    · simp only [mem_iInf', (hl _).mem_iff]
      rintro ⟨I, hI, V, hV, -, rfl, -⟩
      choose u hu using hV
      exact ⟨⟨I, u⟩, ⟨hI, fun i _ => (hu i).1⟩, iInter₂_mono fun i _ => (hu i).2⟩
    · rintro ⟨⟨I, f⟩, ⟨hI₁, hI₂⟩, hsub⟩
      refine mem_of_superset ?_ hsub
      exact (biInter_mem hI₁).mpr fun i hi => mem_iInf_of_mem i <| (hl i).mem_of_mem <| hI₂ _ hi⟩

@[deprecated (since := "2025-05-05")]
alias hasBasis_iInf' := HasBasis.iInf'

protected theorem HasBasis.iInf {ι : Type*} {ι' : ι → Type*} {l : ι → Filter α}
    {p : ∀ i, ι' i → Prop} {s : ∀ i, ι' i → Set α} (hl : ∀ i, (l i).HasBasis (p i) (s i)) :
    (⨅ i, l i).HasBasis
      (fun If : Σ I : Set ι, ∀ i : I, ι' i => If.1.Finite ∧ ∀ i : If.1, p i (If.2 i)) fun If =>
      ⋂ i : If.1, s i (If.2 i) := by
  refine ⟨fun t => ⟨fun ht => ?_, ?_⟩⟩
  · rcases (HasBasis.iInf' hl).mem_iff.mp ht with ⟨⟨I, f⟩, ⟨hI, hf⟩, hsub⟩
    exact ⟨⟨I, fun i => f i⟩, ⟨hI, Subtype.forall.mpr hf⟩, trans (iInter_subtype _ _) hsub⟩
  · rintro ⟨⟨I, f⟩, ⟨hI, hf⟩, hsub⟩
    refine mem_of_superset ?_ hsub
    cases hI.nonempty_fintype
    exact iInter_mem.2 fun i => mem_iInf_of_mem ↑i <| (hl i).mem_of_mem <| hf _

@[deprecated (since := "2025-05-05")]
alias hasBasis_iInf := HasBasis.iInf

open scoped Function in -- required for scoped `on` notation
theorem _root_.Pairwise.exists_mem_filter_basis_of_disjoint {I} [Finite I] {l : I → Filter α}
    {ι : I → Sort*} {p : ∀ i, ι i → Prop} {s : ∀ i, ι i → Set α} (hd : Pairwise (Disjoint on l))
    (h : ∀ i, (l i).HasBasis (p i) (s i)) :
    ∃ ind : ∀ i, ι i, (∀ i, p i (ind i)) ∧ Pairwise (Disjoint on fun i => s i (ind i)) := by
  rcases hd.exists_mem_filter_of_disjoint with ⟨t, htl, hd⟩
  choose ind hp ht using fun i => (h i).mem_iff.1 (htl i)
  exact ⟨ind, hp, hd.mono fun i j hij => hij.mono (ht _) (ht _)⟩

theorem _root_.Set.PairwiseDisjoint.exists_mem_filter_basis {I : Type*} {l : I → Filter α}
    {ι : I → Sort*} {p : ∀ i, ι i → Prop} {s : ∀ i, ι i → Set α} {S : Set I}
    (hd : S.PairwiseDisjoint l) (hS : S.Finite) (h : ∀ i, (l i).HasBasis (p i) (s i)) :
    ∃ ind : ∀ i, ι i, (∀ i, p i (ind i)) ∧ S.PairwiseDisjoint fun i => s i (ind i) := by
  rcases hd.exists_mem_filter hS with ⟨t, htl, hd⟩
  choose ind hp ht using fun i => (h i).mem_iff.1 (htl i)
  exact ⟨ind, hp, hd.mono ht⟩

/-- If `s : ι → Set α` is an indexed family of sets, then finite intersections of `s i` form a basis
of `⨅ i, 𝓟 (s i)`. -/
theorem hasBasis_iInf_principal_finite {ι : Type*} (s : ι → Set α) :
    (⨅ i, 𝓟 (s i)).HasBasis (fun t : Set ι => t.Finite) fun t => ⋂ i ∈ t, s i := by
  refine ⟨fun U => (mem_iInf_finite _).trans ?_⟩
  simp only [iInf_principal_finset, mem_iUnion, mem_principal, exists_prop,
    exists_finite_iff_finset, Finset.set_biInter_coe]

end SameType

end Filter
