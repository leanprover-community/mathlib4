/-
Copyright (c) 2024 Miguel Marco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel Marco
-/
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Lattice

/-!
# Subsets as subtypes

This file defines the function `set_restrict` that converts sets in a type, to sets in a subtype
(as the elements in the subtype whose lift lives in the set), and some notation and simplification
lemmas for convenience.

More precisely, given `α : Type` and `A : Set α`, `set_restrict A : Set α → Set A` takes
some `B : Set α` and produces some `Set ↑A` whose elements are `{ x : ↑A | ↑x ∈ B}`.

It also defines the notation `B ↓∩ A` for `set_restrict A B`.

## Implementation

The simplification lemmas are designed to reduce the number of appearances of the operation `↓∩`
in an expression, if possible.

## Tags

subsets
-/

open Set

universe u

variable {α β : Type u} {A B C: Set α} {S : Set (Set α)} (i : β → Set α)

namespace Subset

def set_restrict (B A : Set α) : Set ↑A := restrict A B

infixl:67 " ↓∩ "  => set_restrict

@[simp]
lemma mem_set_restrict_iff (x : A): x ∈  (B ↓∩ A) ↔ ↑x ∈ B := by rfl

@[simp]
lemma set_restrict_empty : (∅ : Set α) ↓∩  A = (∅ : Set A) := rfl

@[simp]
lemma set_restrict_self : A ↓∩ A = univ := by
  ext x
  simp only [mem_set_restrict_iff, Subtype.coe_prop, mem_univ]

@[simp]
lemma set_restrict_univ : (univ : Set α) ↓∩  A = (univ : Set A) := rfl

@[simp]
lemma set_restrict_union : (B ↓∩ A) ∪ (C ↓∩ A) = (B ∪ C) ↓∩ A :=  rfl

@[simp]
lemma set_restrict_inter :  (B ↓∩ A) ∩ (C ↓∩ A) = (B ∩ C) ↓∩ A :=  rfl

@[simp]
lemma set_inter_self_left_restrict : (B ∩ A) ↓∩ A = B ↓∩ A := by
  rw [← set_restrict_inter ]
  simp only [set_restrict_self, inter_univ]

@[simp]
lemma set_inter_self_right_restrict: (A ∩ B) ↓∩ A = B ↓∩ A := by
  rw [← set_restrict_inter ]
  simp only [set_restrict_self, univ_inter]

lemma set_restrict_eq_univ_of_subset (h : A ⊆ B) : B ↓∩ A = univ := by
  ext x
  simp only [mem_set_restrict_iff, mem_univ, iff_true]
  exact h x.2

@[simp]
lemma union_self_right_restrict: (B ∪ A) ↓∩ A = univ := by
  rw [← set_restrict_union]
  simp only [set_restrict_self, union_univ]

@[simp]
lemma union_self_left_restrict: (A ∪ B) ↓∩ A = univ := by
  rw [← set_restrict_union]
  simp only [set_restrict_self, univ_union]

@[simp]
lemma restrict_subset_restrict_iff: B ↓∩ A ⊆ C ↓∩ A ↔ B ∩ A ⊆ C ∩ A := by
  constructor
  · rintro h x ⟨hxB,hxA⟩
    constructor
    · specialize h ?_
      · exact ⟨x,hxA⟩
      · exact hxB
      exact h
    · exact hxA
  · rintro h ⟨x,hxA⟩ hx
    specialize h ?_
    · exact x
    · exact ⟨hx,hxA⟩
    exact h.1

@[simp]
lemma restrict_eq_iff :  B ↓∩ A = C ↓∩ A ↔ B ∩ A = C ∩ A  := by
  simp only [subset_antisymm_iff, restrict_subset_restrict_iff, subset_inter_iff,
    inter_subset_right, and_true]

@[simp]
lemma set_restrict_sUnion: ⋃₀ {(B ↓∩ A) | B ∈ S} = (⋃₀ S) ↓∩ A := by
  ext x
  simp only [mem_sUnion, mem_setOf_eq, exists_exists_and_eq_and, mem_set_restrict_iff]

@[simp]
lemma set_restrict_iUnion: ⋃ (B : β), i B ↓∩ A = (⋃ (B : β ), i B) ↓∩ A := by
  ext x
  simp only [mem_iUnion, mem_set_restrict_iff]

@[simp]
lemma set_restrict_iInter: ⋂ (B : β), i B ↓∩ A = (⋂ (B : β ), i B) ↓∩ A := by
  ext x
  simp only [mem_iInter, mem_set_restrict_iff]

@[simp]
lemma set_restrict_sInter:  ⋂₀ {(B ↓∩ A) | B ∈ S} = (⋂₀ S) ↓∩ A := by
  ext x
  simp only [mem_sInter, mem_setOf_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    mem_set_restrict_iff]


end Subset
