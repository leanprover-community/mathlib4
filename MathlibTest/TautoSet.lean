/-
Copyright (c) 2025 Lenny Taelman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lenny Taelman
-/

import Mathlib.Tactic.TautoSet

variable {α : Type} {A B C D E : Set α}


example (h : B ∪ C ⊆ A ∪ A) : B ⊆ A := by tauto_set
example (h : B ∩ B ∩ C ⊇ A) : A ⊆ B := by tauto_set
example (hABC : A ⊆ B ∪ C) (hCD : C ⊆ D): A ⊆ B ∪ D := by tauto_set

example (h : A = Aᶜ) : B = ∅ := by tauto_set
example (h : A = Aᶜ) : B = C := by tauto_set

example (h : A ⊆ Aᶜ \ B) : A = ∅ := by tauto_set
example (h1 : A ⊆ B \ C) : A ⊆ B := by tauto_set

example (h : Set.univ ⊆ ((A ∪ B) ∩ C) ∩ ((Aᶜ ∩ Bᶜ) ∪ Cᶜ)) : D \ B ⊆ E ∩ Aᶜ := by tauto_set

example (h : A ∩ B ⊆ C) (h2 : C ∩ D ⊆ E) : A ∩ B ∩ D ⊆ E := by tauto_set
example (h : E = Aᶜᶜ ∩ Cᶜᶜᶜ ∩ D) : D ∩ (B ∪ Cᶜ) ∩ A = E ∪ (A ∩ Dᶜᶜ ∩ B)ᶜᶜ := by tauto_set
example (h : E ⊇ Aᶜᶜ ∩ Cᶜᶜᶜ ∩ D) : D ∩ (B ∪ Cᶜ) ∩ A ⊆  E ∪ (A ∩ Dᶜᶜ ∩ B)ᶜᶜ := by tauto_set

example (h1 : A = B) : A = B := by tauto_set
example (h1 : A = B) (h2 : B ⊆ C): A ⊆ C := by tauto_set

example (h1 : A ∩ B = Set.univ) : A = Set.univ := by tauto_set
example (h1 : A ∪ B = ∅) : A = ∅ := by tauto_set

example (h: Aᶜ ⊆ ∅) : A = Set.univ := by tauto_set
example (h: Set.univ ⊆ Aᶜ) : A = ∅ := by tauto_set

example : A ∩ ∅ = ∅ := by tauto_set
example : A ∪ Set.univ = Set.univ := by tauto_set

example : ∅ ⊆ A := by tauto_set
example : A ⊆ Set.univ := by tauto_set

example (hAB : A ⊆ B) (hBA: B ⊆ A) : A = B := by tauto_set

example : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by tauto_set
example : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by tauto_set
example : A ∩ (B ∪ C) ⊆ (A ∩ B) ∪ (A ∩ C) := by tauto_set

example : A ⊆ (A ∪ B) ∪ C := by tauto_set

example : A ∩ B ⊆ A := by tauto_set
example : A ⊆ A ∪ B := by tauto_set

example (hBA : B ⊆ A) (hB : Set.univ ⊆ B): Set.univ = A := by tauto_set

example (hAB : A ⊆ B) (hCD : C ⊆ D) : C \ B ⊆ D \ A := by tauto_set

example (hAB : Disjoint A B) (hCA : C ⊆ A) : Disjoint C (B \ D) := by tauto_set

example : Aᶜᶜᶜ = Aᶜ := by tauto_set
example : Aᶜᶜ = A := by tauto_set

example (hAB : A ⊆ B) (hBC : B ⊆ C) : A ⊆ C := by tauto_set

example : (Aᶜ ∩ B ∩ Cᶜᶜ)ᶜᶜᶜᶜᶜ = Cᶜ ∪ Bᶜ ∪ ∅ ∪ A ∪ ∅ := by tauto_set

example : D ∩ (B ∪ Cᶜ) ∩ A = (Aᶜᶜ ∩ Cᶜᶜᶜ ∩ D) ∪ (A ∩ Dᶜᶜ ∩ B)ᶜᶜ := by tauto_set

example (hAB : A ⊆ B) (hBC : B ⊆ C) (hCD : C ⊆ D) (hDE : D = E) (hEA : E ⊆ A) :
    (Aᶜ ∩ B ∪ (C ∩ Bᶜ)ᶜ ∩ (Eᶜ ∪ A))ᶜ ∩ (B ∪ Eᶜᶜ)ᶜ =
    (Dᶜ ∩ C ∪ (B ∩ Aᶜ)ᶜ ∩ (Eᶜ ∪ E))ᶜ ∩ (D ∪ Cᶜᶜ)ᶜ := by tauto_set



/-
  Examples from the Matroid Decomposition Theorem Verification,
  see https://github.com/Ivan-Sergeyev/seymour, and in particular
  https://github.com/Ivan-Sergeyev/seymour/blob/d8fcfa23336efe50b09fa0939e8a4ec3a5601ae9/Seymour/ForMathlib/SetTheory.lean
-/

-- setminus_inter_union_eq_union
example : A \ (A ∩ B) ∪ B = A ∪ B := by tauto_set

-- sub_parts_eq
example (hA : A ⊆ B ∪ C) : (A ∩ B) ∪ (A ∩ C) = A := by tauto_set

-- elem_notin_set_minus_singleton
example (a : α) : a ∉ A \ {a} := by tauto_set

-- sub_union_diff_sub_union
example (hA : A ⊆ B \ C) : A ⊆ B := by tauto_set

-- singleton_inter_subset_left
example (hAB : A ∩ B = {a}) : {a} ⊆ A := by tauto_set

-- singleton_inter_subset_right
example (hAB : A ∩ B = {a}) : {a} ⊆ B := by tauto_set

-- diff_subset_parent
example (hAB : A ⊆ C) : A \ B ⊆ C := by tauto_set

-- inter_subset_parent_left
example (hAC : A ⊆ C) : A ∩ B ⊆ C := by tauto_set

-- inter_subset_parent_right
example (hBC : B ⊆ C) : A ∩ B ⊆ C := by tauto_set

-- inter_subset_union
example : A ∩ B ⊆ A ∪ B := by tauto_set

-- subset_diff_empty_eq
example (hAB : A ⊆ B) (hBA : B \ A = ∅) : A = B := by tauto_set

-- Disjoint.ni_of_in
example (hAB : Disjoint A B) (ha : a ∈ A) : a ∉ B := by tauto_set

-- disjoint_of_singleton_inter_left_wo
example (hAB : A ∩ B = {a}) : Disjoint (A \ {a}) B := by tauto_set

-- disjoint_of_singleton_inter_right_wo
example (hAB : A ∩ B = {a}) : Disjoint A (B \ {a}) := by tauto_set

-- disjoint_of_singleton_inter_both_wo
example (hAB : A ∩ B = {a}) : Disjoint (A \ {a}) (B \ {a}) := by tauto_set

-- union_subset_union_iff
example (hAC : Disjoint A C) (hBC : Disjoint B C) :
    A ∪ C ⊆ B ∪ C ↔ A ⊆ B := by
  constructor <;> (intro; tauto_set)

-- symmDiff_eq_alt
example : symmDiff A B = (A ∪ B) \ (A ∩ B) := by tauto_set

-- symmDiff_disjoint_inter
example : Disjoint (symmDiff A B) (A ∩ B) := by tauto_set

-- symmDiff_empty_eq
example : symmDiff A ∅ = A := by tauto_set

-- empty_symmDiff_eq
example : symmDiff ∅ A = A := by tauto_set

-- symmDiff_subset_ground_right
example (hC : symmDiff A B ⊆ C) (hA : A ⊆ C) : B ⊆ C := by tauto_set

-- symmDiff_subset_ground_left
example (hC : symmDiff A B ⊆ C) (hB : B ⊆ C) : A ⊆ C := by tauto_set
