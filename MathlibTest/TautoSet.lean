/-
Copyright (c) 2025 Lenny Taelman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lenny Taelman
-/

import Mathlib.Tactic.TautoSet

variable (α : Type) (A B C D E : Set α)


example (h : B ∪ C ⊆ A ∪ A) : B ⊆ A := by tauto_set
example (h: B ∩ B ∩ C ⊇ A) : A ⊆ B := by tauto_set
example (h1 : A ⊆ B ∪ C) (h2 : C ⊆ D): A ⊆ B ∪ D := by tauto_set

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

example (h1 : Aᶜ ⊆ ∅) : A = Set.univ := by tauto_set
example (h1: Set.univ ⊆ Aᶜ) : A = ∅ := by tauto_set

example : A ∩ ∅ = ∅ := by tauto_set
example : A ∪ Set.univ = Set.univ := by tauto_set

example : ∅ ⊆ A := by tauto_set
example : A ⊆ Set.univ := by tauto_set

example (h1 : A ⊆ B) (h2: B ⊆ A) : A = B := by tauto_set

example : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by tauto_set
example : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by tauto_set
example : A ∩ (B ∪ C) ⊆ (A ∩ B) ∪ (A ∩ C) := by tauto_set

example : A ⊆ (A ∪ B) ∪ C := by tauto_set

example : A ∩ B ⊆ A := by tauto_set
example : A ⊆ A ∪ B := by tauto_set

example (h1 : B ⊆ A) (h2 : Set.univ ⊆ B): Set.univ = A := by tauto_set

example (h1 : A ⊆ B) (h2 : C ⊆ D) : C \ B ⊆ D \ A := by tauto_set

example (h1 : Disjoint A B) (h2 : C ⊆ A) : Disjoint C (B \ D) := by tauto_set

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
example {X Y : Set α} : X \ (X ∩ Y) ∪ Y = X ∪ Y := by tauto_set

-- sub_parts_eq
example {A E₁ E₂ : Set α} (hA : A ⊆ E₁ ∪ E₂) : (A ∩ E₁) ∪ (A ∩ E₂) = A := by tauto_set

-- elem_notin_set_minus_singleton
example (a : α) (X : Set α) : a ∉ X \ {a} := by tauto_set

-- sub_union_diff_sub_union
example {A B C : Set α} (hA : A ⊆ B \ C) : A ⊆ B := by tauto_set

-- singleton_inter_subset_left
example {X Y : Set α} {a : α} (ha : X ∩ Y = {a}) : {a} ⊆ X := by tauto_set

-- singleton_inter_subset_right
example {X Y : Set α} {a : α} (ha : X ∩ Y = {a}) : {a} ⊆ Y := by tauto_set

-- diff_subset_parent
example {X₁ X₂ E : Set α} (hX₁E : X₁ ⊆ E) : X₁ \ X₂ ⊆ E := by tauto_set

-- inter_subset_parent_left
example {X₁ X₂ E : Set α} (hX₁E : X₁ ⊆ E) : X₁ ∩ X₂ ⊆ E := by tauto_set

-- inter_subset_parent_right
example {X₁ X₂ E : Set α} (hX₂E : X₂ ⊆ E) : X₁ ∩ X₂ ⊆ E := by tauto_set

-- inter_subset_union
example {X₁ X₂ : Set α} : X₁ ∩ X₂ ⊆ X₁ ∪ X₂ := by tauto_set

-- subset_diff_empty_eq
example {A B : Set α} (hAB : A ⊆ B) (hBA : B \ A = ∅) : A = B := by tauto_set

-- Disjoint.ni_of_in
example {X Y : Set α} {a : α} (hXY : Disjoint X Y) (ha : a ∈ X) :
    a ∉ Y := by tauto_set

-- disjoint_of_singleton_inter_left_wo
example {X Y : Set α} {a : α} (hXY : X ∩ Y = {a}) :
    Disjoint (X \ {a}) Y := by tauto_set

-- disjoint_of_singleton_inter_right_wo
example {X Y : Set α} {a : α} (hXY : X ∩ Y = {a}) :
    Disjoint X (Y \ {a}) := by tauto_set

-- disjoint_of_singleton_inter_both_wo
example {X Y : Set α} {a : α} (hXY : X ∩ Y = {a}) :
    Disjoint (X \ {a}) (Y \ {a}) := by tauto_set

-- union_subset_union_iff
example {A B X : Set α} (hAX : Disjoint A X) (hBX : Disjoint B X) :
    A ∪ X ⊆ B ∪ X ↔ A ⊆ B := by
  constructor
  · intro h; tauto_set
  · intro h; tauto_set

-- symmDiff_eq_alt
example (X Y : Set α) : symmDiff X Y = (X ∪ Y) \ (X ∩ Y) := by tauto_set

-- symmDiff_disjoint_inter
example (X Y : Set α) : Disjoint (symmDiff X Y) (X ∩ Y) := by tauto_set

-- symmDiff_empty_eq
example (X : Set α) : symmDiff X ∅ = X := by tauto_set

-- empty_symmDiff_eq
example (X : Set α) : symmDiff ∅ X = X := by tauto_set

-- symmDiff_subset_ground_right
example {X Y E : Set α} (hE : symmDiff X Y ⊆ E) (hX : X ⊆ E) : Y ⊆ E := by tauto_set

-- symmDiff_subset_ground_left
example {X Y E : Set α} (hE : symmDiff X Y ⊆ E) (hX : Y ⊆ E) : X ⊆ E := by tauto_set
