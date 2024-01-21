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

It also defines the notation `A ↓∩ B` for `set_restrict A B`.

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

def set_restrict (A B : Set α) : Set ↑A := restrict A B

infixl:67 " ↓∩ "  => set_restrict

@[simp]
lemma mem_set_restrict_iff (x : A): x ∈  (A ↓∩ B) ↔ ↑x ∈ B := by rfl

@[simp]
lemma set_restrict_empty : A ↓∩ (∅ : Set α) = (∅ : Set A) := rfl

@[simp]
lemma set_restrict_self : A ↓∩ A = univ := by
  ext x
  simp only [mem_set_restrict_iff, Subtype.coe_prop, mem_univ]

@[simp]
lemma set_restrict_univ : A ↓∩ (univ : Set α) = (univ : Set A) := rfl

@[simp]
lemma set_restrict_union : (A ↓∩ B) ∪ (A ↓∩ C) = A ↓∩  (B ∪ C) :=  rfl

@[simp]
lemma set_restrict_inter :  (A ↓∩ B) ∩ (A ↓∩ C) = A ↓∩ (B ∩ C) :=  rfl

@[simp]
lemma set_restrit_compl : (A ↓∩ B)ᶜ  = A ↓∩ Bᶜ := by
  apply Eq.refl

@[simp]
lemma set_inter_self_left_restrict : A ↓∩ (B ∩ A) = A ↓∩ B := by
  rw [← set_restrict_inter ]
  simp only [set_restrict_self, inter_univ]

@[simp]
lemma set_inter_self_right_restrict: A ↓∩ (A ∩ B) = A ↓∩ B := by
  rw [← set_restrict_inter ]
  simp only [set_restrict_self, univ_inter]

lemma set_restrict_eq_univ_of_subset (h : A ⊆ B) : A ↓∩ B = univ := by
  ext x
  simp only [mem_set_restrict_iff, mem_univ, iff_true]
  exact h x.2

@[simp]
lemma union_self_right_restrict: A ↓∩ (B ∪ A) = univ := by
  rw [← set_restrict_union]
  simp only [set_restrict_self, union_univ]

@[simp]
lemma union_self_left_restrict: A ↓∩ (A ∪ B) = univ := by
  rw [← set_restrict_union]
  simp only [set_restrict_self, univ_union]

@[simp]
lemma restrict_subset_restrict_iff: A ↓∩ B ⊆ A ↓∩ C ↔ B ∩ A ⊆ C ∩ A := by
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
lemma set_restrict_eq_iff :  A ↓∩ B = A ↓∩ C ↔ B ∩ A = C ∩ A  := by
  simp only [subset_antisymm_iff, restrict_subset_restrict_iff, subset_inter_iff,
    inter_subset_right, and_true]

@[simp]
lemma set_restrict_diff : (A ↓∩ B) \ (A ↓∩ C) = A ↓∩ (B \ C) := by
  apply Eq.refl

@[simp]
lemma set_restrict_sUnion: ⋃₀ {(A ↓∩ B) | B ∈ S} = A ↓∩ (⋃₀ S) := by
  ext x
  simp only [mem_sUnion, mem_setOf_eq, exists_exists_and_eq_and, mem_set_restrict_iff]

@[simp]
lemma set_restrict_iUnion: ⋃ (B : β), A ↓∩ i B = A ↓∩ (⋃ (B : β ), i B) := by
  ext x
  simp only [mem_iUnion, mem_set_restrict_iff]

@[simp]
lemma set_restrict_iInter: ⋂ (B : β), A ↓∩ i B = A ↓∩ (⋂ (B : β ), i B)  := by
  ext x
  simp only [mem_iInter, mem_set_restrict_iff]

@[simp]
lemma set_restrict_sInter:  ⋂₀ {(A ↓∩ B) | B ∈ S} = A ↓∩ (⋂₀ S)  := by
  ext x
  simp only [mem_sInter, mem_setOf_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    mem_set_restrict_iff]

instance coeToTypeSet : CoeOut (Set ↑A) (Set α) where
  coe := image Subtype.val


variable (D E : Set ↑A) (T : Set (Set ↑A)) (j : β → Set ↑A)

@[simp]
lemma mem_coeOut_iff (x : α): x ∈  (↑D : Set α) ↔ ∃ y : ↑A, y ∈ D ∧ ↑y = x  := by rfl

@[simp]
lemma coeOut_univ : ↑(univ : Set A)  = A := by
  simp only [image_univ, Subtype.range_coe_subtype, setOf_mem_eq]


/-
The following simp lemmas try to transform expressions into operations performed in the ambient
type.
-/

@[simp]
lemma coeOut_empty : ↑(∅ : Set A)  = (∅ : Set α ) := image_empty _


@[simp]
lemma coeOut_union : ↑(D ∪ E)  = (↑D : Set α) ∪ ↑E := by
  ext x
  simp_all only [mem_union, mem_image, Subtype.exists, exists_and_right, exists_eq_right]
  apply Iff.intro
  · intro a
    aesop_destruct_products
    simp_all only [exists_true_left]
  · intro a
    cases a
    · aesop_destruct_products
      simp_all only [true_or, exists_const]
    · aesop_destruct_products
      simp_all only [or_true, exists_const]

@[simp]
lemma coeOut_inter : ↑(D ∩ E) = (↑D : Set α) ∩ ↑E := by
  ext
  simp_all only [mem_inter_iff, mem_image, Subtype.exists, exists_and_right, exists_eq_right]
  apply Iff.intro
  · intro a
    aesop_destruct_products
    simp_all only [and_self, exists_const]
  · intro a
    aesop_destruct_products
    simp_all only [exists_const, and_self]

@[simp]
lemma coeOut_compl : ↑(Dᶜ) = A \ ↑D := by
  unhygienic ext
  simp_all only [mem_image, mem_compl_iff, Subtype.exists, exists_and_right, exists_eq_right, mem_diff, not_exists]
  apply Iff.intro
  · intro a
    cases a
    simp_all only [not_false_eq_true, forall_true_left, and_self]
  · intro a
    simp_all only [not_false_eq_true, exists_const]

@[simp]
lemma coeOut_diff : (D \ E) = (D : Set α) \ ↑E  := by
  ext
  simp_all only [mem_diff, mem_image, Subtype.exists, exists_and_right, exists_eq_right, not_exists]
  apply Iff.intro
  · intro a
    aesop_destruct_products
    simp_all only [exists_const, not_false_eq_true, forall_true_left, and_self]
  · intro a
    simp_all only [not_false_eq_true, and_true]

@[simp]
lemma coeOut_sUnion : ↑(⋃₀ T)  = ⋃₀ { (B : Set α) | B ∈ T} := by
  ext x
  simp_all only [mem_sUnion, mem_setOf_eq, exists_exists_and_eq_and, mem_image, Subtype.exists, exists_and_right,
    exists_eq_right]
  apply Iff.intro
  · intro a
    unhygienic with_reducible aesop_destruct_products
    simp_all only [exists_true_left]
    apply Exists.intro
    apply And.intro
    on_goal 2 => exact right
    simp_all only
  · intro a
    unhygienic with_reducible aesop_destruct_products
    simp_all only [exists_true_left]
    apply Exists.intro
    apply And.intro
    exact left
    simp_all only


@[simp]
lemma coeOut_iUnion : ↑(⋃ (B : β ), j B) = ⋃ (B : β), (j B : Set α) := by
  unhygienic ext
  simp_all only [mem_iUnion, mem_image, Subtype.exists, exists_and_right, exists_eq_right]
  apply Iff.intro
  · intro a
    unhygienic with_reducible aesop_destruct_products
    simp_all only [exists_true_left]
    apply Exists.intro
    exact h_1
  · intro a
    unhygienic with_reducible aesop_destruct_products
    simp_all only [exists_true_left]
    apply Exists.intro
    exact h_1

@[simp]
lemma coeOut_sInter (hT : ∃ L, L ∈ T) : ↑(⋂₀ T) = ⋂₀ { (B : Set α) | B ∈ T}  := by
  ext x
  cases' hT with L hL
  apply Iff.intro
  · intro h
    simp_all only [mem_image, mem_sInter, Subtype.exists, exists_and_right, exists_eq_right, mem_setOf_eq,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro a a_1
    unhygienic with_reducible aesop_destruct_products
    simp_all only [exists_const]
  · intro h
    have haux : x ∈ (L : Set α)
    · simp only [mem_sInter, mem_setOf_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      mem_image, Subtype.exists, exists_and_right, exists_eq_right] at h
      specialize h L hL
      cases' h with y hy
      use ⟨x,y⟩
    · simp only [mem_image, mem_sInter, Subtype.exists, exists_and_right, exists_eq_right]
      rcases haux with ⟨⟨y,hyA⟩ ,⟨_,rfl⟩⟩
      simp_all only [mem_sInter, mem_setOf_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, mem_image,
        Subtype.exists, exists_and_right, exists_eq_right, exists_true_left, implies_true, forall_const, exists_const]

@[simp]
lemma coeOut_iInter (b : β) : ↑(⋂ (B : β ), j B) =  ⋂ (B : β), (j B : Set α)  := by
  ext x
  apply Iff.intro
  · intro a
    simp_all only [mem_image, mem_iInter, Subtype.exists, exists_and_right, exists_eq_right]
    intro i_1
    unhygienic with_reducible aesop_destruct_products
    simp_all only [exists_const]
  · intro h
    simp only [mem_iInter, mem_image, Subtype.exists, exists_and_right, exists_eq_right] at h
    have hb := h b
    cases' hb with hxA hx
    simp_all only [exists_true_left, mem_image, mem_iInter, Subtype.exists, exists_and_right, exists_eq_right,
      implies_true, exists_const]

lemma coeOut_contained : ↑D ⊆ A  := by
  simp only [image_subset_iff, Subtype.coe_preimage_self, subset_univ]

@[simp]
lemma coueOut_union_self_right : A ∪ ↑D = A := by
  simp only [union_eq_left, image_subset_iff, Subtype.coe_preimage_self, subset_univ]

@[simp]
lemma coueOut_union_self_left :↑D ∪ A = A := by
  simp only [union_eq_right, image_subset_iff, Subtype.coe_preimage_self, subset_univ]

@[simp]
lemma coueOut_inter_self_right : A ∩ ↑D = ↑D := by
  simp only [inter_eq_right, image_subset_iff, Subtype.coe_preimage_self, subset_univ]

@[simp]
lemma coueOut_inter_self_left : ↑D ∩ A = ↑D := by
  simp only [inter_eq_left, image_subset_iff, Subtype.coe_preimage_self, subset_univ]

@[simp]
lemma coeOut_contained_iff : (D : Set α ) ⊆ ↑E ↔ D ⊆ E := by
  apply Iff.intro
  · intro h x hx
    simp only [image_subset_iff] at h
    specialize h hx
    simp only [mem_preimage, mem_image, Subtype.exists, exists_and_right, exists_eq_right,
      Subtype.coe_eta, Subtype.coe_prop, exists_const] at h
    exact h
  · intro h x hx
    simp_all only [mem_image, Subtype.exists, exists_and_right, exists_eq_right]
    aesop_destruct_products
    simp_all only [exists_true_left]
    apply h
    simp_all only

@[simp]
lemma coeOut_eq_iff : (D : Set α ) = ↑E ↔ D = E := by
  simp only [subset_antisymm_iff,coeOut_contained_iff]

@[simp]
lemma set_restrict_coeOut_eq_self : A ↓∩ ↑D  = D := by
  ext x
  simp only [mem_set_restrict_iff, mem_image, Subtype.exists, exists_and_right, exists_eq_right,
    Subtype.coe_eta, Subtype.coe_prop, exists_const]

@[simp]
lemma coeOut_set_restrict_eq_inter : ↑(A ↓∩ B) = A ∩ B := by
  ext x
  simp only [mem_image, mem_set_restrict_iff, Subtype.exists, exists_and_left, exists_prop,
    exists_eq_right_right, mem_inter_iff]
  rw [and_comm]

lemma coeOut_set_restrict_subset_self : ↑(A ↓∩ B) ⊆ B  := by
  simp only [coeOut_set_restrict_eq_inter, inter_subset_right]

@[simp]
lemma set_restrict_of_inter_of_coe_left : A ↓∩ (↑D ∩ B) = D ∩ (A ↓∩ B ) := by
  ext x
  simp only [mem_set_restrict_iff, mem_inter_iff, mem_image, Subtype.exists, exists_and_right,
    exists_eq_right, Subtype.coe_eta, Subtype.coe_prop, exists_const]

@[simp]
lemma set_restrict_of_inter_of_coe_right : A ↓∩ (B ∩ ↑D) = (A ↓∩ B) ∩ D := by
  ext x
  simp only [mem_set_restrict_iff, mem_inter_iff, mem_image, Subtype.exists, exists_and_right,
    exists_eq_right, Subtype.coe_eta, Subtype.coe_prop, exists_const]

@[simp]
lemma set_restrict_of_union_of_coe_left : A ↓∩ (↑D ∪ B) = D ∪ (A ↓∩ B ) := by
  ext x
  simp only [mem_set_restrict_iff, mem_union, mem_image, Subtype.exists, exists_and_right,
    exists_eq_right, Subtype.coe_eta, Subtype.coe_prop, exists_const]

@[simp]
lemma set_restrict_of_union_of_coe_right : A ↓∩ (B ∪ ↑D) = (A ↓∩ B ) ∪ D := by
  ext x
  simp only [mem_set_restrict_iff, mem_union, mem_image, Subtype.exists, exists_and_right,
    exists_eq_right, Subtype.coe_eta, Subtype.coe_prop, exists_const]


end Subset
