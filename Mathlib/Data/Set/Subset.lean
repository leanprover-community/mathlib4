/-
Copyright (c) 2024 Miguel Marco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel Marco
-/
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Functor

/-!
# Sets in subtypes

This file is about sets in `Set A` when `A` is a set.

It defines notation `↓∩` for sets in a type pulled down to sets in a subtype, as an inverse
operation to the coercion that lifts sets in a subtype up to sets in the ambient type.

This module also provides lemmas for `↓∩` and this coercion.

## Notation

Let `α` be a `Type`, `A B : Set α` two sets in `α`, and `C : Set A` a set in the subtype `↑A`.

- `A ↓∩ B` denotes `(Subtype.val ⁻¹' B : Set A)` (that is, `{x : ↑A | ↑x ∈ B}`).
- `↑C` denotes `Subtype.val '' C` (that is, `{x : α | ∃ y ∈ C, ↑y = x}`).

This notation, (together with the `↑` notation for `Set.CoeHead` in `Mathlib.Data.Set.Functor`)
is scoped to the `Set.Notation` namespace.
To enable it, use `open Set.Notation`.


## Naming conventions

Theorem names refer to `↓∩` as `preimage_val`.

## Tags

subsets
-/

open Set

universe u

variable {α β : Type u} {A B C : Set α} {D E : Set A}
variable {S : Set (Set α)} {T : Set (Set A)} {i : β → Set α} {j : β → Set A}

namespace Set.Notation

/--
Given two sets `A` and `B`, `A ↓∩ B` denotes the intersection of `A` and `B` as a set in `Set A`.

The notation is short for `((↑) ⁻¹' B : Set A)`, while giving hints to the elaborator
that both `A` and `B` are terms of `Set α` for the same `α`.
This set is the same as `{x : ↑A | ↑x ∈ B}`.
-/
scoped notation3 A:67 " ↓∩ " B:67 => (Subtype.val ⁻¹' (B : type_of% A) : Set (A : Set _))

end Set.Notation

namespace Set

open Notation

lemma preimage_val_eq_univ_of_subset (h : A ⊆ B) : A ↓∩ B = univ := by
  ext x
  simp only [mem_univ, iff_true]
  exact h x.2

lemma preimage_val_subset_preimage_val_iff : A ↓∩ B ⊆ A ↓∩ C ↔ A ∩ B ⊆ A ∩ C := by
  constructor
  · rintro h x ⟨hxA, hxB⟩
    constructor
    · exact hxA
    · specialize h ?_
      · exact ⟨x, hxA⟩
      · exact hxB
      exact h
  · rintro h ⟨x, hxA⟩ hx
    specialize h ?_
    · exact x
    · exact ⟨hxA, hx⟩
    exact h.2

lemma preimage_val_eq_iff : A ↓∩ B = A ↓∩ C ↔ A ∩ B = A ∩ C := by
  rw [Subtype.preimage_val_eq_preimage_val_iff, inter_comm _ A, inter_comm _ A]

lemma preimage_val_sUnion : A ↓∩ (⋃₀ S) = ⋃₀ { (A ↓∩ B) | B ∈ S } := by
  ext x
  simp only [preimage_sUnion, mem_iUnion, mem_preimage, exists_prop, mem_sUnion, mem_setOf_eq,
    exists_exists_and_eq_and]

@[simp]
lemma preimage_val_iInter : A ↓∩ (⋂ (B : β), i B) = ⋂ (B : β), A ↓∩ i B := preimage_iInter

lemma preimage_val_sInter : A ↓∩ (⋂₀ S) = ⋂₀ { (A ↓∩ B) | B ∈ S } := by
  ext x
  simp only [preimage_sInter, mem_iInter, mem_preimage, mem_sInter, mem_setOf_eq,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

lemma eq_of_preimage_val_eq_of_subset (hB : B ⊆ A) (hC : C ⊆ A) (h : A ↓∩ B = A ↓∩ C) : B = C := by
  simp only [← inter_eq_right] at hB hC
  simp only [preimage_val_eq_iff, hB, hC] at h
  exact h

/-!
The following simp lemmas try to transform operations in the subtype into operations in the ambient
type, if possible.
-/

lemma image_val_univ : ↑(univ : Set A) = A := by
  simp only [image_univ, Subtype.range_coe_subtype, setOf_mem_eq]

lemma image_val_empty : ↑(∅ : Set A) = (∅ : Set α) := image_empty _

@[simp]
lemma image_val_union : (↑(D ∪ E) : Set α) = ↑D ∪ ↑E := image_union _ _ _

@[simp]
lemma image_val_inter : (↑(D ∩ E) : Set α) = ↑D ∩ ↑E := image_inter Subtype.val_injective

@[simp]
lemma image_val_compl : ↑(Dᶜ) = A \ ↑D := by
  ext
  simp_all only [mem_image, mem_compl_iff, Subtype.exists, exists_and_right, exists_eq_right,
    mem_diff, not_exists]
  constructor
  · rintro ⟨_⟩
    simp_all only [not_false_eq_true, forall_true_left, and_self]
  · intro a
    simp_all only [not_false_eq_true, exists_const]

@[simp]
lemma image_val_diff : (↑(D \ E) : Set α) = ↑D \ ↑E := image_diff Subtype.val_injective _ _

@[simp]
lemma image_val_sUnion : ↑(⋃₀ T) = ⋃₀ { (B : Set α) | B ∈ T} := by
  ext x
  simp_all only [mem_sUnion, mem_setOf_eq, exists_exists_and_eq_and, mem_image, Subtype.exists,
    exists_and_right, exists_eq_right]
  constructor
  · rintro ⟨hxA, D, hDT, hxD⟩
    exact ⟨D, hDT, hxA, hxD⟩
  · rintro ⟨D, hDT, hxA, hxD⟩
    exact ⟨hxA, D, hDT, hxD⟩

@[simp]
lemma image_val_iUnion : ↑(⋃ (B : β), j B) = ⋃ (B : β), (j B : Set α) := image_iUnion

@[simp]
lemma image_val_sInter (hT : T.Nonempty) : (↑(⋂₀ T) : Set α) = ⋂₀ { (↑B : Set α) | B ∈ T } := by
  ext x
  cases' hT with L hL
  constructor
  · intro h
    simp_all only [mem_image, mem_sInter, Subtype.exists, exists_and_right, exists_eq_right,
      mem_setOf_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro a a_1
    rcases h with ⟨_, _⟩
    simp_all only [exists_const]
  · intro h
    have haux : x ∈ (L : Set α)
    · simp only [mem_sInter, mem_setOf_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
        mem_image, Subtype.exists, exists_and_right, exists_eq_right] at h
      specialize h L hL
      cases' h with y hy
      use ⟨x, y⟩
    · simp only [mem_image, mem_sInter, Subtype.exists, exists_and_right, exists_eq_right]
      rcases haux with ⟨⟨y, hyA⟩, ⟨_, rfl⟩⟩
      simp_all only [mem_sInter, mem_setOf_eq, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂, mem_image, Subtype.exists, exists_and_right, exists_eq_right,
        exists_true_left, implies_true, forall_const, exists_const]

@[simp]
lemma image_val_iInter [Nonempty β] : (↑(⋂ (B : β), j B) : Set α) = ⋂ (B : β), (↑(j B) : Set α) :=
  (Subtype.val_injective.injOn _).image_iInter_eq

lemma image_val_subset_set : ↑D ⊆ A := by
  simp only [image_subset_iff, Subtype.coe_preimage_self, subset_univ]

@[simp]
lemma image_val_union_self_right_eq : A ∪ ↑D = A := by
  simp only [union_eq_left, image_subset_iff, Subtype.coe_preimage_self, subset_univ]

@[simp]
lemma image_val_union_self_left_eq : ↑D ∪ A = A := by
  simp only [union_eq_right, image_subset_iff, Subtype.coe_preimage_self, subset_univ]

@[simp]
lemma cou_inter_self_right_eq_coe : A ∩ ↑D = ↑D := by
  simp only [inter_eq_right, image_subset_iff, Subtype.coe_preimage_self, subset_univ]

@[simp]
lemma image_val_inter_self_left_eq_coe : ↑D ∩ A = ↑D := by
  simp only [inter_eq_left, image_subset_iff, Subtype.coe_preimage_self, subset_univ]

@[simp]
lemma subset_preimage_val_image_val_iff : D ⊆ A ↓∩ ↑E ↔ D ⊆ E := by
  constructor
  · intro h x hx
    simp only [image_subset_iff] at h
    specialize h hx
    simp only [mem_preimage, mem_image, Subtype.exists, exists_and_right, exists_eq_right,
      Subtype.coe_eta, Subtype.coe_prop, exists_const] at h
    exact h
  · intro h x hx
    simp only [mem_preimage, mem_image, Subtype.exists, exists_and_right, exists_eq_right,
      Subtype.coe_eta, Subtype.coe_prop, exists_const]
    exact h hx

@[simp]
lemma image_val_eq_iff : (D : Set α) = ↑E ↔ D = E := by
  simp only [subset_antisymm_iff, image_subset_iff, subset_preimage_val_image_val_iff]

lemma image_val_inj (h : (↑D : Set α) = ↑E) : D = E := by
  rw [image_val_eq_iff] at h
  exact h

lemma subset_of_image_val_subset_image_val (h : (↑D : Set α) ⊆ ↑E) : D ⊆ E := by
  simp_all only [image_subset_iff, subset_preimage_val_image_val_iff]

@[mono]
lemma image_val_mono (h : D ⊆ E) : (↑D : Set α) ⊆ ↑E := by
  simp only [image_subset_iff, subset_preimage_val_image_val_iff, h]

/-!
Relations between restriction and coercion.
-/

lemma image_val_preimage_val_subset_self : ↑(A ↓∩ B) ⊆ B := by
  simp only [Subtype.image_preimage_coe, inter_subset_left]

end Set
