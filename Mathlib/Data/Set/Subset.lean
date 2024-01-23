/-
Copyright (c) 2024 Miguel Marco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel Marco
-/
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Functor
import Mathlib.Lean.Expr.ExtraRecognizers

/-!
# Subsets as subtypes

This file defines the function `set_restrict` that converts sets in a type, to sets in a subtype
(as the elements in the subtype whose lift lives in the set), and some notation and simplification
lemmas for convenience.

More precisely, given `α : Type` and `A : Set α`, `set_restrict A : Set α → Set A` takes
some `B : Set α` and produces some `Set ↑A` whose elements are `{ x : ↑A | ↑x ∈ B}`.

It also defines the notation `A ↓∩ B` for `set_restrict A B`.

## Implementation

The simplification lemmas are designed to simplify the expression appearing inside the `↓∩`
operation, if possible.

## Tags

subsets
-/

open Lean PrettyPrinter Delaborator SubExpr in
/--
Sets of a subtype coerced to the ambient type are denoted with `↑`.
-/
@[delab app.Set.image]
def delab_set_image_subtype : Delab := do
  let #[α, _, f, _] := (← getExpr).getAppArgs | failure
  guard <| f.isAppOfArity ``Subtype.val 2
  let some _ := α.coeTypeSet? | failure
  let e ← withAppArg delab
  `(↑$e)

open Set

universe u

variable {α β : Type u} {A B C: Set α} {D E : Set ↑A}
variable {S : Set (Set α)} {T : Set (Set ↑A)} {i : β → Set α} {j : β → Set ↑A}

namespace Subset

/--
Given two sets `A` and `B`, `set_restrict A B` is the set of `↑A` formed by the elements
whose value is in `B`.
-/
def set_restrict (A B : Set α) : Set ↑A := restrict A B

/--
`A ↓∩ B` denotes `restrict A B`.
-/
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
lemma set_restrict_union :  A ↓∩  (B ∪ C) = (A ↓∩ B) ∪ (A ↓∩ C) :=  rfl

@[simp]
lemma set_restrict_inter : A ↓∩ (B ∩ C) = (A ↓∩ B) ∩ (A ↓∩ C) :=  rfl

@[simp]
lemma set_restrit_compl : A ↓∩ Bᶜ = (A ↓∩ B)ᶜ  := by
  apply Eq.refl

lemma set_restrict_eq_univ_of_subset (h : A ⊆ B) : A ↓∩ B = univ := by
  ext x
  simp only [mem_set_restrict_iff, mem_univ, iff_true]
  exact h x.2

@[simp]
lemma restrict_subset_restrict_iff: A ↓∩ B ⊆ A ↓∩ C ↔ A ∩ B ⊆ A ∩ C := by
  constructor
  · rintro h x ⟨hxA,hxB⟩
    constructor
    · exact hxA
    · specialize h ?_
      · exact ⟨x,hxA⟩
      · exact hxB
      exact h
  · rintro h ⟨x,hxA⟩ hx
    specialize h ?_
    · exact x
    · exact ⟨hxA,hx⟩
    exact h.2

@[simp]
lemma set_restrict_eq_iff :  A ↓∩ B = A ↓∩ C ↔ A ∩ B = A ∩ C  := by
  simp only [subset_antisymm_iff, restrict_subset_restrict_iff, subset_inter_iff,
    inter_subset_right, and_true]

@[simp]
lemma set_restrict_diff : A ↓∩ (B \ C) = (A ↓∩ B) \ (A ↓∩ C) := by
  apply Eq.refl

@[simp]
lemma set_restrict_sUnion: A ↓∩ (⋃₀ S) = ⋃₀ {(A ↓∩ B) | B ∈ S} := by
  ext x
  simp only [mem_sUnion, mem_setOf_eq, exists_exists_and_eq_and, mem_set_restrict_iff]

@[simp]
lemma set_restrict_iUnion: A ↓∩ (⋃ (B : β ), i B) = ⋃ (B : β), A ↓∩ i B := by
  ext x
  simp only [mem_iUnion, mem_set_restrict_iff]

@[simp]
lemma set_restrict_iInter: A ↓∩ (⋂ (B : β ), i B) = ⋂ (B : β), A ↓∩ i B   := by
  ext x
  simp only [mem_iInter, mem_set_restrict_iff]

@[simp]
lemma set_restrict_sInter:  A ↓∩ (⋂₀ S)  = ⋂₀ {(A ↓∩ B) | B ∈ S} := by
  ext x
  simp only [mem_sInter, mem_setOf_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    mem_set_restrict_iff]

lemma eq_of_restrict_eq_of_subset (hB : B ⊆ A) (hC : C ⊆ A) (h : A ↓∩ B = A ↓∩ C) : B = C := by
  simp only [← inter_eq_right] at hB hC
  simp only [set_restrict_eq_iff,hB,hC] at h
  exact h

lemma restrict_mono (h : B ⊆ C) : A ↓∩ B ⊆ A ↓∩ C := by
  simp only [restrict_subset_restrict_iff, subset_inter_iff, inter_subset_left, true_and]
  apply subset_trans (inter_subset_right A B) h

lemma mem_coe_iff (x : α): x ∈  (↑D : Set α) ↔ ∃ y : ↑A, y ∈ D ∧ ↑y = x  := by rfl

/--
The following simp lemmas try to transform operations in the subtype into operations  in the ambient
type, if possible.
-/

lemma coe_univ : ↑(univ : Set A)  = A := by
  simp only [image_univ, Subtype.range_coe_subtype, setOf_mem_eq]

lemma coe_empty : ↑(∅ : Set A)  = (∅ : Set α ) := image_empty _

@[simp]
lemma coe_union : (↑(D ∪ E) : Set α)  = ↑D ∪ ↑E := by
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
lemma coe_inter : (↑(D ∩ E) : Set α) = ↑D  ∩ ↑E := by
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
lemma coe_compl : ↑(Dᶜ) = A \ ↑D := by
  unhygienic ext
  simp_all only [mem_image, mem_compl_iff, Subtype.exists, exists_and_right, exists_eq_right,
    mem_diff, not_exists]
  apply Iff.intro
  · intro a
    cases a
    simp_all only [not_false_eq_true, forall_true_left, and_self]
  · intro a
    simp_all only [not_false_eq_true, exists_const]

@[simp]
lemma coe_diff :  (↑(D \ E) : Set α) =  ↑D \ ↑E  := by
  ext
  simp_all only [mem_diff, mem_image, Subtype.exists, exists_and_right, exists_eq_right, not_exists]
  apply Iff.intro
  · intro a
    aesop_destruct_products
    simp_all only [exists_const, not_false_eq_true, forall_true_left, and_self]
  · intro a
    simp_all only [not_false_eq_true, and_true]

@[simp]
lemma coe_sUnion : ↑(⋃₀ T)  = ⋃₀ { (B : Set α) | B ∈ T} := by
  ext x
  simp_all only [mem_sUnion, mem_setOf_eq, exists_exists_and_eq_and, mem_image, Subtype.exists,
    exists_and_right, exists_eq_right]
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
lemma coe_iUnion : ↑(⋃ (B : β ), j B) = ⋃ (B : β), (j B : Set α) := image_iUnion

@[simp]
lemma coe_sInter (hT : ∃ L, L ∈ T) : (↑(⋂₀ T) : Set α) = ⋂₀ { (↑B : Set α) | B ∈ T}  := by
  ext x
  cases' hT with L hL
  apply Iff.intro
  · intro h
    simp_all only [mem_image, mem_sInter, Subtype.exists, exists_and_right, exists_eq_right,
      mem_setOf_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
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
      simp_all only [mem_sInter, mem_setOf_eq, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂, mem_image, Subtype.exists, exists_and_right, exists_eq_right,
       exists_true_left, implies_true, forall_const, exists_const]

@[simp]
lemma coe_iInter (b : β) : (↑(⋂ (B : β ), j B) : Set α) =  ⋂ (B : β), (↑(j B) : Set α) := by
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
    simp_all only [exists_true_left, mem_image, mem_iInter, Subtype.exists, exists_and_right,
      exists_eq_right, implies_true, exists_const]

lemma coe_contained : ↑D ⊆ A  := by
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
lemma coe_contained_iff : D ⊆ Subtype.val ⁻¹' ↑E ↔ D ⊆ E := by
  apply Iff.intro
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
lemma coe_eq_iff : (D : Set α) = ↑E ↔ D = E := by
  simp only [subset_antisymm_iff, image_subset_iff, coe_contained_iff]

lemma coe_inj (h : (↑D : Set α) = ↑E) : D = E := by
  simp only [coe_eq_iff] at h
  exact h

lemma coe_mono (h : (↑D : Set α) ⊆ ↑E) : D ⊆  E := by
  intro x hx
  specialize h _
  · exact ↑x
  · simp only [mem_image, Subtype.exists, exists_and_right, exists_eq_right, Subtype.coe_eta, hx,
    Subtype.coe_prop, exists_const]
  simp only [mem_image, Subtype.exists, exists_and_right, exists_eq_right, Subtype.coe_eta,
    Subtype.coe_prop, exists_const] at h
  exact h

/-
Relations between restriction and coercion.
-/

@[simp]
lemma set_restrict_coe_eq_self : A ↓∩ ↑D  = D := by
  ext x
  simp only [mem_set_restrict_iff, mem_image, Subtype.exists, exists_and_right, exists_eq_right,
    Subtype.coe_eta, Subtype.coe_prop, exists_const]

@[simp]
lemma coe_set_restrict_eq_inter : ↑(A ↓∩ B) = A ∩ B := by
  ext x
  simp only [mem_image, mem_set_restrict_iff, Subtype.exists, exists_and_left, exists_prop,
    exists_eq_right_right, mem_inter_iff]
  rw [and_comm]

lemma coe_set_restrict_subset_self : ↑(A ↓∩ B) ⊆ B  := by
  simp only [coe_set_restrict_eq_inter, inter_subset_right]

end Subset
