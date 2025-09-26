/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Order.Concept
import Mathlib.Order.UpperLower.CompleteLattice

/-!
# Dedekind-MacNeille completion

The Dedekind-MacNeille completion of a partial order is the smallest complete lattice into which it
embeds.

The theory of concept lattices allows for a simple construction. In fact, `DedekindCut α` is simply
an abbreviation for `Concept α α (· ≤ ·)`. This means we don't need to reprove that this is a
complete lattice; instead, the file simply proves that any order embedding into another complete
lattice factors through it.

## Todo

- Build the order isomorphism `DedekindCut ℚ ≃o ℝ`.
-/

open Concept Set

variable {α β γ : Type*} [Preorder α] [PartialOrder β] [CompleteLattice γ]

variable (α) in
/-- The **Dedekind-MacNeille completion** of a partial order is the smallest complete lattice that
contains it. We define here the type of Dedekind cuts of `α` as the `Concept` lattice of the `≤`
relation of `α`.

For `A : DedekindCut α`, the sets `A.left` and `A.right` are related by
`upperBounds A.left = A.right` and `lowerBounds A.right = A.left`.

The file `Order.Dedekind` proves that if `α` is a partial order and `β` is a complete lattice, any
embedding `α ↪o β` factors through `DedekindCut α`. -/
abbrev DedekindCut := Concept α α (· ≤ ·)

namespace DedekindCut

/-- The left set of a Dedekind cut. This is an alias for `Concept.extent`. -/
abbrev left (A : DedekindCut α) : Set α := A.extent

/-- The right set of a Dedekind cut. This is an alias for `Concept.intent`. -/
abbrev right (A : DedekindCut α) : Set α := A.intent

/-- See `DedekindCut.ext'` for a version using the right set. -/
@[ext] theorem ext {A B : DedekindCut α} (h : A.left = B.left) : A = B := Concept.ext h

/-- See `DedekindCut.ext` for a version using the left set. -/
theorem ext' {A B : DedekindCut α} (h : A.right = B.right) : A = B := Concept.ext' h

@[simp]
theorem upperBounds_left (A : DedekindCut α) : upperBounds A.left = A.right :=
  A.upperPolar_extent

@[simp]
theorem lowerBounds_right (A : DedekindCut α) : lowerBounds A.right = A.left :=
  A.lowerPolar_intent

theorem image_left_subset_lowerBounds {β : Type*} [Preorder β] {f : α → β} (hf : Monotone f)
    (A : DedekindCut α) : f '' A.left ⊆ lowerBounds (f '' A.right) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact hf <| rel_extent_intent hx hy

theorem image_right_subset_upperBounds {β : Type*} [Preorder β] {f : α → β} (hf : Monotone f)
    (A : DedekindCut α) : f '' A.right ⊆ upperBounds (f '' A.left) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact hf <| rel_extent_intent hy hx

/-- Convert an element into its Dedekind cut (`Iic a`, `Ici a`). This map is order-preserving,
though it is injective only on partial orders. -/
def of (a : α) : DedekindCut α :=
  (Concept.ofObject _ a).copy
    (Iic a) (by ext; simpa [mem_lowerPolar_iff] using forall_ge_iff_le.symm)
    (Ici a) (by ext; simp)

@[simp] theorem left_of (a : α) : (of a).left = Iic a := rfl
@[simp] theorem right_of (a : α) : (of a).right = Ici a := rfl

@[simp] theorem ofObject_eq_of (a : α) : ofObject (· ≤ ·) a = of a := (copy_eq ..).symm
@[simp] theorem ofAttribute_eq_of (a : α) : ofAttribute (· ≤ ·) a = of a := by ext; simp

@[simp]
theorem of_le_of {a b : α} : of a ≤ of b ↔ a ≤ b := by
  simpa using ofObject_le_ofAttribute_iff (r := (· ≤ ·)) (a := a)

@[simp]
theorem of_lt_of {a b : β} : of a < of b ↔ a < b := by
  simp [lt_iff_le_not_ge]

@[simp]
theorem of_inj {a b : β} : of a = of b ↔ a = b := by
  simp [le_antisymm_iff]

/-- `DedekindCut.of` as an `OrderEmbedding`. -/
@[simps! apply]
def ofEmbedding : β ↪o DedekindCut β where
  toFun := of
  inj' _ _ := of_inj.1
  map_rel_iff' := of_le_of

@[simp] theorem ofEmbedding_coe : ⇑(@ofEmbedding β _) = of := rfl

@[simp]
theorem of_sSup (A : DedekindCut γ) : of (sSup A.left) = A := by
  apply ext'
  ext
  rw [right_of, mem_Ici, sSup_le_iff, ← upperBounds_left, mem_upperBounds]

@[simp]
theorem of_sInf (A : DedekindCut γ) : of (sInf A.right) = A := by
  ext
  rw [left_of, mem_Iic, le_sInf_iff, ← lowerBounds_right, mem_lowerBounds]

/-- Any order embedding `β ↪o γ` into a complete lattice factors through `DedekindCut β`.

This map is defined so that `factorEmbedding f A = sSup (f '' A.left)`. Although the construction
`factorEmbedding f A = sInf (f '' A.right)` would also work, these do **not** in general give equal
embeddings. -/
def factorEmbedding (f : β ↪o γ) : DedekindCut β ↪o γ :=
  .ofMapLEIff (fun A ↦ sSup (f '' A.left)) <| by
    refine fun A B ↦ ⟨fun h x hx ↦ ?_, fun h ↦ sSup_le_sSup (image_mono h)⟩
    simp_rw [← lowerBounds_right]
    simp_rw [le_sSup_iff, sSup_le_iff, forall_mem_image] at h
    intro y hy
    rw [← f.le_iff_le]
    exact h _ (image_right_subset_upperBounds f.monotone _ (mem_image_of_mem _ hy)) hx

theorem factorEmbedding_apply (f : β ↪o γ) (A : DedekindCut β) :
    factorEmbedding f A = sSup (f '' A.left) :=
  rfl

@[simp]
theorem factorEmbedding_ofElement (f : β ↪o γ) (x : β) : factorEmbedding f (of x) = f x := by
  rw [factorEmbedding_apply]
  apply le_antisymm (by simp)
  rw [le_sSup_iff]
  refine fun y hy ↦ hy ?_
  simp

/-- The Dedekind-MacNeille completion of a partial order is the smallest complete lattice containing
it, in the sense that any embedding into any complete lattice factors through it. -/
theorem factorEmbedding_factors (f : β ↪o γ) :
    ofEmbedding.trans (factorEmbedding f) = f := by
  ext; simp

/-- `DedekindCut.of` as an `OrderIso`.

This provides the second half of the **fundamental theorem of concept lattices**: every complete
lattice is isomorphic to a concept lattice. -/
@[simps! apply]
def ofIso : γ ≃o DedekindCut γ where
  invFun := factorEmbedding (OrderIso.refl _).toOrderEmbedding
  left_inv := factorEmbedding_ofElement _
  right_inv x := by simp [factorEmbedding]
  __ := ofEmbedding

theorem ofIso_symm_apply (A : DedekindCut γ) : ofIso.symm A = sSup A.left :=
  (factorEmbedding_apply ..).trans <| by simp

noncomputable instance : DecidableLE (DedekindCut α) :=
  Classical.decRel _

variable {α : Type*} [LinearOrder α]

instance : IsTotal (DedekindCut α) (· ≤ ·) where
  total x y := le_total (α := LowerSet α) ⟨_, isLowerSet_extent_le x⟩ ⟨_, isLowerSet_extent_le y⟩

noncomputable instance : LinearOrder (DedekindCut α) where
  min_def x y := congrFun₂ inf_eq_minDefault x y
  max_def x y := congrFun₂ sup_eq_maxDefault x y
  le_total := total_of _
  toDecidableLE := inferInstance

noncomputable instance : CompleteLinearOrder (DedekindCut α) where
  __ := inferInstanceAs (LinearOrder _)
  __ := inferInstanceAs (CompleteLattice _)
  __ := LinearOrder.toBiheytingAlgebra _

end DedekindCut
