/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Order.Concept

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

/-- The left set of a Dedekind cut. -/
abbrev left (A : DedekindCut α) : Set α := A.extent

/-- The right set of a Dedekind cut. -/
abbrev right (A : DedekindCut α) : Set α := A.intent

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

@[simp] theorem left_of (a : α) : (of a).left = Iic a := rfl
@[simp] theorem right_of (a : α) : (of a).right = Ici a := rfl

#exit
@[simp]
theorem ofElement_le_ofElement {a b : α} : ofElement a ≤ ofElement b ↔ a ≤ b := by
  simp [← fst_subset_fst_iff]

@[simp]
theorem ofElement_lt_ofElement {a b : β} : ofElement a < ofElement b ↔ a < b := by
  simp [lt_iff_le_not_ge]

@[simp]
theorem ofElement_inj {a b : β} : ofElement a = ofElement b ↔ a = b := by
  simp [le_antisymm_iff]

/-- `DedekindCut.ofElement` as an `OrderEmbedding`. -/
@[simps!]
def ofElementEmbedding : β ↪o DedekindCut β where
  toFun := ofElement
  inj' _ _ := ofElement_inj.1
  map_rel_iff' := ofElement_le_ofElement

@[simp] theorem ofElementEmbedding_coe : ⇑(@ofElementEmbedding β _) = ofElement := rfl

/-- Any order embedding `β ↪o γ` into a complete lattice factors through `DedekindCut β`.

This map is defined so that `factorEmbedding f A = sSup (f '' A.fst)`. Although the construction
`factorEmbedding f A = sInf (f '' A.snd)` would also work, these do **not** in general give equal
embeddings. -/
def factorEmbedding (f : β ↪o γ) : DedekindCut β ↪o γ :=
  .ofMapLEIff (fun A ↦ sSup (f '' A.fst)) <| by
    refine fun A B ↦ ⟨fun h x hx ↦ ?_, fun h ↦ sSup_le_sSup (image_mono h)⟩
    simp_rw [← lowerBounds_snd]
    simp_rw [le_sSup_iff, sSup_le_iff, forall_mem_image] at h
    intro y hy
    rw [← f.le_iff_le]
    exact h _ (image_snd_subset_upperBounds f.monotone _ (mem_image_of_mem _ hy)) hx

theorem factorEmbedding_apply (f : β ↪o γ) (A : DedekindCut β) :
    factorEmbedding f A = sSup (f '' A.fst) :=
  rfl

@[simp]
theorem factorEmbedding_ofElement (f : β ↪o γ) (x : β) : factorEmbedding f (ofElement x) = f x := by
  rw [factorEmbedding_apply]
  apply le_antisymm (by simp)
  rw [le_sSup_iff]
  refine fun y hy ↦ hy ?_
  simp

/-- The Dedekind-MacNeille completion of a partial order is the smallest complete lattice containing
it, in the sense that any embedding into any complete lattice factors through it. -/
theorem factorEmbedding_factors (f : β ↪o γ) :
    ofElementEmbedding.trans (factorEmbedding f) = f := by
  ext; simp

end DedekindCut
