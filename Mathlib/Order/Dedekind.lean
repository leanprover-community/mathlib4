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

namespace DedekindCut

theorem image_fst_subset_lowerBounds {β : Type*} [Preorder β] {f : α → β} (hf : Monotone f)
    (A : DedekindCut α) : f '' A.fst ⊆ lowerBounds (f '' A.snd) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact hf <| rel_fst_snd hx hy

theorem image_snd_subset_upperBounds {β : Type*} [Preorder β] {f : α → β} (hf : Monotone f)
    (A : DedekindCut α) : f '' A.snd ⊆ upperBounds (f '' A.fst) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact hf <| rel_fst_snd hy hx

/-- Convert an element into its Dedekind cut (`Iic a`, `Ici a`). This map is order-preserving,
though it is injective only on partial orders. -/
@[simps!]
def ofElement (a : α) : DedekindCut α where
  fst := Iic a
  snd := Ici a
  closure_fst := upperBounds_Iic
  closure_snd := lowerBounds_Ici

@[simp] theorem fst_ofElement (a : α) : (ofElement a).fst = Iic a := rfl
@[simp] theorem snd_ofElement (a : α) : (ofElement a).snd = Ici a := rfl

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
