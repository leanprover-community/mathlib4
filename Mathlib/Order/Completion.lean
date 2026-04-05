/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Order.Concept

import Mathlib.Order.UpperLower.CompleteLattice

/-!
# Dedekind-MacNeille completion

The Dedekind-MacNeille completion of a partial order is the smallest complete lattice into which it
embeds.

The theory of concept lattices allows for a simple construction. In fact, `DedekindCut α` is simply
an abbreviation for `Concept α α (· ≤ ·)`. This means we don't need to reprove that this is a
complete lattice; instead, the file simply proves that any order embedding into another complete
lattice factors through it.

## Tags

Dedekind completion, Dedekind cut
-/

@[expose] public section

open Concept Set

variable {α β : Type*}

variable (α) in
/-- The **Dedekind-MacNeille completion** of a partial order is the smallest complete lattice that
contains it. We define here the type of Dedekind cuts of `α` as the `Concept` lattice of the `≤`
relation of `α`.

For `A : DedekindCut α`, the sets `A.left` and `A.right` are related by
`upperBounds A.left = A.right` and `lowerBounds A.right = A.left`.

The theorem `DedekindCut.principalEmbedding_trans_factorEmbedding` proves that if `α` is a partial
order and `β` is a complete lattice, any embedding `α ↪o β` factors through `DedekindCut α`. -/
abbrev DedekindCut [Preorder α] := Concept α α (· ≤ ·)

namespace DedekindCut

section Preorder
variable [Preorder α] [Preorder β]

/-- The left set of a Dedekind cut. This is an alias for `Concept.extent`. -/
abbrev left (A : DedekindCut α) : Set α := A.extent

/-- The right set of a Dedekind cut. This is an alias for `Concept.intent`. -/
abbrev right (A : DedekindCut α) : Set α := A.intent

/-- See `DedekindCut.ext'` for a version using the right set instead. -/
@[ext] theorem ext {A B : DedekindCut α} (h : A.left = B.left) : A = B := Concept.ext h

/-- See `DedekindCut.ext` for a version using the left set instead. -/
theorem ext' {A B : DedekindCut α} (h : A.right = B.right) : A = B := Concept.ext' h

@[simp]
theorem upperBounds_left (A : DedekindCut α) : upperBounds A.left = A.right :=
  A.upperPolar_extent

@[simp]
theorem lowerBounds_right (A : DedekindCut α) : lowerBounds A.right = A.left :=
  A.lowerPolar_intent

theorem image_left_subset_lowerBounds {f : α → β} (hf : Monotone f)
    (A : DedekindCut α) : f '' A.left ⊆ lowerBounds (f '' A.right) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact hf <| rel_extent_intent hx hy

theorem image_right_subset_upperBounds {f : α → β} (hf : Monotone f)
    (A : DedekindCut α) : f '' A.right ⊆ upperBounds (f '' A.left) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact hf <| rel_extent_intent hy hx

/-- Convert an element into its Dedekind cut (`Iic a`, `Ici a`). This map is order-preserving,
though it is injective only on partial orders. -/
def principal (a : α) : DedekindCut α :=
  (Concept.ofObject _ a).copy (Iic a) (Ici a)
    (by ext; simpa [mem_lowerPolar_iff] using forall_ge_iff_le.symm)
    (by ext; simp)

@[simp] theorem left_principal (a : α) : (principal a).left = Iic a := rfl
@[simp] theorem right_principal (a : α) : (principal a).right = Ici a := rfl

@[simp] theorem ofObject_eq_principal (a : α) : ofObject (· ≤ ·) a = principal a :=
  (copy_eq ..).symm
@[simp] theorem ofAttribute_eq_principal (a : α) : ofAttribute (· ≤ ·) a = principal a := by
  ext; simp

@[simp]
theorem principal_le_principal {a b : α} : principal a ≤ principal b ↔ a ≤ b := by
  simpa using ofObject_le_ofAttribute_iff (r := (· ≤ ·)) (a := a)

@[simp]
theorem principal_lt_principal {a b : α} : principal a < principal b ↔ a < b := by
  simp [lt_iff_le_not_ge]

/-- We can never have a computable decidable instance, for the same reason we can't on `Set α`. -/
noncomputable instance : DecidableLE (DedekindCut α) :=
  Classical.decRel _

end Preorder

section PartialOrder
variable [PartialOrder α]

@[simp]
theorem principal_inj {a b : α} : principal a = principal b ↔ a = b := by
  simp [le_antisymm_iff]

/-- `DedekindCut.principal` as an `OrderEmbedding`. -/
@[simps! apply]
def principalEmbedding : α ↪o DedekindCut α where
  toFun := principal
  inj' _ _ := principal_inj.1
  map_rel_iff' := principal_le_principal

@[simp] theorem coe_principalEmbedding : ⇑(@principalEmbedding α _) = principal := rfl

end PartialOrder

section CompleteLattice
variable [CompleteLattice α] [PartialOrder β]

@[simp]
theorem principal_sSup_left (A : DedekindCut α) : principal (sSup A.left) = A := by
  apply ext'
  ext
  rw [right_principal, mem_Ici, sSup_le_iff, ← upperBounds_left, mem_upperBounds]

@[simp]
theorem principal_sInf_right (A : DedekindCut α) : principal (sInf A.right) = A := by
  ext
  rw [left_principal, mem_Iic, le_sInf_iff, ← lowerBounds_right, mem_lowerBounds]

/-- Any order embedding `β ↪o α` into a complete lattice `α` factors through `DedekindCut β`.

This map is defined so that `factorEmbedding f A = sSup (f '' A.left)`. Although the construction
`factorEmbedding f A = sInf (f '' A.right)` would also work, these do **not** in general give equal
embeddings. -/
def factorEmbedding (f : β ↪o α) : DedekindCut β ↪o α :=
  .ofMapLEIff (fun A ↦ sSup (f '' A.left)) <| by
    refine fun A B ↦ ⟨fun h x hx ↦ ?_, fun h ↦ sSup_le_sSup (image_mono h)⟩
    simp_rw [← lowerBounds_right]
    simp_rw [le_sSup_iff, sSup_le_iff, forall_mem_image] at h
    intro y hy
    rw [← f.le_iff_le]
    exact h _ (image_right_subset_upperBounds f.monotone _ (mem_image_of_mem _ hy)) hx

theorem factorEmbedding_apply (f : β ↪o α) (A : DedekindCut β) :
    factorEmbedding f A = sSup (f '' A.left) :=
  rfl

@[simp]
theorem factorEmbedding_principal (f : β ↪o α) (x : β) : factorEmbedding f (principal x) = f x := by
  rw [factorEmbedding_apply]
  apply le_antisymm (by simp)
  rw [le_sSup_iff]
  refine fun y hy ↦ hy ?_
  simp

/-- The Dedekind-MacNeille completion of a partial order is the smallest complete lattice containing
it, in the sense that any embedding into any complete lattice factors through it. -/
theorem principalEmbedding_trans_factorEmbedding (f : β ↪o α) :
    principalEmbedding.trans (factorEmbedding f) = f := by
  ext; simp

/-- `DedekindCut.principal` as an `OrderIso`.

This provides the second half of the **fundamental theorem of concept lattices**: every complete
lattice is isomorphic to a concept lattice (its own Dedekind completion).

See `Concept.instCompleteLattice` for the first half. -/
@[simps! apply]
def principalIso : α ≃o DedekindCut α where
  invFun := factorEmbedding (OrderIso.refl α)
  left_inv x := factorEmbedding_principal _ x
  right_inv x := by simp [factorEmbedding]
  __ := principalEmbedding

theorem principalIso_symm_apply (A : DedekindCut α) : principalIso.symm A = sSup A.left :=
  (factorEmbedding_apply ..).trans <| by simp

end CompleteLattice

section LinearOrder
variable [LinearOrder α]

instance : @Std.Total (DedekindCut α) (· ≤ ·) where
  total x y := le_total (α := LowerSet α) ⟨_, isLowerSet_extent_le x⟩ ⟨_, isLowerSet_extent_le y⟩

noncomputable instance : LinearOrder (DedekindCut α) where
  min_def x y := congrFun₂ inf_eq_minDefault x y
  max_def x y := congrFun₂ sup_eq_maxDefault x y
  le_total := total_of _
  toDecidableLE := inferInstance

noncomputable instance : CompleteLinearOrder (DedekindCut α) where
  __ := (inferInstance : LinearOrder _)
  __ := (inferInstance : CompleteLattice _)
  __ := LinearOrder.toBiheytingAlgebra _

end LinearOrder
end DedekindCut
