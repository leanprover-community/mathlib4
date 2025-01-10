/-
Copyright (c) 2024 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/
import Mathlib.Order.CompleteSublattice

/-!
# `SetLike` instance for elements of `CompleteSublattice (Set X)`

This file defines a `SetLike` instance for elements of `CompleteSublattice (Set X)`, but does not
register it for typeclass inference to avoid conflicts.
-/

namespace CompleteSublattice

variable {X : Type*} {L : CompleteSublattice (Set X)}

/-- membership is inherited from `Set X` -/
@[simps] def setLikeCompleteSublattice : SetLike L X where
  coe T := T
  coe_injective' := Subtype.val_injective

attribute [local instance] setLikeCompleteSublattice

variable {S T : L} {s : Set L} {I : Sort*} {f : I → L} {x : X}

@[ext] theorem ext (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := SetLike.coe_injective <| Set.ext h

@[local simp] theorem mem_subtype : x ∈ L.subtype T ↔ x ∈ T := Iff.rfl

@[simp] theorem mem_sInf : x ∈ sInf s ↔ ∀ T ∈ s, x ∈ T := by simp [← mem_subtype]
@[simp] theorem mem_iInf : x ∈ ⨅ i : I, f i ↔ ∀ i : I, x ∈ f i := by simp [← mem_subtype]
@[simp] theorem mem_inf : x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T := by simp [← mem_subtype]
@[simp] theorem mem_top : x ∈ (⊤ : L) := by simp [← mem_subtype]

@[simp] theorem mem_sSup : x ∈ sSup s ↔ ∃ T ∈ s, x ∈ T := by simp [← mem_subtype]
@[simp] theorem mem_iSup : x ∈ ⨆ i : I, f i ↔ ∃ i : I, x ∈ f i := by simp [← mem_subtype]
@[simp] theorem mem_sup : x ∈ S ⊔ T ↔ x ∈ S ∨ x ∈ T := by simp [← mem_subtype]
@[simp] theorem mem_bot : ¬ x ∈ (⊥ : L) := by simp [← mem_subtype]

@[simp] lemma mem_coe : x ∈ T.val ↔ x ∈ T := Iff.rfl
@[simp] lemma mem_mk (U : Set X) (h : U ∈ L) : x ∈ (⟨U, h⟩ : L) ↔ x ∈ U := Iff.rfl

end CompleteSublattice
