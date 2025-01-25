/-
Copyright (c) 2024 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/
import Mathlib.Order.CompleteSublattice

/-!
# `SetLike` instance for elements of `CompleteSublattice (Set X)`

This file provides lemmas for the `SetLike` instance for elements of `CompleteSublattice (Set X)`
-/

attribute [local instance] SetLike.instSubtypeSet

namespace Sublattice

variable {X : Type*} {L : Sublattice (Set X)}

variable {S T : L} {x : X}

@[ext] theorem ext_mem (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := SetLike.coe_injective <| Set.ext h

theorem mem_subtype : x ∈ L.subtype T ↔ x ∈ T := Iff.rfl

@[simp] theorem setLike_mem_inf : x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T := by simp [← mem_subtype]
@[simp] theorem setLike_mem_sup : x ∈ S ⊔ T ↔ x ∈ S ∨ x ∈ T := by simp [← mem_subtype]

@[simp] lemma setLike_mem_coe : x ∈ T.val ↔ x ∈ T := Iff.rfl
@[simp] lemma setLike_mem_mk (U : Set X) (h : U ∈ L) : x ∈ (⟨U, h⟩ : L) ↔ x ∈ U := Iff.rfl

end Sublattice

namespace CompleteSublattice

variable {X : Type*} {L : CompleteSublattice (Set X)}

variable {𝒮 : Set L} {I : Sort*} {f : I → L} {x : X}

@[simp] theorem mem_sInf : x ∈ sInf 𝒮 ↔ ∀ T ∈ 𝒮, x ∈ T := by simp [← Sublattice.mem_subtype]
@[simp] theorem mem_iInf : x ∈ ⨅ i : I, f i ↔ ∀ i : I, x ∈ f i := by simp [← Sublattice.mem_subtype]
@[simp] theorem mem_top : x ∈ (⊤ : L) := by simp [← mem_subtype]

@[simp] theorem mem_sSup : x ∈ sSup 𝒮 ↔ ∃ T ∈ 𝒮, x ∈ T := by simp [← Sublattice.mem_subtype]
@[simp] theorem mem_iSup : x ∈ ⨆ i : I, f i ↔ ∃ i : I, x ∈ f i := by simp [← Sublattice.mem_subtype]
@[simp] theorem mem_bot : ¬ x ∈ (⊥ : L) := by simp [← Sublattice.mem_subtype]

end CompleteSublattice
