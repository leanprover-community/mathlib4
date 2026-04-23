/-
Copyright (c) 2024 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/
module

public import Mathlib.Order.CompleteSublattice
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Set.Lattice
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-!
# `SetLike` instance for elements of `CompleteSublattice (Set X)`

This file provides lemmas for the `SetLike` instance for elements of `CompleteSublattice (Set X)`
-/

public section

attribute [local instance] SetLike.instSubtypeSet

namespace Sublattice

variable {X : Type*} {L : Sublattice (Set X)}

variable {S T : L} {x : X}

@[ext] lemma ext_mem (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := SetLike.ext h

lemma mem_subtype : x ∈ L.subtype T ↔ x ∈ T := Iff.rfl

@[simp] lemma setLike_mem_inf : x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T := by simp [← mem_subtype]
@[simp] lemma setLike_mem_sup : x ∈ S ⊔ T ↔ x ∈ S ∨ x ∈ T := by simp [← mem_subtype]

@[simp] lemma setLike_mem_coe : x ∈ T.val ↔ x ∈ T := Iff.rfl

end Sublattice

namespace CompleteSublattice

variable {X : Type*} {L : CompleteSublattice (Set X)}

variable {S T : L} {𝒮 : Set L} {I : Sort*} {f : I → L} {x : X}

@[ext] lemma ext (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := SetLike.ext h

lemma mem_subtype : x ∈ L.subtype T ↔ x ∈ T := Iff.rfl

@[simp] lemma mem_inf : x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T := by simp [← mem_subtype]
@[simp] lemma mem_sInf : x ∈ sInf 𝒮 ↔ ∀ T ∈ 𝒮, x ∈ T := by simp [← mem_subtype]
@[simp] lemma mem_iInf : x ∈ ⨅ i : I, f i ↔ ∀ i : I, x ∈ f i := by simp [← mem_subtype]

@[simp] lemma mem_top : x ∈ (⊤ : L) := by simp [← mem_subtype]

@[simp] lemma mem_sup : x ∈ S ⊔ T ↔ x ∈ S ∨ x ∈ T := by simp [← mem_subtype]
@[simp] lemma mem_sSup : x ∈ sSup 𝒮 ↔ ∃ T ∈ 𝒮, x ∈ T := by simp [← mem_subtype]
@[simp] lemma mem_iSup : x ∈ ⨆ i : I, f i ↔ ∃ i : I, x ∈ f i := by simp [← mem_subtype]

@[simp] lemma notMem_bot : x ∉ (⊥ : L) := by simp [← mem_subtype]

end CompleteSublattice
