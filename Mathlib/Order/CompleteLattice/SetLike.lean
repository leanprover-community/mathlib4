/-
Copyright (c) 2024 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe, Artie Khovanov
-/
module

public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Order.CompleteSublattice

/-!
# Lattice operations agreeing with set operations

This file provides lemmas about lattice operations agreeing with set operations.
-/

public section

@[expose] public section

variable {A B : Type*} [Membership B A]

section SemilatticeSup

variable [SemilatticeSup A] [IsMemLE A B] {p q : A}

theorem mem_sup_left {x : B} (h : x ∈ p) : x ∈ p ⊔ q :=
  mem_of_le_of_mem le_sup_left h

theorem mem_sup_right {x : B} (h : x ∈ q) : x ∈ p ⊔ q :=
  mem_of_le_of_mem le_sup_right h

theorem mem_sup_of_mem_or_mem {x : B} (h : x ∈ p ∨ x ∈ q) : x ∈ p ⊔ q :=
  h.elim (mem_sup_left ·) (mem_sup_right ·)

end SemilatticeSup

section OrderBot

variable [LE A] [OrderBot A] [IsMemLE A B] {p q : A}

theorem mem_of_mem_bot {x : B} (h : x ∈ (⊥ : A)) : x ∈ p :=
  mem_of_le_of_mem bot_le h

end OrderBot

section SemilatticeInf

variable [SemilatticeInf A] [IsMemLE A B] {p q : A}

theorem mem_of_mem_inf_left {x : B} (h : x ∈ p ⊓ q) : x ∈ p :=
  mem_of_le_of_mem inf_le_left h

theorem mem_of_mem_inf_right {x : B} (h : x ∈ p ⊓ q) : x ∈ q :=
  mem_of_le_of_mem inf_le_right h

end SemilatticeInf

section OrderTop

variable [LE A] [OrderTop A] [IsMemLE A B] {p q : A}

theorem mem_top_of_mem {x : B} (h : x ∈ p) : x ∈ (⊤ : A) :=
  mem_of_le_of_mem le_top h

end OrderTop

section CompleteLattice

variable [CompleteLattice A] [IsMemLE A B] {s : Set A}

theorem mem_sSup_of_mem {x : B} {p : A} (hp : p ∈ s) (hx : x ∈ p) : x ∈ sSup s :=
  mem_of_le_of_mem (le_sSup hp) hx

theorem mem_sSup_of_exists {x : B} (h : ∃ p ∈ s, x ∈ p) : x ∈ sSup s := by
  rcases h with ⟨_, hp, hx⟩
  exact mem_sSup_of_mem hp hx

end CompleteLattice

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
