/-
Copyright (c) 2026 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
module

public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Order.CompleteLattice.Basic

/-!
# Lattice operations agreeing with set operations

This file provides lemmas about lattice operations agreeing with set operations.
-/

public section

variable {A B : Type*} [Membership B A]

section CompleteLattice

variable [CompleteLattice A] [IsConcreteLE A B] {s : Set A}

theorem mem_sSup_of_mem {x : B} {p : A} (hp : p ∈ s) (hx : x ∈ p) : x ∈ sSup s :=
  mem_of_le_of_mem (le_sSup hp) hx

grind_pattern [membership] mem_sSup_of_mem => p ∈ s, x ∈ sSup s

theorem mem_sSup_of_exists {x : B} (h : ∃ p ∈ s, x ∈ p) : x ∈ sSup s := by
  rcases h with ⟨_, hp, hx⟩
  exact mem_sSup_of_mem hp hx

theorem mem_of_mem_sInf {x : B} {p : A} (hp : p ∈ s) (hx : x ∈ sInf s) : x ∈ p :=
  mem_of_le_of_mem (sInf_le hp) hx

grind_pattern [membership] mem_of_mem_sInf => p ∈ s, x ∈ sInf s, x ∈ p

end CompleteLattice
