/-
Copyright (c) 2024 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe, Artie Khovanov
-/
module

public import Mathlib.Basic.SetLike.Basic

/-!
# Lattice operations agreeing with set operations

This file provides lemmas about lattice operations agreeing with set operations.
-/

public section

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
