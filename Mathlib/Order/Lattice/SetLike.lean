/-
Copyright (c) 2026 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
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

variable [SemilatticeSup A] [IsConcreteLE A B] {p q : A}

@[membership .]
theorem mem_sup_left {x : B} (h : x ∈ p) : x ∈ p ⊔ q :=
  mem_of_le_of_mem le_sup_left h

@[membership .]
theorem mem_sup_right {x : B} (h : x ∈ q) : x ∈ p ⊔ q :=
  mem_of_le_of_mem le_sup_right h

end SemilatticeSup

section OrderBot

variable [LE A] [OrderBot A] [IsConcreteLE A B] {p q : A}

theorem mem_of_mem_bot {x : B} (h : x ∈ (⊥ : A)) : x ∈ p :=
  mem_of_le_of_mem bot_le h

grind_pattern [membership] mem_of_mem_bot => x ∈ ⊥, x ∈ p where p =/= ⊥

end OrderBot

section SemilatticeInf

variable [SemilatticeInf A] [IsConcreteLE A B] {p q : A}

theorem mem_of_mem_inf_left {x : B} (h : x ∈ p ⊓ q) : x ∈ p :=
  mem_of_le_of_mem inf_le_left h

grind_pattern [membership] mem_of_mem_inf_left => x ∈ p ⊓ q, x ∈ p

theorem mem_of_mem_inf_right {x : B} (h : x ∈ p ⊓ q) : x ∈ q :=
  mem_of_le_of_mem inf_le_right h

grind_pattern [membership] mem_of_mem_inf_right => x ∈ p ⊓ q, x ∈ p

end SemilatticeInf

section OrderTop

variable [LE A] [OrderTop A] [IsConcreteLE A B] {p q : A}

theorem mem_top_of_mem {x : B} (h : x ∈ p) : x ∈ (⊤ : A) :=
  mem_of_le_of_mem le_top h

grind_pattern [membership] mem_top_of_mem => x ∈ ⊤, x ∈ p where p =/= ⊤

end OrderTop
