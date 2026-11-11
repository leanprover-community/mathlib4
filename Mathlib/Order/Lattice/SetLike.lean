/-
Copyright (c) 2026 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
module

public import Mathlib.Basic.SetLike.Basic

/-!
# Lattice operations agreeing with set operations

This file defines several typeclasses for lattice operations that agree with the
set operation described by a `Membership` instance.

We also prove lemmas about lattice operations agreeing with set operations.

## Main definitions

* `IsMemInf` : infimum agrees with intersection
* `IsMemSup` : supremum agrees with union
-/

public section

section defs

variable (A : Type*) {B : Type*} [Membership B A]

/-- A class to indicate that the infimum on a type corresponds to set intersection. -/
class IsMemInf [Min A] where
  /-- The infimum corresponds to set intersection. -/
  protected mem_inf {S T : A} {x : B} : x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T := by rfl

@[simp, membership =] alias mem_inf_iff_mem_and_mem := IsMemInf.mem_inf

/-- A class to indicate that the supremum on a type corresponds to set union. -/
class IsMemSup [Max A] where
  /-- The supremum corresponds to set union. -/
  protected mem_sup {S T : A} {x : B} : x ∈ S ⊔ T ↔ x ∈ S ∨ x ∈ T := by rfl

@[simp, membership =] alias mem_sup_iff_mem_or_mem := IsMemSup.mem_sup

end defs

section default

variable (A : Type*) {B : Type*}

@[reducible] def SemilatticeInf.ofSetLike [SetLike A B] [Min A] [IsMemInf A] :
    SemilatticeInf A where
  __ := PartialOrder.ofSetLike A
  inf := (· ⊓ ·)
  inf_le_left := by membership
  inf_le_right := by membership
  le_inf := by membership

@[reducible] def SemilatticeSup.ofSetLike [SetLike A B] [Max A] [IsMemSup A] :
    SemilatticeSup A where
  __ := PartialOrder.ofSetLike A
  sup := (· ⊔ ·)
  le_sup_left := by membership
  le_sup_right := by membership
  sup_le := by membership

end default

section lemmas

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

end lemmas
