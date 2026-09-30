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

We also prove lemmas about membership under lattice operations.

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

@[simp] alias SetLike.mem_inf := IsMemInf.mem_inf

/-- A class to indicate that the supremum on a type corresponds to set union. -/
class IsMemSup [Max A] where
  /-- The supremum corresponds to set union. -/
  protected mem_sup {S T : A} {x : B} : x ∈ S ⊔ T ↔ x ∈ S ∨ x ∈ T := by rfl

@[simp] alias SetLike.mem_sup := IsMemSup.mem_sup

end defs

section default

variable (A : Type*) {B : Type*}

@[reducible] def SemilatticeInf.ofSetLike [SetLike A B] [Min A] [IsMemInf A] :
    SemilatticeInf A where
  __ := PartialOrder.ofSetLike A B
  inf := (· ⊓ ·)
  inf_le_left := by simp [LE.le]; grind
  inf_le_right := by simp [LE.le]
  le_inf := by simp [LE.le]; grind

@[reducible] def SemilatticeSup.ofSetLike [SetLike A B] [Max A] [IsMemSup A] :
    SemilatticeSup A where
  __ := PartialOrder.ofSetLike A B
  sup := (· ⊔ ·)
  le_sup_left := by simp [LE.le]; grind
  le_sup_right := by simp [LE.le]; grind
  sup_le := by simp [LE.le]; grind

end default

section lemmas

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

end lemmas
