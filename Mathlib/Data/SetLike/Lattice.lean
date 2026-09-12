/-
Copyright (c) 2026 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
module

public import Mathlib.Data.SetLike.Basic
public import Mathlib.Data.Set.Insert
public import Mathlib.Order.CompleteLattice.Defs

/-!
# Lattice operations agreeing with set operations

This file defines several typeclasses for lattice operations that agree with the
set operation described by a `Membership` instance.

## Main definitions

* `IsMemInf` : infinimum agrees with intersection
* `IsMemSup` : supremum agrees with union

-/

@[expose] public section

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
