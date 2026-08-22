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
TODO
-/

@[expose] public section

section defs

variable (A : Type*) {B : Type*} [Membership B A]

/-- A class to indicate that the bottom element on a type has no members. -/
class IsMemBot [Bot A] where
  /-- The bottom element corresponds to the empty set. -/
  protected notMem_bot {x : B} : x ∉ (⊥ : A) := by exact fun h ↦ h

@[simp] alias SetLike.notMem_bot := IsMemBot.notMem_bot

/-- A class to indicate that the top element on a type contains every member. -/
class IsMemTop [Top A] where
  /-- The top element corresponds to the universal set. -/
  protected mem_top {x : B} : x ∈ (⊤ : A) := by exact trivial

@[simp] alias SetLike.mem_top := IsMemTop.mem_top

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

/-- A class to indicate that the set infimum on a type corresponds to set intersection. -/
class IsMemSInf [InfSet A] where
  /-- The set infimum corresponds to set intersection. -/
  protected mem_sInf {S : Set A} {x : B} : x ∈ sInf S ↔ ∀ T ∈ S, x ∈ T := by rfl

@[simp] alias SetLike.mem_sInf := IsMemSInf.mem_sInf

/-- A class to indicate that the set supremum on a type corresponds to set union. -/
class IsMemSSup [SupSet A] where
  /-- The set supremum corresponds to set union. -/
  protected mem_sSup {S : Set A} {x : B} : x ∈ sSup S ↔ ∃ T ∈ S, x ∈ T := by rfl

@[simp] alias SetLike.mem_sSup := IsMemSSup.mem_sSup

end defs

section default

variable (A : Type*) {B : Type*}

@[reducible] def OrderBot.ofMembership [Membership B A] [Bot A] [IsMemBot A] :
    letI := LE.ofMembership A; OrderBot A where
  __ := LE.ofMembership A
  bot := ⊥
  bot_le := by simp [LE.le]

@[reducible] def OrderTop.ofMembership [Membership B A] [Top A] [IsMemTop A] :
    letI := LE.ofMembership A; OrderTop A where
  __ := LE.ofMembership A
  top := ⊤
  le_top := by simp [LE.le]

@[reducible] def SemilatticeInf.ofSetLike [SetLike A B] [Min A] [IsMemInf A] :
    SemilatticeInf A where
  __ := PartialOrder.ofSetLike A
  inf := (· ⊓ ·)
  inf_le_left := by simp [LE.le]; grind
  inf_le_right := by simp [LE.le]
  le_inf := by simp [LE.le]; grind

@[reducible] def SemilatticeSup.ofSetLike [SetLike A B] [Max A] [IsMemSup A] :
    SemilatticeSup A where
  __ := PartialOrder.ofSetLike A
  sup := (· ⊔ ·)
  le_sup_left := by simp [LE.le]; grind
  le_sup_right := by simp [LE.le]; grind
  sup_le := by simp [LE.le]; grind

@[reducible] def CompleteLattice.ofSetLikeSInf [SetLike A B] [InfSet A] [IsMemSInf A] :
    CompleteLattice A where
  __ := PartialOrder.ofSetLike A
  __ := completeLatticeOfInf A fun s ↦
    ⟨by simp [lowerBounds, LE.le]; grind,
    by simp [upperBounds, lowerBounds, LE.le]; grind⟩

@[reducible] def CompleteLattice.ofSetLikeSSup [SetLike A B] [SupSet A] [IsMemSSup A] :
    CompleteLattice A where
  __ := PartialOrder.ofSetLike A
  __ := completeLatticeOfSup A fun s ↦
    ⟨by simp [upperBounds, LE.le]; grind,
    by simp [lowerBounds, upperBounds, LE.le]; grind⟩

/- Matches `.ofSetLikeSInf`. -/
instance [Membership B A] [InfSet A] [IsMemSInf A] :
    letI : Min A := { min := (sInf {·, ·}) }; IsMemInf A :=
  letI : Min A := { min := (sInf {·, ·}) }
  { mem_inf := by simp }

/- Matches `.ofSetLikeSInf`. -/
instance [Membership B A] [InfSet A] [IsMemSInf A] :
    letI : Top A := { top := sInf ∅ }; IsMemTop A :=
  letI : Top A := { top := sInf ∅ }
  { mem_top := by simp }

/- Matches `.ofSetLikeSSup`. -/
instance [Membership B A] [SupSet A] [IsMemSSup A] :
    letI : Max A := { max := (sSup {·, ·}) }; IsMemSup A :=
  letI : Max A := { max := (sSup {·, ·}) }
  { mem_sup := by simp }

/- Matches `.ofSetLikeSSup`. -/
instance [Membership B A] [SupSet A] [IsMemSSup A] :
    letI : Bot A := { bot := sSup ∅ }; IsMemBot A :=
  letI : Bot A := { bot := sSup ∅ }
  { notMem_bot := by simp }

end default
