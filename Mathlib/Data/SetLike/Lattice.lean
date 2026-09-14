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

instance OrderBot.ofMembership [Membership B A]
    [LE A] [IsConcreteLE A B] [Bot A] [IsMemBot A] : OrderBot A where
  bot_le := by simp [SetLike.le_def]

instance OrderTop.ofMembership [Membership B A]
    [LE A] [IsConcreteLE A B] [Top A] [IsMemTop A] : OrderTop A where
  le_top := by simp [SetLike.le_def]

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

@[reducible] def CompleteLattice.ofSetLikeSInf [SetLike A B] [InfSet A] [IsMemSInf A] :
    CompleteLattice A where
  __ := PartialOrder.ofSetLike A B
  __ := completeLatticeOfInf A fun s ↦
    ⟨by simp [lowerBounds, LE.le]; grind,
    by simp [upperBounds, lowerBounds, LE.le]; grind⟩

@[reducible] def CompleteLattice.ofSetLikeSSup [SetLike A B] [SupSet A] [IsMemSSup A] :
    CompleteLattice A where
  __ := PartialOrder.ofSetLike A B
  __ := completeLatticeOfSup A fun s ↦
    ⟨by simp [upperBounds, LE.le]; grind,
    by simp [lowerBounds, upperBounds, LE.le]; grind⟩

-- TODO : move to right place
-- TODO : replicate for others
-- TODO : test in concrete cases
@[reducible] def Min.ofSInf (A : Type*) [InfSet A] : Min A :=
  ⟨fun S T => sInf {S, T}⟩

/- Matches `.ofSetLikeSInf`. -/
instance [Membership B A] [InfSet A] [IsMemSInf A] :
    letI := Min.ofSInf A
    IsMemInf A :=
  letI : Min A := Min.ofSInf A
  { mem_inf := by simp [Min.min] }

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
