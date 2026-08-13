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
  protected notMem_bot {x : B} : x ∉ (⊥ : A) := by rfl

@[simp] alias SetLike.notMem_bot := IsMemBot.notMem_bot

/-- A class to indicate that the top element on a type contains every member. -/
class IsMemTop [Top A] where
  /-- The top element corresponds to the universal set. -/
  protected mem_top {x : B} : x ∈ (⊤ : A) := by rfl

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
  bot_le := by simp [SetLike.le_def]

@[reducible] def OrderTop.ofMembership [Membership B A] [Top A] [IsMemTop A] :
    letI := LE.ofMembership A; OrderTop A where
  __ := LE.ofMembership A
  top := ⊤
  le_top := by simp [SetLike.le_def]

@[reducible] def SemilatticeInf.ofSetLike [SetLike A B] [Min A] [IsMemInf A] :
    SemilatticeInf A where
  __ := PartialOrder.ofSetLike A
  inf := (· ⊓ ·)
  inf_le_left := by simp [SetLike.le_def]; grind
  inf_le_right := by simp [SetLike.le_def]
  le_inf := by simp [SetLike.le_def]; grind

@[reducible] def SemilatticeSup.ofSetLike [SetLike A B] [Max A] [IsMemSup A] :
    SemilatticeSup A where
  __ := PartialOrder.ofSetLike A
  sup := (· ⊔ ·)
  le_sup_left := by simp [SetLike.le_def]; grind
  le_sup_right := by simp [SetLike.le_def]; grind
  sup_le := by simp [SetLike.le_def]; grind

@[reducible] def CompleteLattice.ofSetLikeSInf [SetLike A B] [InfSet A] [IsMemSInf A] :
    CompleteLattice A :=
  letI := PartialOrder.ofSetLike A
  completeLatticeOfInf A fun s ↦
    ⟨by simp_all [lowerBounds, SetLike.le_def],
    by simp_all [upperBounds, lowerBounds, SetLike.le_def]⟩

@[reducible] def CompleteLattice.ofSetLikeSSup [SetLike A B] [SupSet A] [IsMemSSup A] :
    CompleteLattice A :=
  letI := PartialOrder.ofSetLike A
  completeLatticeOfSup A fun s ↦
    ⟨by simp_all [upperBounds, SetLike.le_def]; grind,
    by simp_all [lowerBounds, upperBounds, SetLike.le_def]; grind⟩

/- Matches the definition in `completeLatticeOfInf`. -/
instance [Membership B A] [InfSet A] [IsMemSInf A] :
    letI : Min A := { min := (sInf {·, ·}) }; IsMemInf A :=
  letI : Min A := { min := (sInf {·, ·}) }
  { mem_inf := by simp }

/- Matches the definition in `completeLatticeOfInf`. -/
instance [Membership B A] [InfSet A] [IsMemSInf A] :
    letI : Top A := { top := sInf ∅ }; IsMemTop A :=
  letI : Top A := { top := sInf ∅ }
  { mem_top := by simp }

/- Matches the definition in `completeLatticeOfSup`. -/
instance [Membership B A] [SupSet A] [IsMemSSup A] :
    letI : Max A := { max := (sSup {·, ·}) }; IsMemSup A :=
  letI : Max A := { max := (sSup {·, ·}) }
  { mem_sup := by simp }

/- Matches the definition in `completeLatticeOfSup`. -/
instance [Membership B A] [SupSet A] [IsMemSSup A] :
    letI : Bot A := { bot := sSup ∅ }; IsMemBot A :=
  letI : Bot A := { bot := sSup ∅ }
  { notMem_bot := by simp }

end default
