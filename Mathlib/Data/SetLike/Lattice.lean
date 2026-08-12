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

/-- A class to indicate that bottom on a `SetLike` type is the empty set. -/
class IsMemBot [Bot A] where
  /-- The coercion from a `SetLike` type preserves bottom. -/
  protected coe_bot' : SetLike.coe (⊥ : A) = ∅

/-- A class to indicate that top on a `SetLike` type is the universal set. -/
class IsMemTop [Top A] where
  /-- The coercion from a `SetLike` type preserves top. -/
  protected coe_top' : SetLike.coe (⊤ : A) = Set.univ

/-- A class to indicate that the infimum on a type corresponds to set intersection. -/
class IsMemInf [Min A] where
  /-- The coercion from a `SetLike` type preserves infima. -/
  protected mem_inf {S T : A} {x : B} : x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T := by rfl

@[simp] alias SetLike.mem_inf := IsMemInf.mem_inf

/-- A class to indicate that supremum on a `SetLike` type is union. -/
class IsMemSup [Max A] where
  /-- The coercion from a `SetLike` type preserves suprema. -/
  protected coe_sup' {S T : A} :
    SetLike.coe (S ⊔ T) = SetLike.coe S ∪ SetLike.coe T

/-- A class to indicate that set infimum on a `SetLike` type is intersection. -/
class IsMemSInf [InfSet A] where
  /-- The coercion from a `SetLike` type preserves arbitrary infima. -/
  protected coe_sInf' {S : Set A} :
    SetLike.coe (sInf S) = sInf (SetLike.coe '' S)

/-- A class to indicate that set supremum on a `SetLike` type is union. -/
class IsMemSSup [SupSet A] where
  /-- The coercion from a `SetLike` type preserves arbitrary suprema. -/
  protected coe_sSup' {S : Set A} :
    SetLike.coe (sSup S) = sSup (SetLike.coe '' S)

end defs

section default

variable (A : Type*) {B : Type*} [SetLike A B]

/- Matches the definition in `completeLatticeOfInf`. -/
instance [InfSet A] [IsMemSInf A B] :
    letI : Min A := { min := (sInf {·, ·}) }; IsMemInf A B :=
  letI : Min A := { min := (sInf {·, ·}) }
  { coe_inf' := fun {S T} ↦ by
      rw [Min.min, IsMemSInf.coe_sInf']
      ext
      simp [Set.image_insert_eq]
  }

/- Matches the definition in `completeLatticeOfInf`. -/
instance [InfSet A] [IsMemSInf A B] :
    letI : Top A := { top := sInf ∅ }; IsMemTop A B :=
  letI : Top A := { top := sInf ∅ }
  { coe_top' := by
      rw [Top.top, IsMemSInf.coe_sInf']
      ext
      simp }

/- Matches the definition in `completeLatticeOfSup`. -/
instance [SupSet A] [IsMemSSup A B] :
    letI : Max A := { max := (sSup {·, ·}) }; IsMemSup A B :=
  letI : Max A := { max := (sSup {·, ·}) }
  { coe_sup' := fun {S T} ↦ by
      rw [Max.max, IsMemSSup.coe_sSup']
      ext
      simp [Set.image_insert_eq] }

/- Matches the definition in `completeLatticeOfSup`. -/
instance [SupSet A] [IsMemSSup A B] :
    letI : Bot A := { bot := sSup ∅ }; IsMemBot A B :=
  letI : Bot A := { bot := sSup ∅ }
  { coe_bot' := by
      rw [Bot.bot, IsMemSSup.coe_sSup']
      ext
      simp }

end default
