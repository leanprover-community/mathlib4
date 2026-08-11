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

variable (A : Type*) (B : outParam Type*) [SetLike A B]

/-- A class to indicate that bottom on a `SetLike` type is the empty set. -/
class IsConcreteBot [Bot A] where
  /-- The coercion from a `SetLike` type preserves bottom. -/
  protected coe_bot' : SetLike.coe (⊥ : A) = ∅

/-- A class to indicate that top on a `SetLike` type is the universal set. -/
class IsConcreteTop [Top A] where
  /-- The coercion from a `SetLike` type preserves top. -/
  protected coe_top' : SetLike.coe (⊤ : A) = Set.univ

/-- A class to indicate that infimum on a `SetLike` type is intersection. -/
class IsConcreteMin [Min A] where
  /-- The coercion from a `SetLike` type preserves infima. -/
  protected coe_inf' {S T : A} :
    SetLike.coe (S ⊓ T) = SetLike.coe S ∩ SetLike.coe T

/-- A class to indicate that supremum on a `SetLike` type is union. -/
class IsConcreteMax [Max A] where
  /-- The coercion from a `SetLike` type preserves suprema. -/
  protected coe_sup' {S T : A} :
    SetLike.coe (S ⊔ T) = SetLike.coe S ∪ SetLike.coe T

/-- A class to indicate that set infimum on a `SetLike` type is intersection. -/
class IsConcreteSInf [InfSet A] where
  /-- The coercion from a `SetLike` type preserves arbitrary infima. -/
  protected coe_sInf' {S : Set A} :
    SetLike.coe (sInf S) = sInf (SetLike.coe '' S)

/-- A class to indicate that set supremum on a `SetLike` type is union. -/
class IsConcreteSSup [SupSet A] where
  /-- The coercion from a `SetLike` type preserves arbitrary suprema. -/
  protected coe_sSup' {S : Set A} :
    SetLike.coe (sSup S) = sSup (SetLike.coe '' S)

end defs

section default

variable (A B : Type*) [SetLike A B]

/-- The bottom element induced from a `SetLike` instance by the empty set.

A bottom element defined as `.ofSetLike` will automatically make available an instance
of `IsConcreteBot`.
-/
@[reducible] noncomputable def Bot.ofSetLike
    (h : ∃ U : A, SetLike.coe U = ∅) : Bot A where
  bot := Classical.choose h

instance (h : ∃ U : A, SetLike.coe U = ∅) :
    letI := Bot.ofSetLike A B h; IsConcreteBot A B :=
  letI := Bot.ofSetLike A B h; { coe_bot' := Classical.choose_spec h }

/-- The top element induced from a `SetLike` instance by the universal set.

A top element defined as `.ofSetLike` will automatically make available an instance
of `IsConcreteTop`.
-/
@[reducible] noncomputable def Top.ofSetLike
    (h : ∃ U : A, SetLike.coe U = Set.univ) : Top A where
  top := Classical.choose h

instance (h : ∃ U : A, SetLike.coe U = Set.univ) :
    letI := Top.ofSetLike A B h; IsConcreteTop A B :=
  letI := Top.ofSetLike A B h; { coe_top' := Classical.choose_spec h }

/-- The infimum induced from a `SetLike` instance by intersection.

An infimum defined as `.ofSetLike` will automatically make available an instance
of `IsConcreteMin`.
-/
@[reducible] noncomputable def Min.ofSetLike
    (h : ∀ S T : A, ∃ U : A, SetLike.coe U = SetLike.coe S ∩ SetLike.coe T) : Min A where
  min S T := Classical.choose (h S T)

instance (h : ∀ S T : A, ∃ U : A, SetLike.coe U = SetLike.coe S ∩ SetLike.coe T) :
    letI := Min.ofSetLike A B h; IsConcreteMin A B :=
  letI := Min.ofSetLike A B h; { coe_inf' := Classical.choose_spec (h _ _) }

/-- The supremum induced from a `SetLike` instance by union.

A supremum defined as `.ofSetLike` will automatically make available an instance
of `IsConcreteMax`.
-/
@[reducible] noncomputable def Max.ofSetLike
    (h : ∀ S T : A, ∃ U : A, SetLike.coe U = SetLike.coe S ∪ SetLike.coe T) : Max A where
  max S T := Classical.choose (h S T)

instance (h : ∀ S T : A, ∃ U : A, SetLike.coe U = SetLike.coe S ∪ SetLike.coe T) :
    letI := Max.ofSetLike A B h; IsConcreteMax A B :=
  letI := Max.ofSetLike A B h; { coe_sup' := Classical.choose_spec (h _ _) }

/-- The arbitrary infimum induced from a `SetLike` instance by intersection.

An arbitrary infimum defined as `.ofSetLike` will automatically make available an instance
of `IsConcreteSInf`.
-/
@[reducible] noncomputable def InfSet.ofSetLike
    (h : ∀ S : Set A, ∃ U : A, SetLike.coe U = sInf (SetLike.coe '' S)) :
    InfSet A where
  sInf S := Classical.choose (h S)

instance (h : ∀ S : Set A, ∃ U : A, SetLike.coe U = sInf (SetLike.coe '' S)) :
    letI := InfSet.ofSetLike A B h; IsConcreteSInf A B :=
  letI := InfSet.ofSetLike A B h; { coe_sInf' := Classical.choose_spec (h _) }

/- Matches the definition in `completeLatticeOfInf`. -/
instance [InfSet A] [IsConcreteSInf A B] :
    letI : Min A := { min := (sInf {·, ·}) }; IsConcreteMin A B :=
  letI : Min A := { min := (sInf {·, ·}) }
  { coe_inf' := fun {S T} ↦ by
      rw [Min.min, IsConcreteSInf.coe_sInf']
      ext
      simp [Set.image_insert_eq]
  }

/- Matches the definition in `completeLatticeOfInf`. -/
instance [InfSet A] [IsConcreteSInf A B] :
    letI : Top A := { top := sInf ∅ }; IsConcreteTop A B :=
  letI : Top A := { top := sInf ∅ }
  { coe_top' := by
      rw [Top.top, IsConcreteSInf.coe_sInf']
      ext
      simp }

/-- The arbitrary supremum induced from a `SetLike` instance by union.

An arbitrary supremum defined as `.ofSetLike` will automatically make available an instance
of `IsConcreteSSup`.
-/
@[reducible] noncomputable def SupSet.ofSetLike
    (h : ∀ S : Set A, ∃ U : A, SetLike.coe U = sSup (SetLike.coe '' S)) :
    SupSet A where
  sSup S := Classical.choose (h S)

instance (h : ∀ S : Set A, ∃ U : A, SetLike.coe U = sSup (SetLike.coe '' S)) :
    letI := SupSet.ofSetLike A B h; IsConcreteSSup A B :=
  letI := SupSet.ofSetLike A B h; { coe_sSup' := Classical.choose_spec (h _) }

/- Matches the definition in `completeLatticeOfSup`. -/
instance [SupSet A] [IsConcreteSSup A B] :
    letI : Max A := { max := (sSup {·, ·}) }; IsConcreteMax A B :=
  letI : Max A := { max := (sSup {·, ·}) }
  { coe_sup' := fun {S T} ↦ by
      rw [Max.max, IsConcreteSSup.coe_sSup']
      ext
      simp [Set.image_insert_eq] }

/- Matches the definition in `completeLatticeOfSup`. -/
instance [SupSet A] [IsConcreteSSup A B] :
    letI : Bot A := { bot := sSup ∅ }; IsConcreteBot A B :=
  letI : Bot A := { bot := sSup ∅ }
  { coe_bot' := by
      rw [Bot.bot, IsConcreteSSup.coe_sSup']
      ext
      simp }

end default

namespace SetLike

variable {A B : Type*} [SetLike A B]

section Bot

variable [Bot A] [IsConcreteBot A B] {x : B}

@[simp] theorem mem_bot : x ∈ (⊥ : A) ↔ False := by
  simp [← SetLike.mem_coe, IsConcreteBot.coe_bot']

end Bot

section Top

variable [Top A] [IsConcreteTop A B] {x : B}

@[simp] theorem mem_top : x ∈ (⊤ : A) ↔ True := by
  simp [← SetLike.mem_coe, IsConcreteTop.coe_top']

end Top

section Min

variable [Min A] [IsConcreteMin A B] {S T : A} {x : B}

@[simp] theorem mem_inf : x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T := by
  simp [← SetLike.mem_coe, IsConcreteMin.coe_inf']

end Min

section Max

variable [Max A] [IsConcreteMax A B] {S T : A} {x : B}

@[simp] theorem mem_sup : x ∈ S ⊔ T ↔ x ∈ S ∨ x ∈ T := by
  simp [← SetLike.mem_coe, IsConcreteMax.coe_sup']

end Max

section InfSet

variable [InfSet A] [IsConcreteSInf A B] {S : Set A} {x : B}

@[simp] theorem mem_sInf : x ∈ sInf S ↔ ∀ T ∈ S, x ∈ T := by
  simp [← SetLike.mem_coe, IsConcreteSInf.coe_sInf']

end InfSet

section SupSet

variable [SupSet A] [IsConcreteSSup A B] {S : Set A} {x : B}

@[simp] theorem mem_sSup : x ∈ sSup S ↔ ∃ T ∈ S, x ∈ T := by
  simp [← SetLike.mem_coe, IsConcreteSSup.coe_sSup']

end SupSet

end SetLike
