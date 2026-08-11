/-
Copyright (c) 2026 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
module

public import Mathlib.Data.SetLike.Basic
public import Mathlib.Order.SetNotation

/-!
TODO
-/

@[expose] public section

/-- A class to indicate that infimum on a `SetLike` type is intersection. -/
class IsConcreteMin (A : Type*) (B : outParam Type*) [SetLike A B] [Min A] where
  /-- The coercion from a `SetLike` type preserves infima. -/
  protected coe_inf' {S T : A} :
    SetLike.coe (S ⊓ T) = SetLike.coe S ⊓ SetLike.coe T

/-- A class to indicate that supremum on a `SetLike` type is union. -/
class IsConcreteMax (A : Type*) (B : outParam Type*) [SetLike A B] [Max A] where
  /-- The coercion from a `SetLike` type preserves suprema. -/
  protected coe_sup' {S T : A} :
    SetLike.coe (S ⊔ T) = SetLike.coe S ⊔ SetLike.coe T

/-- A class to indicate that set infimum on a `SetLike` type is intersection. -/
class IsConcreteSInf (A : Type*) (B : outParam Type*) [SetLike A B] [InfSet A] where
  /-- The coercion from a `SetLike` type preserves arbitrary infima. -/
  protected coe_sInf' {S : Set A} :
    SetLike.coe (sInf S) = sInf (SetLike.coe '' S)

/-- A class to indicate that set supremum on a `SetLike` type is union. -/
class IsConcreteSSup (A : Type*) (B : outParam Type*) [SetLike A B] [SupSet A] where
  /-- The coercion from a `SetLike` type preserves arbitrary suprema. -/
  protected coe_sSup' {S : Set A} :
    SetLike.coe (sSup S) = sSup (SetLike.coe '' S)

namespace SetLike

variable {A B : Type*} [SetLike A B]

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
