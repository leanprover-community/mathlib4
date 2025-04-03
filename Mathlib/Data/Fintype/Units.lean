/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.SetTheory.Cardinal.Finite

#align_import data.fintype.units from "leanprover-community/mathlib"@"509de852e1de55e1efa8eacfa11df0823f26f226"

/-!
# fintype instances relating to units
-/


variable {α : Type*}

instance UnitsInt.fintype : Fintype ℤˣ :=
  ⟨{1, -1}, fun x ↦ by cases Int.units_eq_one_or x <;> simp [*]⟩
#align units_int.fintype UnitsInt.fintype

@[simp]
theorem UnitsInt.univ : (Finset.univ : Finset ℤˣ) = {1, -1} := rfl
#align units_int.univ UnitsInt.univ

@[simp]
theorem Fintype.card_units_int : Fintype.card ℤˣ = 2 := rfl
#align fintype.card_units_int Fintype.card_units_int

instance [Monoid α] [Fintype α] [DecidableEq α] : Fintype αˣ :=
  Fintype.ofEquiv _ (unitsEquivProdSubtype α).symm

instance [Monoid α] [Finite α] : Finite αˣ := Finite.of_injective _ Units.ext

theorem Fintype.card_eq_card_units_add_one [GroupWithZero α] [Fintype α] [DecidableEq α] :
    Fintype.card α = Fintype.card αˣ + 1 := by
  rw [eq_comm, Fintype.card_congr unitsEquivNeZero]
  have := Fintype.card_congr (Equiv.sumCompl (· = (0 : α)))
  rwa [Fintype.card_sum, add_comm, Fintype.card_subtype_eq] at this

theorem Nat.card_eq_card_units_add_one [GroupWithZero α] [Finite α] :
    Nat.card α = Nat.card αˣ + 1 := by
  have : Fintype α := Fintype.ofFinite α
  classical
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_eq_card_units_add_one]

theorem Fintype.card_units [GroupWithZero α] [Fintype α] [DecidableEq α] :
    Fintype.card αˣ = Fintype.card α - 1 := by
  rw [@Fintype.card_eq_card_units_add_one α, Nat.add_sub_cancel]
#align fintype.card_units Fintype.card_units
