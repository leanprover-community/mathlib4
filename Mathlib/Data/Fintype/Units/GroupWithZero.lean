/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Data.Fintype.Units.Defs

/-!
# fintype instances relating to units
-/

assert_not_exists Field

variable {α : Type*}

variable (α)

theorem Nat.card_units [GroupWithZero α] :
    Nat.card αˣ = Nat.card α - 1 := by
  classical
  rw [Nat.card_congr unitsEquivNeZero, eq_comm, ← Nat.card_congr (Equiv.sumCompl (· = (0 : α)))]
  rcases finite_or_infinite {a : α // a ≠ 0}
  · rw [Nat.card_sum, Nat.card_unique, add_tsub_cancel_left]
  · rw [Nat.card_eq_zero_of_infinite, Nat.card_eq_zero_of_infinite, zero_tsub]

theorem Nat.card_eq_card_units_add_one [GroupWithZero α] [Finite α] :
    Nat.card α = Nat.card αˣ + 1 := by
  rw [Nat.card_units, tsub_add_cancel_of_le Nat.card_pos]

theorem Fintype.card_units [GroupWithZero α] [Fintype α] [DecidableEq α] :
    Fintype.card αˣ = Fintype.card α - 1 := by
  rw [← Nat.card_eq_fintype_card, Nat.card_units, Nat.card_eq_fintype_card]

theorem Fintype.card_eq_card_units_add_one [GroupWithZero α] [Fintype α] [DecidableEq α] :
    Fintype.card α = Fintype.card αˣ + 1 := by
  rw [Fintype.card_units, tsub_add_cancel_of_le Fintype.card_pos]
