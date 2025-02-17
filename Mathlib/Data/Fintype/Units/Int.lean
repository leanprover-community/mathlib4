/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Data.Fintype.Card

/-!
# fintype instances relating to units
-/

assert_not_exists Field

instance UnitsInt.fintype : Fintype ℤˣ :=
  ⟨{1, -1}, fun x ↦ by cases Int.units_eq_one_or x <;> simp [*]⟩

@[simp]
theorem UnitsInt.univ : (Finset.univ : Finset ℤˣ) = {1, -1} := rfl

@[simp]
theorem Fintype.card_units_int : Fintype.card ℤˣ = 2 := rfl
