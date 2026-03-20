/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.SetTheory.Cardinal.Finite

/-! # Properties of `Equiv.Perm` on `Finite` types

-/

public section

-- assert_not_exists Field

variable {α : Type*} [Finite α]

namespace Nat

theorem card_perm : Nat.card (Equiv.Perm α) = (Nat.card α)! := by
  classical
  have := Fintype.ofFinite α
  rw [card_eq_fintype_card, card_eq_fintype_card, Fintype.card_perm]

end Nat

namespace Equiv.Perm

theorem isCyclic_of_card_le_two (hα : Nat.card α ≤ 2) :
    IsCyclic (Perm α) := by
  apply isCyclic_of_card_dvd_prime (p := 2)
  rw [Nat.card_perm]
  interval_cases (Nat.card α) <;> simp

theorem isMulCommutative_of_card_le_two (hα : Nat.card α ≤ 2) :
    IsMulCommutative (Perm α) :=
  (isCyclic_of_card_le_two hα).isMulCommutative

end Equiv.Perm
