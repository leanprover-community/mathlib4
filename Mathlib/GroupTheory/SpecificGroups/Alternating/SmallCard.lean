/-
Copyright (c) 2026 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # Specific properties of permutation groups on a set of small cardinality

-/

@[expose] public section

variable {α : Type*}

section le_two

variable [Finite α]

theorem Equiv.Perm.isCyclic_of_card_le_two (hα : Nat.card α ≤ 2) :
    IsCyclic (Perm α) := by
  apply isCyclic_of_card_dvd_prime (p := 2)
  rw [Nat.card_perm]
  interval_cases (Nat.card α) <;> simp

theorem Equiv.Perm.isMulCommutative_of_card_le_two (hα : Nat.card α ≤ 2) :
    IsMulCommutative (Perm α) :=
  (isCyclic_of_card_le_two hα).isMulCommutative

end le_two

section le_three

variable [Fintype α] [DecidableEq α]

theorem alternatingGroup.isCyclic_of_card_le_three (hα : Nat.card α ≤ 3) :
    IsCyclic (alternatingGroup α) := by
  cases subsingleton_or_nontrivial α
  · infer_instance
  have : 1 < Nat.card α := Finite.one_lt_card
  apply isCyclic_of_card_dvd_prime (p := 3)
  rw [nat_card_alternatingGroup]
  interval_cases (Nat.card α) <;> simp [Nat.factorial_succ]

theorem alternatingGroup.isMulCommutative_of_card_le_three (hα : Nat.card α ≤ 3) :
    IsMulCommutative (alternatingGroup α) :=
  (isCyclic_of_card_le_three hα).isMulCommutative

end le_three
