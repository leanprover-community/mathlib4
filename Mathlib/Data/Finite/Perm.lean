/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-! # Properties of `Equiv.Perm` on `Finite` types

Let `α` be a `Finite` type.

* `Nat.card_perm`: cardinality of `Equiv.Perm α`.

* `Equiv.Perm.isCyclic_of_card_le_two`: if `Nat.card α ≤ 2`,
  then `Equiv.Perm α` is cyclic.

* `Equiv.Perm.isCyclic_iff_card_le_two`: `Equiv.Perm α` is cyclic iff `Nat.card α ≤ 2`.

* `Equiv.Perm.isMulCommutative_iff_card_le_two`: `Equiv.Perm α` is commutative iff `Nat.card α ≤ 2`.

-/
set_option backward.defeqAttrib.useBackward true

public section

assert_not_exists Field

open Equiv Nat

variable {α : Type*} [Finite α]

namespace Nat

theorem card_perm : Nat.card (Perm α) = (Nat.card α)! := by
  classical
  have := Fintype.ofFinite α
  rw [card_eq_fintype_card, card_eq_fintype_card, Fintype.card_perm]

end Nat

namespace Equiv.Perm

theorem isCyclic_of_card_le_two (hα : Nat.card α ≤ 2) :
    IsCyclic (Perm α) := by
  apply isCyclic_of_card_dvd_prime (p := 2)
  simpa [card_perm] using factorial_dvd_factorial hα

theorem isMulCommutative_iff_card_le_two :
    IsMulCommutative (Perm α) ↔ Nat.card α ≤ 2 := by
  refine ⟨?_, fun h ↦ (isCyclic_of_card_le_two h).isMulCommutative⟩
  classical
  rintro ⟨⟨h⟩⟩
  rw [← not_lt, ← Set.ncard_univ, Set.two_lt_ncard_iff]
  rintro ⟨a, b, c, _, _, _, hab, hac, hbc⟩
  apply hbc
  simp_rw [Perm.ext_iff] at h
  simpa [swap_apply_of_ne_of_ne hab hac] using h (swap a b) (swap b c) a

theorem isCyclic_iff_card_le_two :
    IsCyclic (Perm α) ↔ Nat.card α ≤ 2 :=
  ⟨fun h ↦ isMulCommutative_iff_card_le_two.mp h.isMulCommutative, isCyclic_of_card_le_two⟩

end Equiv.Perm
