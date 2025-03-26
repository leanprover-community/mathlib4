/-
Copyright (c) 2021 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde
-/
import Mathlib.Algebra.Order.BigOperators.Ring.List
import Mathlib.Algebra.BigOperators.Group.Multiset.Defs

/-!
# Big operators on a multiset in ordered rings

This file contains the results concerning the interaction of multiset big operators with ordered
rings.
-/

@[simp]
lemma CanonicallyOrderedAdd.multiset_prod_pos {R : Type*}
    [CommSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R] [NoZeroDivisors R] [Nontrivial R]
    {m : Multiset R} : 0 < m.prod ↔ ∀ x ∈ m, 0 < x := by
  rcases m with ⟨l⟩
  rw [Multiset.quot_mk_to_coe'', Multiset.prod_coe]
  exact CanonicallyOrderedAdd.list_prod_pos
