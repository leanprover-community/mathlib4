/-
Copyright (c) 2021 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde
-/
import Mathlib.Algebra.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.Ring.List

/-!
# Big operators on a multiset in ordered rings

This file contains the results concerning the interaction of multiset big operators with ordered
rings.
-/

namespace Multiset
variable {R : Type*}

section OrderedCommSemiring
variable [OrderedCommSemiring R] {s : Multiset R}

lemma prod_nonneg (h : ∀ a ∈ s, 0 ≤ a) : 0 ≤ s.prod := by
  revert h
  refine s.induction_on ?_ fun a s hs ih ↦ ?_
  · simp
  · rw [prod_cons]
    exact mul_nonneg (ih _ <| mem_cons_self _ _) (hs fun a ha ↦ ih _ <| mem_cons_of_mem ha)
#align multiset.prod_nonneg Multiset.prod_nonneg

end OrderedCommSemiring

@[simp]
lemma _root_.CanonicallyOrderedCommSemiring.multiset_prod_pos [CanonicallyOrderedCommSemiring R]
    [Nontrivial R] {m : Multiset R} : 0 < m.prod ↔ ∀ x ∈ m, 0 < x := by
  rcases m with ⟨l⟩
  rw [Multiset.quot_mk_to_coe'', Multiset.prod_coe]
  exact CanonicallyOrderedCommSemiring.list_prod_pos

end Multiset
