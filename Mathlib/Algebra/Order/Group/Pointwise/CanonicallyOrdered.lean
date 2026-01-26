/-
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia, Andrew Yang
-/
module

public import Mathlib.Algebra.Order.Group.Pointwise.Interval

/-!
# Pointwise operations on intervals in canonically ordered cases

This file strengthens some of the subset results from `Interval.lean`
to equalities in canonically ordered cases.
-/

@[expose] public section

open Pointwise

namespace Set

variable {α β : Type*} [Monoid α] [Monoid β]
variable [Preorder β] [CanonicallyOrderedMul β] [MulRightMono β]

@[to_additive (attr := simp)]
theorem Ici_mul_Ici_eq_of_canonicallyOrdered {a b : β} :
    Ici a * Ici b = Ici (a * b) := by
  refine Subset.antisymm (Ici_mul_Ici_subset' ..) (subset_def ▸ fun c c_in ↦
    mem_mul.mpr ⟨a, ⟨by simp, ?_⟩⟩)
  obtain ⟨d, hd⟩ := exists_mul_of_le <| mem_Ici.mp c_in
  exact ⟨b * d, by simp [← mul_assoc, hd]⟩

@[to_additive (attr := simp)]
theorem Ici_pow_eq_of_canonicallyOrdered {a : β} :
    ∀ n ≠ 0, Ici a ^ n = Ici (a ^ n)
  | 1, _ => by simp
  | n + 2, _ => by simp [pow_succ _ n.succ, Ici_pow_eq_of_canonicallyOrdered]

omit [MulRightMono β] in
@[to_additive (attr := simp)]
lemma Ici_one_eq_univ_of_canonicallyOrdered : Set.Ici (1 : β) = Set.univ := by aesop

end Set
