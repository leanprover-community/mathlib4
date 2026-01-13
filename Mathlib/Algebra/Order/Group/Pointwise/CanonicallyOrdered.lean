/-
Copyright (c) 2025 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
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

variable {α β F : Type*} [Monoid α] [Monoid β] [FunLike F α β]
variable [Preorder β] [CanonicallyOrderedMul β] [MulRightMono β]

@[to_additive]
theorem Ici_mul_Ici_eq_of_canonicallyOrdered {a b : β} :
    Ici a * Ici b = Ici (a * b) := by
  refine Subset.antisymm (Ici_mul_Ici_subset' ..) (subset_def ▸ fun c c_in ↦
    mem_mul.mpr ⟨a, ⟨by simp, ?_⟩⟩)
  obtain ⟨d, hd⟩ := exists_mul_of_le <| mem_Ici.mp c_in
  exact ⟨b * d, by simp [← mul_assoc, hd]⟩

@[to_additive]
theorem Ici_pow_eq_of_canonicallyOrdered {a : β} :
    ∀ n ≠ 0, Ici a ^ n = Ici (a ^ n)
  | 1, _ => by simp
  | n + 2, _ => by simpa [pow_succ _ n.succ, Ici_pow_eq_of_canonicallyOrdered]
    using Ici_mul_Ici_eq_of_canonicallyOrdered (a := a ^ (n + 1)) (b := a)

end Set
