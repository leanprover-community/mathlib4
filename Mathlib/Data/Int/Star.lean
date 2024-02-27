/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.GroupWithZero.Power
import Mathlib.Algebra.Parity
import Mathlib.Algebra.Star.Order
import Mathlib.GroupTheory.Submonoid.Order

#align_import data.rat.star from "leanprover-community/mathlib"@"31c24aa72e7b3e5ed97a8412470e904f82b81004"

/-!
# Star ordered ring structure on ℚ

This file shows that `ℚ` is a `StarOrderedRing`. In particular, this means that every nonnegative
rational number is a sum of squares.
-/
open AddSubmonoid Set

namespace Int

@[simp] lemma addSubmonoid_closure_range_pow {n : ℕ} (hn : Even n) :
    closure (range fun x : ℤ ↦ x ^ n) = nonneg _ := by
  refine le_antisymm (closure_le.2 <| range_subset_iff.2 hn.pow_nonneg) fun x hx ↦ ?_
  have : x = x.natAbs • 1 ^ n := by simpa [eq_comm (a := x)] using hx
  rw [this]
  exact nsmul_mem (subset_closure $ mem_range_self _) _

@[simp]
lemma addSubmonoid_closure_range_mul_self : closure (range fun x : ℤ ↦ x * x) = nonneg _ := by
  simpa only [sq] using addSubmonoid_closure_range_pow even_two

instance Int.instStarOrderedRing : StarOrderedRing ℤ where
  le_iff a b := by simp [le_iff_exists_nonneg_add a b]

end Int
