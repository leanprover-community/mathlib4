/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux, Yaël Dillies
-/
import Mathlib.Algebra.GroupWithZero.Power
import Mathlib.Algebra.Parity
import Mathlib.Algebra.Star.Order
import Mathlib.GroupTheory.Submonoid.Order
import Mathlib.Tactic.FieldSimp

#align_import data.rat.star from "leanprover-community/mathlib"@"31c24aa72e7b3e5ed97a8412470e904f82b81004"

/-!
# Star ordered ring structure on ℚ

This file shows that `ℚ` is a `StarOrderedRing`. In particular, this means that every nonnegative
rational number is a sum of squares.
-/

open AddSubmonoid Set

namespace Rat

@[simp] lemma addSubmonoid_closure_range_pow {n : ℕ} (hn₀ : n ≠ 0) (hn : Even n) :
    closure (range fun x : ℚ ↦ x ^ n) = nonneg _ := by
  refine le_antisymm (closure_le.2 <| range_subset_iff.2 hn.pow_nonneg) fun x hx ↦ ?_
  suffices x = (x.num.natAbs * x.den ^ (n - 1)) • (x.den : ℚ)⁻¹ ^ n by
    rw [this]; exact nsmul_mem (subset_closure <| mem_range_self _) _
  refine (num_div_den _).symm.trans ?_
  field_simp [x.den_pos.ne']
  rw [Int.cast_natAbs, abs_of_nonneg (num_nonneg.2 hx), mul_assoc, ← pow_succ', Nat.sub_add_cancel]
  rwa [Nat.one_le_iff_ne_zero]

@[simp]
lemma addSubmonoid_closure_range_mul_self : closure (range fun x : ℚ ↦ x * x) = nonneg _ := by
  simpa only [sq] using addSubmonoid_closure_range_pow two_ne_zero even_two

instance instStarOrderedRing : StarOrderedRing ℚ where
  le_iff a b := by simp [le_iff_exists_nonneg_add a b]

end Rat
