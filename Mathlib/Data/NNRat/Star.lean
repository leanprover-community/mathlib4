/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.GroupWithZero.Power
import Mathlib.Algebra.Star.Order
import Mathlib.Data.NNRat.Lemmas

/-!
# Star ordered ring structure on ℚ≥0

This file shows that `ℚ≥0` is a `StarOrderedRing`. In particular, this means that every nonnegative
rational number is a sum of squares.
-/

open AddSubmonoid Set

namespace NNRat

@[simp] lemma addSubmonoid_closure_range_pow {n : ℕ} (hn₀ : n ≠ 0) :
    closure (range fun x : ℚ≥0 ↦ x ^ n) = ⊤ := by
  refine (eq_top_iff' _).2 fun x ↦ ?_
  suffices x = (x.num * x.den ^ (n - 1)) • (x.den : ℚ≥0)⁻¹ ^ n by
    rw [this]
    exact nsmul_mem (subset_closure <| mem_range_self _) _
  rw [nsmul_eq_mul]
  push_cast
  rw [mul_assoc, pow_sub₀, pow_one, mul_right_comm, ← mul_pow, mul_inv_cancel, one_pow, one_mul,
    ← div_eq_mul_inv, num_div_den]
  all_goals simp [x.den_pos.ne', Nat.one_le_iff_ne_zero, *]

@[simp] lemma addSubmonoid_closure_range_mul_self : closure (range fun x : ℚ≥0 ↦ x * x) = ⊤ := by
  simpa only [sq] using addSubmonoid_closure_range_pow two_ne_zero

instance instStarOrderedRing : StarOrderedRing ℚ≥0 where
  le_iff a b := by simp [le_iff_exists_nonneg_add a b]

end NNRat
