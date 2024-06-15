/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Star.Order
import Mathlib.Algebra.Order.Monoid.Submonoid

/-!
# Star ordered ring structure on `ℤ`

This file shows that `ℤ` is a `StarOrderedRing`.
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

instance instStarOrderedRing : StarOrderedRing ℤ where
  le_iff a b := by simp [le_iff_exists_nonneg_add a b]

end Int
