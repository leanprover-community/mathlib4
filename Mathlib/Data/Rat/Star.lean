/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux, Yaël Dillies
-/
import Mathlib.Algebra.GroupWithZero.Power
import Mathlib.Algebra.Parity
import Mathlib.Algebra.Star.Order
import Mathlib.Data.NNRat.Star
import Mathlib.GroupTheory.Submonoid.Order
import Mathlib.Tactic.FieldSimp

#align_import data.rat.star from "leanprover-community/mathlib"@"31c24aa72e7b3e5ed97a8412470e904f82b81004"

/-!
# Star ordered ring structure on ℚ

This file shows that `ℚ` is a `StarOrderedRing`. In particular, this means that every nonnegative
rational number is a sum of squares.
-/

open AddSubmonoid Set
open scoped NNRat

namespace Rat

@[simp] lemma addSubmonoid_closure_range_pow {n : ℕ} (hn₀ : n ≠ 0) (hn : Even n) :
    closure (range fun x : ℚ ↦ x ^ n) = nonneg _ := by
  convert (AddMonoidHom.map_mclosure NNRat.coeHom $ range fun x ↦ x ^ n).symm
  · have (x : ℚ) : ∃ y : ℚ≥0, y ^ n = x ^ n := ⟨x.nnabs, by simp [hn.pow_abs]⟩
    simp [subset_antisymm_iff, range_subset_iff, this]
  · ext
    simp [NNRat.addSubmonoid_closure_range_pow hn₀, NNRat.exists]

@[simp]
lemma addSubmonoid_closure_range_mul_self : closure (range fun x : ℚ ↦ x * x) = nonneg _ := by
  simpa only [sq] using addSubmonoid_closure_range_pow two_ne_zero even_two

instance instStarOrderedRing : StarOrderedRing ℚ where
  le_iff a b := by simp [le_iff_exists_nonneg_add a b]

end Rat
