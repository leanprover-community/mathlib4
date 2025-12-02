/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux, Yaël Dillies
-/
module

public import Mathlib.Algebra.GroupWithZero.Commute
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Data.NNRat.Order
public import Mathlib.Tactic.FieldSimp

/-!
# Star ordered ring structures on `ℚ` and `ℚ≥0`

This file shows that `ℚ` and `ℚ≥0` are `StarOrderedRing`s. In particular, this means that every
nonnegative rational number is a sum of squares.
-/

@[expose] public section

open AddSubmonoid Set
open scoped NNRat

namespace NNRat

@[simp] lemma addSubmonoid_closure_range_pow {n : ℕ} (hn₀ : n ≠ 0) :
    closure (range fun x : ℚ≥0 ↦ x ^ n) = ⊤ := by
  refine (eq_top_iff' _).2 fun x ↦ ?_
  suffices x = (x.num * x.den ^ (n - 1)) • (x.den : ℚ≥0)⁻¹ ^ n by
    rw [this]
    exact nsmul_mem (subset_closure <| mem_range_self _) _
  rw [nsmul_eq_mul]
  push_cast
  rw [mul_assoc, pow_sub₀, pow_one, mul_right_comm, ← mul_pow, mul_inv_cancel₀, one_pow, one_mul,
    ← div_eq_mul_inv, num_div_den]
  all_goals simp [x.den_pos.ne', Nat.one_le_iff_ne_zero, *]

@[simp] lemma addSubmonoid_closure_range_mul_self : closure (range fun x : ℚ≥0 ↦ x * x) = ⊤ := by
  simpa only [sq] using addSubmonoid_closure_range_pow two_ne_zero

instance instStarOrderedRing : StarOrderedRing ℚ≥0 where
  le_iff a b := by simp [eq_comm, le_iff_exists_nonneg_add (a := a)]

end NNRat

namespace Rat

@[simp] lemma addSubmonoid_closure_range_pow {n : ℕ} (hn₀ : n ≠ 0) (hn : Even n) :
    closure (range fun x : ℚ ↦ x ^ n) = nonneg _ := by
  convert (AddMonoidHom.map_mclosure NNRat.coeHom <| range fun x ↦ x ^ n).symm
  · have (x : ℚ) : ∃ y : ℚ≥0, y ^ n = x ^ n := ⟨x.nnabs, by simp [hn.pow_abs]⟩
    simp [subset_antisymm_iff, range_subset_iff, this]
  · ext
    simp [NNRat.addSubmonoid_closure_range_pow hn₀, NNRat.exists]

@[simp]
lemma addSubmonoid_closure_range_mul_self : closure (range fun x : ℚ ↦ x * x) = nonneg _ := by
  simpa only [sq] using addSubmonoid_closure_range_pow two_ne_zero even_two

instance instStarOrderedRing : StarOrderedRing ℚ where
  le_iff a b := by simp [eq_comm, le_iff_exists_nonneg_add (a := a)]

end Rat
