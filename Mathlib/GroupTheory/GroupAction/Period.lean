/-
Copyright (c) 2024 Emilie Burgun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emilie Burgun
-/

import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Dynamics.PeriodicPts
import Mathlib.GroupTheory.Exponent

/-!
# Period of a group action

This module defines some helpful lemmas around [`MulAction.period`] and [`AddAction.period`].
The period of a point `a` by a group element `g` is the smallest `m` such that `g ^ m • a = a`
(resp. `(m • g) +ᵥ a = a`) for a given `g : G` and `a : α`.

If such an `m` does not exist,
then by convention `MulAction.period` and `AddAction.period` return 0.
-/

namespace MulAction

universe u v
variable {α : Type v}
variable {G : Type u} [Group G] [MulAction G α]
variable {M : Type u} [Monoid M] [MulAction M α]

/-- If the action is periodic, then a lower bound for its period can be computed. -/
@[to_additive]
theorem period_gt_of_moved {m : M} {a : α} {n : ℕ} (period_pos : 0 < period m a)
    (moved : ∀ k, 0 < k → k < n → m^k • a ≠ a) : n ≤ period m a := by
  by_contra period_le_n
  rw [not_le] at period_le_n
  apply moved _ period_pos period_le_n
  exact smul_pow_period_fixed m a

/-- If for some `n`, `m ^ n • a = a`, then `period m a ≤ n`. -/
@[to_additive]
theorem period_le_of_fixed {m : M} {a : α} {n : ℕ} (n_pos : 0 < n) (fixed : m ^ n • a = a) :
    period m a ≤ n := by
  rw [period_eq_minimalPeriod]
  rw [fixed_iff_isPeriodicPt] at fixed
  exact Function.IsPeriodicPt.minimalPeriod_le n_pos fixed

/-- If for some `n`, `m ^ n • a = a`, then `0 < period m a`. -/
@[to_additive]
theorem period_pos_of_fixed {m : M} {a : α} {n : ℕ} (n_pos : 0 < n) (fixed : m ^ n • a = a) :
    0 < period m a := by
  rw [fixed_iff_isPeriodicPt] at fixed
  rw [period_eq_minimalPeriod]
  exact Function.IsPeriodicPt.minimalPeriod_pos n_pos fixed

@[to_additive]
theorem period_eq_one_of_fixed {m : M} {a : α} (fixed : m • a = a) : period m a = 1 := by
  symm
  rw [← pow_one m] at fixed
  refine Nat.eq_of_le_of_lt_succ (period_le_of_fixed Nat.one_pos fixed) ?pos
  rw [Nat.lt_add_left_iff_pos]
  exact period_pos_of_fixed Nat.one_pos fixed

/-- For any non-zero `n` less than the period, `a` is moved by `m^n`. -/
@[to_additive]
theorem moved_of_lt_period {m : M} {a : α} {n : ℕ} (n_pos : 0 < n) (n_lt_period : n < period m a) :
    m^n • a ≠ a := by
  intro a_fixed
  apply Nat.not_le.mpr n_lt_period
  exact period_le_of_fixed n_pos a_fixed

section MonoidExponent

/-! ## `MulAction.period` and group exponents

The period of a given element `m : M` can be bounded by the `Monoid.exponent M` or `orderOf m`.
-/

@[to_additive]
theorem period_pos_of_orderOf_pos {m : M} (order_pos : 0 < orderOf m) (a : α):
    0 < period m a := by
  apply period_pos_of_fixed order_pos
  rw [pow_orderOf_eq_one, one_smul]

@[to_additive]
theorem period_le_orderOf {m : M} (order_pos : 0 < orderOf m) (a : α):
    period m a ≤ orderOf m := by
  apply period_le_of_fixed order_pos
  rw [pow_orderOf_eq_one, one_smul]

@[to_additive]
theorem period_pos_of_exponent_pos (exp_pos : 0 < Monoid.exponent M) (m : M) (a : α) :
    0 < period m a := by
  apply period_pos_of_fixed exp_pos
  rw [Monoid.pow_exponent_eq_one, one_smul]

@[to_additive]
theorem period_le_exponent (exp_pos : 0 < Monoid.exponent M) (m : M) (a : α) :
    period m a ≤ Monoid.exponent M := by
  apply period_le_of_fixed exp_pos
  rw [Monoid.pow_exponent_eq_one, one_smul]

variable (α)

@[to_additive]
theorem period_bounded_of_exponent_pos (exp_pos : 0 < Monoid.exponent M) (m : M) :
    BddAbove (Set.range (fun a : α => period m a)) := by
  use Monoid.exponent M
  simp [upperBounds]
  apply period_le_exponent exp_pos

end MonoidExponent


end MulAction
