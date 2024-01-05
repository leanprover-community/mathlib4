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

This module defines the period of a group action ([`MulAction.period`] and [`AddAction.period`]),
which is the smallest `m` such that `g ^ m • a = a` (resp. `(m • g) +ᵥ a = a`) for a given `g : G` and `a : α`.

If such an `m` does not exist, then by convention `MulAction.period` and `AddAction.period` return 0.
-/

namespace MulAction

universe u v
variable {α : Type v}
variable {G : Type u} [Group G] [MulAction G α]
variable {M : Type u} [Monoid M] [MulAction M α]

/--
The period of a multiplicative action of `g` on `a` is the smallest `n` such that `g ^ n • a = a`,
or `0` if such an `n` does not exist.
-/
@[to_additive "The period of an additive action of `g` on `a` is the smallest `n` such that `(n • g) +ᵥ a = a`, or `0` if such an `n` does not exist."]
noncomputable def period (m : M) (a : α) : ℕ := Function.minimalPeriod (fun x => m • x) a

@[to_additive]
theorem period_eq_minimalPeriod {m : M} {a : α} :
    MulAction.period m a = Function.minimalPeriod (fun x => m • x) a := rfl

@[to_additive]
lemma smul_pow_eq_function_pow (m : M) (a : α) (n : ℕ): m ^ n • a = (fun x => m • x)^[n] a := by
  rw [smul_iterate]

/-- `m ^ (period m a)` fixes `a` -/
@[to_additive (attr := simp) "`(period m a) • m` fixes `a`"]
theorem smul_pow_period_fixed (m : M) (a : α) : m ^ (period m a) • a = a := by
  rw [period_eq_minimalPeriod, smul_pow_eq_function_pow, Function.iterate_minimalPeriod]

/-- If the action is periodic, then a lower bound for its period can be computed. -/
@[to_additive]
theorem period_gt_of_moved {m : M} {a : α} {n : ℕ} (period_pos : 0 < period m a)
    (moved : ∀ k, 0 < k → k < n → m^k • a ≠ a) : n ≤ period m a := by
  by_contra period_le_n
  rw [not_le] at period_le_n
  apply moved _ period_pos period_le_n
  exact smul_pow_period_fixed m a

@[to_additive]
lemma fixed_iff_isPeriodicPt {m : M} {a : α} {n : ℕ} :
    m ^ n • a = a ↔ Function.IsPeriodicPt (fun x => m • x) n a := by
  rw [smul_pow_eq_function_pow]
  rfl

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

theorem period_pos_of_orderOf_pos {m : M} (order_pos : 0 < orderOf m) (a : α):
    0 < period m a := by
  apply period_pos_of_fixed order_pos
  rw [pow_orderOf_eq_one, one_smul]

theorem period_le_orderOf {m : M} (order_pos : 0 < orderOf m) (a : α):
    period m a ≤ orderOf m := by
  apply period_le_of_fixed order_pos
  rw [pow_orderOf_eq_one, one_smul]

theorem period_pos_of_exponent_pos (exp_pos : 0 < Monoid.exponent M) (m : M) (a : α) :
    0 < period m a := by
  apply period_pos_of_fixed exp_pos
  rw [Monoid.pow_exponent_eq_one, one_smul]

theorem period_le_exponent (exp_pos : 0 < Monoid.exponent M) (m : M) (a : α) :
    period m a ≤ Monoid.exponent M := by
  apply period_le_of_fixed exp_pos
  rw [Monoid.pow_exponent_eq_one, one_smul]

variable (α)

theorem period_bounded_of_exponent_pos (exp_pos : 0 < Monoid.exponent M) (m : M) :
    BddAbove (Set.range (fun a : α => period m a)) := by
  use Monoid.exponent M
  simp [upperBounds]
  apply period_le_exponent exp_pos

end MonoidExponent

end MulAction
