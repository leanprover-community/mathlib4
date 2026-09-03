/-
Copyright (c) 2024 Emilie Burgun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emilie Burgun
-/
module

public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.GroupTheory.Exponent
public import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Period of a group action

This module defines some helpful lemmas around [`MulAction.period`] and [`AddAction.period`].
The period of a point `a` by a group element `g` is the smallest `m` such that `g ^ m • a = a`
(resp. `(m • g) +ᵥ a = a`) for a given `g : G` and `a : α`.

If such an `m` does not exist,
then by convention `MulAction.period` and `AddAction.period` return 0.
-/

public section

namespace MonoidAction

universe u v
variable {α : Type v}
variable {G : Type u} [Group G] [MulAction G α]
variable {M : Type u} [Monoid M] [MulAction M α]

/-- If the action is periodic, then a lower bound for its period can be computed. -/
@[to_additive /-- If the action is periodic, then a lower bound for its period can be computed. -/]
theorem le_period {m : M} {a : α} {n : ℕ} (period_pos : 0 < period m a)
    (moved : ∀ k, 0 < k → k < n → m ^ k • a ≠ a) : n ≤ period m a :=
  le_of_not_gt fun period_lt_n =>
    moved _ period_pos period_lt_n <| pow_period_smul m a

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.le_period := le_period
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.le_period := _root_.AddMonoidAction.le_period

/-- If for some `n`, `m ^ n • a = a`, then `period m a ≤ n`. -/
@[to_additive /-- If for some `n`, `(n • m) +ᵥ a = a`, then `period m a ≤ n`. -/]
theorem period_le_of_fixed {m : M} {a : α} {n : ℕ} (n_pos : 0 < n) (fixed : m ^ n • a = a) :
    period m a ≤ n :=
  (isPeriodicPt_smul_iff.mpr fixed).minimalPeriod_le n_pos

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.period_le_of_fixed := period_le_of_fixed
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.period_le_of_fixed := _root_.AddMonoidAction.period_le_of_fixed

/-- If for some `n`, `m ^ n • a = a`, then `0 < period m a`. -/
@[to_additive /-- If for some `n`, `(n • m) +ᵥ a = a`, then `0 < period m a`. -/]
theorem period_pos_of_fixed {m : M} {a : α} {n : ℕ} (n_pos : 0 < n) (fixed : m ^ n • a = a) :
    0 < period m a :=
  (isPeriodicPt_smul_iff.mpr fixed).minimalPeriod_pos n_pos

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.period_pos_of_fixed := period_pos_of_fixed
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.period_pos_of_fixed := _root_.AddMonoidAction.period_pos_of_fixed

@[to_additive]
theorem period_eq_one_iff {m : M} {a : α} : period m a = 1 ↔ m • a = a :=
  ⟨fun eq_one => pow_one m ▸ eq_one ▸ pow_period_smul m a,
   fun fixed => le_antisymm
    (period_le_of_fixed one_pos (by simpa))
    (period_pos_of_fixed one_pos (by simpa))⟩

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.period_eq_one_iff := period_eq_one_iff
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.period_eq_zero_iff := _root_.AddMonoidAction.period_eq_zero_iff

/-- For any non-zero `n` less than the period of `m` on `a`, `a` is moved by `m ^ n`. -/
@[to_additive
/-- For any non-zero `n` less than the period of `m` on `a`, `a` is moved by `n • m`. -/]
theorem pow_smul_ne_of_lt_period {m : M} {a : α} {n : ℕ} (n_pos : 0 < n)
    (n_lt_period : n < period m a) : m ^ n • a ≠ a := fun a_fixed =>
  not_le_of_gt n_lt_period <| period_le_of_fixed n_pos a_fixed

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.pow_smul_ne_of_lt_period := pow_smul_ne_of_lt_period
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.nsmul_vadd_ne_of_lt_period :=
  _root_.AddMonoidAction.nsmul_vadd_ne_of_lt_period

section Identities

/-! ### `MulAction.period` for common group elements
-/

variable (M) in
@[to_additive (attr := simp)]
theorem period_one (a : α) : period (1 : M) a = 1 := period_eq_one_iff.mpr (one_smul M a)

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.period_one := period_one
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.period_zero := _root_.AddMonoidAction.period_zero

@[to_additive (attr := simp)]
theorem period_inv (g : G) (a : α) : period g⁻¹ a = period g a := by
  simp only [period_eq_minimalPeriod, Function.minimalPeriod_eq_minimalPeriod_iff,
    isPeriodicPt_smul_iff]
  intro n
  rw [smul_eq_iff_eq_inv_smul, eq_comm, ← zpow_natCast, inv_zpow, inv_inv, zpow_natCast]

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.period_inv := period_inv
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.period_neg := _root_.AddMonoidAction.period_neg

end Identities

section MonoidExponent

/-! ### `MulAction.period` and group exponents

The period of a given element `m : M` can be bounded by the `Monoid.exponent M` or `orderOf m`.
-/

@[to_additive]
theorem period_dvd_orderOf (m : M) (a : α) : period m a ∣ orderOf m := by
  rw [← pow_smul_eq_iff_period_dvd, pow_orderOf_eq_one, one_smul]

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.period_dvd_orderOf := period_dvd_orderOf
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.period_dvd_addOrderOf := _root_.AddMonoidAction.period_dvd_addOrderOf

@[to_additive]
theorem period_pos_of_orderOf_pos {m : M} (order_pos : 0 < orderOf m) (a : α) :
    0 < period m a :=
  Nat.pos_of_dvd_of_pos (period_dvd_orderOf m a) order_pos

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.period_pos_of_orderOf_pos := period_pos_of_orderOf_pos
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.period_pos_of_addOrderOf_pos :=
  _root_.AddMonoidAction.period_pos_of_addOrderOf_pos

@[to_additive]
theorem period_le_orderOf {m : M} (order_pos : 0 < orderOf m) (a : α) :
    period m a ≤ orderOf m :=
  Nat.le_of_dvd order_pos (period_dvd_orderOf m a)

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.period_le_orderOf := period_le_orderOf
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.period_le_addOrderOf := _root_.AddMonoidAction.period_le_addOrderOf

@[to_additive]
theorem period_dvd_exponent (m : M) (a : α) : period m a ∣ Monoid.exponent M := by
  rw [← pow_smul_eq_iff_period_dvd, Monoid.pow_exponent_eq_one, one_smul]

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.period_dvd_exponent := period_dvd_exponent
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.period_dvd_exponent := _root_.AddMonoidAction.period_dvd_exponent

@[to_additive]
theorem period_pos_of_exponent_pos (exp_pos : 0 < Monoid.exponent M) (m : M) (a : α) :
    0 < period m a :=
  Nat.pos_of_dvd_of_pos (period_dvd_exponent m a) exp_pos

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.period_pos_of_exponent_pos := period_pos_of_exponent_pos
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.period_pos_of_exponent_pos :=
  _root_.AddMonoidAction.period_pos_of_exponent_pos

@[to_additive]
theorem period_le_exponent (exp_pos : 0 < Monoid.exponent M) (m : M) (a : α) :
    period m a ≤ Monoid.exponent M :=
  Nat.le_of_dvd exp_pos (period_dvd_exponent m a)

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.period_le_exponent := period_le_exponent
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.period_le_exponent := _root_.AddMonoidAction.period_le_exponent

variable (α)

@[to_additive]
theorem period_bounded_of_exponent_pos (exp_pos : 0 < Monoid.exponent M) (m : M) :
    BddAbove (Set.range (fun a : α => period m a)) := by
  use Monoid.exponent M
  simpa [upperBounds] using period_le_exponent exp_pos _

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.period_bounded_of_exponent_pos := period_bounded_of_exponent_pos
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.period_bounded_of_exponent_pos :=
  _root_.AddMonoidAction.period_bounded_of_exponent_pos

end MonoidExponent


end MonoidAction
