/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# Logarithmic Power Series

This file defines the logarithmic power series `log A = ∑ (-1)^(n+1)/n · Xⁿ`
over ℚ-algebras and establishes its key properties.

## Main definitions

* `PowerSeries.log`: The power series `log(1+X) = X - X²/2 + X³/3 - ⋯`.

## Main results

* `PowerSeries.coeff_log`: The coefficient of `log A` at `n` is `(-1)^(n+1)/n` for `n ≥ 1`,
  and `0` for `n = 0`.
* `PowerSeries.constantCoeff_log`: The constant term of `log A` is `0`.
* `PowerSeries.map_log`: `log` is preserved by ring homomorphisms between ℚ-algebras.
* `PowerSeries.coeff_one_log`: The coefficient of `log A` at `1` is `1`.
* `PowerSeries.order_log`: The order of `log A` is `1`.
* `PowerSeries.deriv_log`: The derivative of `log(1+X)` is the geometric series
  `∑ (-1)^n · Xⁿ = 1/(1+X)`.
-/

@[expose] public section

namespace PowerSeries

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- Power series for `log(1 + X) = X - X²/2 + X³/3 - ⋯`. -/
def log : PowerSeries A :=
  mk fun n ↦ if n = 0 then 0 else algebraMap ℚ A ((-1 : ℚ) ^ (n + 1) / n)

variable {A}

@[simp]
theorem coeff_log (n : ℕ) :
    coeff n (log A) = if n = 0 then 0 else algebraMap ℚ A ((-1 : ℚ) ^ (n + 1) / n) :=
  coeff_mk _ _

@[simp]
theorem constantCoeff_log : constantCoeff (log A) = 0 := by
  simp [← coeff_zero_eq_constantCoeff_apply]

@[simp]
theorem map_log {A' : Type*} [CommRing A'] [Algebra ℚ A'] (f : A →+* A') :
    map f (log A) = log A' := by
  ext n; simp only [coeff_map, coeff_log]; split_ifs <;> simp [RingHom.map_rat_algebraMap]

theorem coeff_one_log : coeff 1 (log A) = 1 := by simp

theorem order_log [Nontrivial A] : (log A).order = 1 :=
  order_eq_nat.mpr ⟨by simp, fun i hi ↦ by simp [Nat.lt_one_iff.mp hi]⟩

/-- The derivative of `log(1+X)` is the geometric series `1 - X + X² - X³ + ⋯ = 1/(1+X)`. -/
theorem deriv_log : d⁄dX A (log A) = mk fun n ↦ algebraMap ℚ A ((-1 : ℚ) ^ n) := by
  ext n
  have : (n + 1) = algebraMap ℚ A (n + 1) := by simp
  rw [coeff_derivative, coeff_log, coeff_mk]
  grind

/-! ## Substitution -/

theorem HasSubst.log : HasSubst (log A) :=
  HasSubst.of_constantCoeff_zero' constantCoeff_log

theorem HasSubst.exp_sub_one : HasSubst (exp A - 1) :=
  HasSubst.of_constantCoeff_zero' (by simp [constantCoeff_exp])

/-- `logOf f` is `log(1+X)` substituted at `f - 1`, i.e., `(f-1) - (f-1)²/2 + (f-1)³/3 - ⋯`. -/
noncomputable def logOf (f : A⟦X⟧) : A⟦X⟧ :=
  (log A).subst (f - 1)

theorem logOf_eq (f : A⟦X⟧) : logOf f = (log A).subst (f - 1) := rfl

theorem constantCoeff_logOf {f : A⟦X⟧} (hf : constantCoeff f = 1) :
    constantCoeff (logOf f) = 0 := by
  rw [logOf_eq]
  have h : MvPowerSeries.constantCoeff (f - 1 : A⟦X⟧) = 0 := by
    rw [map_sub, map_one, ← constantCoeff_eq, hf, sub_self]
  exact constantCoeff_subst_eq_zero h _ constantCoeff_log

variable (A) in
@[simp]
theorem logOf_one_add_X : logOf (1 + X : A⟦X⟧) = log A := by
  rw [logOf_eq, add_sub_cancel_left, X_subst]

end PowerSeries

end
