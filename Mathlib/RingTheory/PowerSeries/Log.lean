/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.WellKnown

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
* `PowerSeries.derivative_log`: The derivative of `log(1+X)` is the geometric series
  `∑ (-1)^n · Xⁿ = 1/(1+X)`.
* `PowerSeries.derivative_log_mul_one_add_X`: `(log(1+X))' · (1 + X) = 1`.
* `PowerSeries.subst_exp_log`: `exp` and `log` are mutually inverse:
  substituting `log(1+X)` into `exp` yields `1 + X`.
* `PowerSeries.subst_log_exp_sub_one`: Substituting `exp X - 1` into `log(1+X)`
  yields `X`.
* `PowerSeries.logOf_exp`: The reformulation `logOf (exp X) = X`, where `logOf f` is
  `log(1+X)` evaluated at `f - 1`.
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
theorem derivative_log : d⁄dX A (log A) = mk fun n ↦ (-1 : A) ^ n := by
  ext n
  have : (n + 1) = algebraMap ℚ A (n + 1) := by simp
  rw [coeff_derivative, coeff_log, coeff_mk]
  grind

@[deprecated (since := "2026-08-29")] alias deriv_log := derivative_log

/-- The derivative of `log(1+X)` is the inverse of `1 + X`. -/
theorem derivative_log_mul_one_add_X : d⁄dX A (log A) * (1 + X) = 1 := by
  rw [derivative_log, mk_neg_one_pow_mul_one_add_eq_one]

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

/-! ## Log and exp as inverses -/

omit [Algebra ℚ A] in
theorem eq_of_derivative_mul_one_add_X_eq_self [IsAddTorsionFree A]
    {g : A⟦X⟧} (hderiv : d⁄dX A g * (1 + X) = g) :
    g = constantCoeff g • (1 + X) := by
  have : Invertible (1 + X : A⟦X⟧) := (isUnit_iff_constantCoeff.mpr (by simp)).invertible
  have hcu : constantCoeff (⅟(1 + X) : A⟦X⟧) = 1 := by
    have h := congrArg (constantCoeff (R := A)) (mul_invOf_self (1 + X : A⟦X⟧))
    rw [map_mul] at h
    simpa using h
  have hg : g * ⅟(1 + X) = d⁄dX A g := by
    conv_lhs => rw [← hderiv]
    rw [mul_assoc, mul_invOf_self, mul_one]
  have key : g * ⅟(1 + X) = C (constantCoeff g) := by
    refine derivative.ext ?_ ?_
    · simp only [Derivation.leibniz, derivative_invOf, map_add, derivative_one, derivative_X,
        zero_add, derivative_C, mul_one, smul_eq_mul, ← hg]
      ring
    · simp [hcu]
  rw [smul_eq_C_mul, ← key, mul_assoc, invOf_mul_self, mul_one]

variable (A) in
theorem subst_exp_log : (exp A).subst (log A) = 1 + X := by
  have : IsAddTorsionFree A := IsAddTorsionFree.of_module_rat A
  have hderiv : d⁄dX A ((exp A).subst (log A)) * (1 + X) = (exp A).subst (log A) := by
    rw [derivative_subst (hg := HasSubst.log), derivative_exp, mul_assoc,
      derivative_log_mul_one_add_X, mul_one]
  have hconst : constantCoeff ((exp A).subst (log A)) = 1 := by
    rw [constantCoeff_eq, constantCoeff_subst_of_constantCoeff_zero constantCoeff_log,
      constantCoeff_exp, map_one]
  have h := eq_of_derivative_mul_one_add_X_eq_self hderiv
  rwa [hconst, one_smul] at h

variable (A) in
theorem subst_log_exp_sub_one : (log A).subst (exp A - 1) = X := by
  apply subst_eq_X_of_subst_eq_X (P := exp A - 1)
  · simp [constantCoeff_exp]
  · simp [coeff_exp]
  · exact HasSubst.log
  · rw [subst_sub HasSubst.log, subst_exp_log A, ← coe_substAlgHom HasSubst.log (R := A), map_one]
    ring

variable (A) in
@[simp]
theorem logOf_exp : logOf (exp A) = X :=
  subst_log_exp_sub_one A

end PowerSeries

end
