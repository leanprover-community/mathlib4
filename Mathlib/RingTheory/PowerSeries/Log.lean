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
* `PowerSeries.exp_subst_log`: `exp` and `log` are mutually inverse:
  substituting `log(1+X)` into `exp` yields `1 + X`.
* `PowerSeries.log_subst_exp_sub_one`: Conversely, substituting `exp X - 1` into `log(1+X)`
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


/-! ## Log and exp as inverses -/

omit [Algebra ℚ A] in
private theorem eq_of_deriv_mul_one_add_X_eq_self [IsAddTorsionFree A]
    {g : A⟦X⟧} {c : A} (hderiv : d⁄dX A g * (1 + X) = g) (hconst : constantCoeff g = c) :
    g = c • (1 + X) := by
  have hcoeff : ∀ n, coeff n (d⁄dX A g * (1 + X)) = coeff n g := fun n => by rw [hderiv]
  have hrec : ∀ n : ℕ, (↑(n + 2) : A) * coeff (n + 2) g = -↑n * coeff (n + 1) g := fun n => by
    have h := hcoeff (n + 1)
    rw [mul_add, mul_one, map_add, coeff_succ_mul_X, coeff_derivative, coeff_derivative] at h
    push_cast at h ⊢
    linear_combination h
  have h1 : coeff 1 g = c := by
    have h := hcoeff 0
    simp only [mul_add, mul_one, map_add, coeff_zero_mul_X, add_zero, coeff_derivative,
      Nat.cast_zero, zero_add] at h
    rw [h, coeff_zero_eq_constantCoeff, hconst]
  have h2 : ∀ n : ℕ, coeff (n + 2) g = 0 := by
    intro n
    induction n with
    | zero =>
      have h := hrec 0
      simp only [Nat.cast_zero, neg_zero, zero_mul, ← nsmul_eq_mul] at h
      exact (nsmul_eq_zero_iff_right (by omega : (2 : ℕ) ≠ 0)).mp h
    | succ m ih =>
      have h := hrec (m + 1)
      rw [ih, mul_zero, ← nsmul_eq_mul] at h
      exact (nsmul_eq_zero_iff_right (by omega : (m + 3 : ℕ) ≠ 0)).mp h
  ext n
  match n with
  | 0 => simp [coeff_zero_eq_constantCoeff, hconst]
  | 1 => simp [h1]
  | n + 2 => simp [h2, coeff_X]

private theorem geom_mul_one_add_X :
    (mk fun n ↦ algebraMap ℚ A ((-1 : ℚ) ^ n)) * (1 + X : A⟦X⟧) = 1 := by
  ext n
  rw [mul_add, mul_one, map_add, coeff_one]
  match n with
  | 0 => simp
  | n + 1 =>
    rw [coeff_succ_mul_X, coeff_mk, coeff_mk, pow_succ, ← map_add,
      show (-1 : ℚ) ^ n * -1 + (-1) ^ n = 0 by ring, map_zero]
    simp

theorem exp_subst_log [IsAddTorsionFree A] : (exp A).subst (log A) = 1 + X := by
  have hderiv : d⁄dX A ((exp A).subst (log A)) * (1 + X) = (exp A).subst (log A) := by
    rw [derivative_subst (hg := HasSubst.log), derivative_exp, deriv_log, mul_assoc,
      geom_mul_one_add_X, mul_one]
  have hconst : constantCoeff ((exp A).subst (log A)) = 1 := by
    change MvPowerSeries.constantCoeff _ = _
    rw [constantCoeff_subst_of_constantCoeff_zero constantCoeff_log, constantCoeff_exp, map_one]
  simpa using eq_of_deriv_mul_one_add_X_eq_self hderiv hconst

variable (A) in
theorem log_subst_exp_sub_one [IsAddTorsionFree A] :
    (log A).subst (exp A - 1) = X := by
  apply derivative.ext
  · rw [derivative_X, derivative_subst (hg := HasSubst.exp_sub_one), deriv_log, map_sub,
      derivative_exp, (d⁄dX A).map_one_eq_zero, sub_zero]
    have h : ((mk fun n ↦ algebraMap ℚ A ((-1 : ℚ) ^ n)) * (1 + X : A⟦X⟧)).subst
        (exp A - 1) = (1 : A⟦X⟧).subst (exp A - 1) := congrArg _ geom_mul_one_add_X
    rw [subst_mul HasSubst.exp_sub_one, subst_add HasSubst.exp_sub_one,
      ← coe_substAlgHom HasSubst.exp_sub_one (R := A), map_one,
      coe_substAlgHom, subst_X HasSubst.exp_sub_one] at h
    rwa [show (1 : A⟦X⟧) + (exp A - 1) = exp A from by ring] at h
  · change MvPowerSeries.constantCoeff _ = _
    rw [constantCoeff_subst_of_constantCoeff_zero (show constantCoeff (exp A - 1 : A⟦X⟧) = 0
      by simp [constantCoeff_exp]), constantCoeff_log, map_zero, constantCoeff_X]

variable (A) in
theorem logOf_exp [IsAddTorsionFree A] : logOf (exp A) = X :=
  log_subst_exp_sub_one A

end PowerSeries

end
