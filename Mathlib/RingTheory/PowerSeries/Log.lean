/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathlib contributors
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.RingTheory.PowerSeries.Derivative

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
* `PowerSeries.deriv_log`: The derivative of `log(1+X)` is the geometric series
  `∑ (-1)^n · Xⁿ = 1/(1+X)`.
-/

@[expose] public section

namespace PowerSeries

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- Power series for `log(1 + X) = X - X²/2 + X³/3 - ⋯`. -/
def log : PowerSeries A :=
  mk fun n => if n = 0 then 0 else algebraMap ℚ A ((-1 : ℚ) ^ (n + 1) / n)

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

/-- The derivative of `log(1+X)` is the geometric series `1 - X + X² - X³ + ⋯ = 1/(1+X)`. -/
theorem deriv_log : d⁄dX A (log A) = mk fun n => algebraMap ℚ A ((-1 : ℚ) ^ n) := by
  ext n
  simp only [coeff_derivative, coeff_log, coeff_mk, Nat.add_eq_zero_iff, one_ne_zero,
    and_false, ↓reduceIte, show (↑n + 1 : A) = algebraMap ℚ A (n + 1) from by simp, ← map_mul]
  congr 1; push_cast; field_simp; ring

end PowerSeries

end
