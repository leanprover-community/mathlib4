/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
module

public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.Tactic.LinearCombination

/-!
# The formal logarithmic derivative of a power series

For a formal power series `f` over a commutative ring `R` we define
`PowerSeries.logDeriv f = f' * f⁻¹`, using `Ring.inverse` so that the definition is total. On units
this is the honest logarithmic derivative, and it is there that it has the expected properties.

Unlike `PowerSeries.log`, this needs no `ℚ`-algebra structure: it is purely formal and is available
over an arbitrary commutative ring. It is the algebraic counterpart of `logDeriv` for functions.

## Main definitions

* `PowerSeries.logDeriv`: the formal logarithmic derivative `f' * f⁻¹`.

## Main results

* `PowerSeries.logDeriv_mul`: on units, the logarithmic derivative turns products into sums.
* `PowerSeries.map_derivative`: the formal derivative commutes with `PowerSeries.map`.
* `PowerSeries.map_logDeriv`: on units, the logarithmic derivative commutes with `PowerSeries.map`.
-/

@[expose] public section

namespace PowerSeries

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The formal logarithmic derivative `f' * f⁻¹` of a power series, defined via `Ring.inverse`
so that it is total. It behaves as expected on units; see `PowerSeries.logDeriv_mul`. -/
noncomputable def logDeriv (f : R⟦X⟧) : R⟦X⟧ := derivative R f * Ring.inverse f

theorem logDeriv_def (f : R⟦X⟧) : logDeriv f = derivative R f * Ring.inverse f := rfl

/-- Multiplying the logarithmic derivative of a unit by that unit recovers the derivative. -/
theorem logDeriv_mul_self {f : R⟦X⟧} (hf : IsUnit f) : logDeriv f * f = derivative R f := by
  rw [logDeriv, mul_assoc, Ring.inverse_mul_cancel f hf, mul_one]

/-- **The logarithmic derivative turns products of units into sums.** -/
theorem logDeriv_mul {f g : R⟦X⟧} (hf : IsUnit f) (hg : IsUnit g) :
    logDeriv (f * g) = logDeriv f + logDeriv g := by
  have hfi : f * Ring.inverse f = 1 := Ring.mul_inverse_cancel f hf
  have hgi : g * Ring.inverse g = 1 := Ring.mul_inverse_cancel g hg
  simp only [logDeriv, Derivation.leibniz, Ring.mul_inverse_rev]
  linear_combination (derivative R f * Ring.inverse f) * hgi
    + (derivative R g * Ring.inverse g) * hfi

/-- The formal derivative commutes with `PowerSeries.map`. -/
theorem map_derivative (ψ : R →+* S) (f : R⟦X⟧) :
    map ψ (derivative R f) = derivative S (map ψ f) := by
  ext n
  rw [coeff_map, coeff_derivative, coeff_derivative, coeff_map, map_mul, map_add,
    map_natCast, map_one]

/-- `PowerSeries.map` preserves the `Ring.inverse` of a unit. -/
theorem map_ringInverse (ψ : R →+* S) {u : R⟦X⟧} (hu : IsUnit u) :
    map ψ (Ring.inverse u) = Ring.inverse (map ψ u) := by
  have hu' : IsUnit (map ψ u) := hu.map (map ψ)
  have h1 : map ψ u * map ψ (Ring.inverse u) = 1 := by
    rw [← map_mul, Ring.mul_inverse_cancel u hu, map_one]
  calc map ψ (Ring.inverse u)
      = (Ring.inverse (map ψ u) * map ψ u) * map ψ (Ring.inverse u) := by
        rw [Ring.inverse_mul_cancel _ hu', one_mul]
    _ = Ring.inverse (map ψ u) * 1 := by rw [mul_assoc, h1]
    _ = Ring.inverse (map ψ u) := mul_one _

/-- **The logarithmic derivative of a unit commutes with `PowerSeries.map`.** -/
theorem map_logDeriv (ψ : R →+* S) {u : R⟦X⟧} (hu : IsUnit u) :
    map ψ (logDeriv u) = logDeriv (map ψ u) := by
  rw [logDeriv, logDeriv, map_mul, map_derivative, map_ringInverse ψ hu]

end PowerSeries
