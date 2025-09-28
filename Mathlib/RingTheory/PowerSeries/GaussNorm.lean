/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/

import Mathlib.Data.Real.Archimedean
import Mathlib.RingTheory.PowerSeries.Order

/-!
# Gauss norm for power series
This file defines the Gauss norm for power series. Given a power series `f` in `R⟦X⟧`, a function
`v : R → ℝ` and a real number `c`, the Gauss norm is defined as the supremum of the set of all
values of `v (f.coeff i) * c ^ i` for all `i : ℕ`.

In case `f` is a polynomial, `v` is a non-negative function with `v 0 = 0` and `c ≥ 0`,
`f.gaussNorm v c` reduces to the Gauss norm defined in
`Mathlib/RingTheory/Polynomial/GaussNorm.lean`, see `Polynomial.gaussNorm_coe_powerSeries`.

## Main Definitions and Results
* `PowerSeries.gaussNorm` is the supremum of the set of all values of `v (f.coeff i) * c ^ i`
  for all `i : ℕ`, where `f` is a power series in `R⟦X⟧`, `v : R → ℝ` is a function and `c` is a
  real number.
* `PowerSeries.gaussNorm_nonneg`: if `v` is a non-negative function, then the Gauss norm is
  non-negative.
* `PowerSeries.gaussNorm_eq_zero_iff`: if `v` is a non-negative function and `v x = 0 ↔ x = 0` for
  all `x : R` and `c` is positive, then the Gauss norm is zero if and only if the power series is
  zero.
-/

namespace PowerSeries

variable {R F : Type*} [Semiring R] [FunLike F R ℝ] (v : F) (c : ℝ) (f : R⟦X⟧)

/-- Given a power series `f` in `R⟦X⟧`, a function `v : R → ℝ` and a real number `c`, the Gauss norm
is defined as the supremum of the set of all values of `v (f.coeff i) * c ^ i` for all `i : ℕ`. -/
noncomputable def gaussNorm : ℝ := ⨆ i : ℕ, v (f.coeff i) * c ^ i

lemma le_gaussNorm (hbd : BddAbove {x | ∃ i, v (f.coeff i) * c ^ i = x}) (i : ℕ) :
    v (f.coeff i) * c ^ i ≤ f.gaussNorm v c := le_ciSup hbd i

@[simp]
theorem gaussNorm_zero [ZeroHomClass F R ℝ] : gaussNorm v c 0 = 0 := by simp [gaussNorm]

theorem gaussNorm_nonneg [NonnegHomClass F R ℝ] : 0 ≤ f.gaussNorm v c := by
  by_cases h : BddAbove (Set.range fun i ↦ v (f.coeff i) * c ^ i)
  · calc
    0 ≤ v (f.coeff 0) * c ^ 0 :=
      mul_nonneg (apply_nonneg v (f.coeff 0)) <| pow_nonneg (le_of_lt (zero_lt_one)) 0
    _ ≤ f.gaussNorm v c := le_ciSup h 0
  · simp [gaussNorm, h]

@[simp]
theorem gaussNorm_eq_zero_iff [ZeroHomClass F R ℝ] [NonnegHomClass F R ℝ] {v : F}
    (h_eq_zero : ∀ x : R, v x = 0 → x = 0) {f : R⟦X⟧} {c : ℝ} (hc : 0 < c)
    (hbd : BddAbove (Set.range fun i ↦ v (f.coeff i) * c ^ i)) :
    f.gaussNorm v c = 0 ↔ f = 0 := by
  refine ⟨?_, fun hf ↦ by simp [hf]⟩
  contrapose!
  intro hf
  apply ne_of_gt
  obtain ⟨n, hn⟩ := exists_coeff_ne_zero_iff_ne_zero.mpr hf
  calc
  0 < v (f.coeff n) * c ^ n := by
    have := fun h ↦ hn (h_eq_zero (coeff n f) h)
    positivity
  _ ≤ gaussNorm v c f := le_ciSup hbd n

end PowerSeries
