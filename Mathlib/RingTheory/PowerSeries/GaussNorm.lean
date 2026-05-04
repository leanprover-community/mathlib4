/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/
module

public import Mathlib.Data.Real.Archimedean
public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.RingTheory.MvPowerSeries.GaussNorm

/-!
# Gauss norm for power series
This file defines the Gauss norm for power series using the gaussNorm for multivariate power series.
Given a power series `f` in `R⟦X⟧`, a function `v : R → ℝ` and a real number `c`, the Gauss norm is
defined as the supremum of the set of all values of `v (f.coeff i) * c ^ i` for all `i : ℕ`.

In case `f` is a polynomial, `v` is a non-negative function with `v 0 = 0` and `c ≥ 0`,
`f.gaussNorm v c` reduces to the Gauss norm defined in
`Mathlib/RingTheory/Polynomial/GaussNorm.lean`, see `Polynomial.gaussNorm_coe_powerSeries`.

## Main Definitions and Results
* Using `PowerSeries.gaussNorm_eq`, `PowerSeries.gaussNorm` is the supremum of the set of all values
  of `v (f.coeff i) * c ^ i` for all `i : ℕ`, where `f` is a power series in `R⟦X⟧`, `v : R → ℝ` is
  a function and `c` is a real number.

* `PowerSeries.gaussNorm_nonneg`: if `v` is a non-negative function, then the Gauss norm is
  non-negative.

* `PowerSeries.gaussNorm_eq_zero_iff`: if `v` is a non-negative function and `v x = 0 ↔ x = 0` for
  all `x : R` and `c` is positive, then the Gauss norm is zero if and only if the power series is
  zero.

* `PowerSeries.gaussNormC_eq_zero_iff`: if `v` is a non-negative function and `v x = 0 ↔ x = 0`
  for all `x : R` and `c` is positive, then the Gauss norm is zero if and only if the power series
  is zero.

* `PowerSeries.gaussNorm_add_le_max`: if `v` is a non-negative non-archimedean function and the
  set of values `v (coeff t f) * c ^ t` is bounded above (similarily for `g`), then
  the Gauss norm has the non-archimedean property.
-/

public section

namespace PowerSeries

variable {R : Type*} [Semiring R] (v : R → ℝ) (c : ℝ) (f : PowerSeries R)

/-- Given a power series `f` in, a function `v : R → ℝ` and a real number `c`, the Gauss norm is
  defined as the supremum of the set of all values of `v (coeff t f) * c ^ t` for all `t : ℕ`. -/
noncomputable
abbrev gaussNorm : ℝ := MvPowerSeries.gaussNorm v (fun _ => c) f

lemma gaussNorm_eq : gaussNorm v c f = ⨆ i : ℕ, v (f.coeff i) * c ^ i := by
  refine Equiv.iSup_congr Equiv.finsuppUnique ?_
  intro x
  simp only [coeff, Equiv.finsuppUnique_apply, PUnit.default_eq_unit, Finsupp.prod_pow,
    Finset.univ_unique, Finset.prod_singleton, show (Finsupp.single () (x PUnit.unit)) = x by grind]

/-- We say `f` HasGaussNorm if the values `v (coeff t f) * c ^ t` is bounded above, that is
  `gaussNormC f` is finite. -/
abbrev HasGaussNorm := BddAbove (Set.range (fun (t : ℕ) ↦ (v (coeff t f) * c ^ t)))

lemma HasGaussNorm.HasMvGaussNorm (h : HasGaussNorm v c f) :
    MvPowerSeries.HasGaussNorm v (fun _ ↦ c) f := by
  suffices (Set.range (fun (t : ℕ) ↦ (v (coeff t f) * c ^ t))) =
      Set.range fun t ↦ v ((MvPowerSeries.coeff t) f) * t.prod fun _ x2 ↦ c ^ x2 by
    simpa only [MvPowerSeries.HasGaussNorm, ← this]
  refine Set.ext (fun _ ↦ ?_)
  simp only [Set.mem_range, Finsupp.prod_pow, Finset.univ_unique, PUnit.default_eq_unit,
    Finset.prod_singleton]
  constructor
  · intro h
    obtain ⟨y, hy⟩ := h
    use Equiv.finsuppUnique.invFun y
    rw [coeff] at hy
    convert hy
    ext
    simp
  · intro h
    obtain ⟨y, hy⟩ := h
    use Equiv.finsuppUnique.toFun y
    simpa [coeff, show (Finsupp.single () (y PUnit.unit)) = y by grind]

theorem gaussNorm_zero (vZero : v 0 = 0) : gaussNorm v c 0 = 0 :=
  MvPowerSeries.gaussNorm_zero v (fun _ ↦ c) vZero

lemma le_gaussNorm (hbd : HasGaussNorm v c f) (t : ℕ) :
    v (coeff t f) * c ^ t ≤ gaussNorm v c f := by
  rw [gaussNorm_eq]
  apply le_ciSup hbd

lemma gaussNorm_nonneg (vNonneg : ∀ a, v a ≥ 0) : 0 ≤ gaussNorm v c f :=
  MvPowerSeries.gaussNorm_nonneg v (fun _ ↦ c) f vNonneg

lemma gaussNorm_eq_zero_iff (vZero : v 0 = 0) (vNonneg : ∀ a, v a ≥ 0)
    (h_eq_zero : ∀ x : R, v x = 0 → x = 0) (hc : 0 < c) (hbd : HasGaussNorm v c f) :
    gaussNorm v c f = 0 ↔ f = 0 :=
  MvPowerSeries.gaussNorm_eq_zero_iff v (fun _ ↦ c) f vZero vNonneg h_eq_zero
    (by grind) (hbd.HasMvGaussNorm)

lemma gaussNorm_add_le_max (g : PowerSeries R) (hc : 0 ≤ c)
    (vNonneg : ∀ a, v a ≥ 0) (hv : ∀ x y, v (x + y) ≤ max (v x) (v y))
    (hbfd : HasGaussNorm v c f) (hbgd : HasGaussNorm v c g) :
    gaussNorm v c (f + g) ≤ max (gaussNorm v c f) (gaussNorm v c g) :=
  MvPowerSeries.gaussNorm_add_le_max v (fun _ ↦ c) f g (fun _ => by simp [hc]) vNonneg hv
   hbfd.HasMvGaussNorm hbgd.HasMvGaussNorm

end PowerSeries
