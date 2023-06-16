/-
Copyright (c) 2021 James Arthur, Benjamin Davidson, Andrew Souther. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Arthur, Benjamin Davidson, Andrew Souther

! This file was ported from Lean 3 source module «100-theorems-list».«9_area_of_a_circle»
! leanprover-community/mathlib commit 328375597f2c0dd00522d9c2e5a33b6a6128feeb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Freek № 9: The Area of a Circle

In this file we show that the area of a disc with nonnegative radius `r` is `π * r^2`. The main
tools our proof uses are `volume_region_between_eq_integral`, which allows us to represent the area
of the disc as an integral, and `interval_integral.integral_eq_sub_of_has_deriv_at'_of_le`, the
second fundamental theorem of calculus.

We begin by defining `disc` in `ℝ × ℝ`, then show that `disc` can be represented as the
`region_between` two functions.

Though not necessary for the main proof, we nonetheless choose to include a proof of the
measurability of the disc in order to convince the reader that the set whose volume we will be
calculating is indeed measurable and our result is therefore meaningful.

In the main proof, `area_disc`, we use `volume_region_between_eq_integral` followed by
`interval_integral.integral_of_le` to reduce our goal to a single `interval_integral`:
  `∫ (x : ℝ) in -r..r, 2 * sqrt (r ^ 2 - x ^ 2) = π * r ^ 2`.
After disposing of the trivial case `r = 0`, we show that `λ x, 2 * sqrt (r ^ 2 - x ^ 2)` is equal
to the derivative of `λ x, r ^ 2 * arcsin (x / r) + x * sqrt (r ^ 2 - x ^ 2)` everywhere on
`Ioo (-r) r` and that those two functions are continuous, then apply the second fundamental theorem
of calculus with those facts. Some simple algebra then completes the proof.

Note that we choose to define `disc` as a set of points in `ℝ × ℝ`. This is admittedly not ideal; it
would be more natural to define `disc` as a `metric.ball` in `euclidean_space ℝ (fin 2)` (as well as
to provide a more general proof in higher dimensions). However, our proof indirectly relies on a
number of theorems (particularly `measure_theory.measure.prod_apply`) which do not yet exist for
Euclidean space, thus forcing us to use this less-preferable definition. As `measure_theory.pi`
continues to develop, it should eventually become possible to redefine `disc` and extend our proof
to the n-ball.
-/


open Set Real MeasureTheory intervalIntegral

open scoped Real NNReal

namespace Theorems100

/-- A disc of radius `r` is defined as the collection of points `(p.1, p.2)` in `ℝ × ℝ` such that
  `p.1 ^ 2 + p.2 ^ 2 < r ^ 2`.
  Note that this definition is not equivalent to `metric.ball (0 : ℝ × ℝ) r`. This was done
  intentionally because `dist` in `ℝ × ℝ` is defined as the uniform norm, making the `metric.ball`
  in `ℝ × ℝ` a square, not a disc.
  See the module docstring for an explanation of why we don't define the disc in Euclidean space. -/
def disc (r : ℝ) :=
  {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < r ^ 2}
#align theorems_100.disc Theorems100.disc

variable (r : ℝ≥0)

/-- A disc of radius `r` can be represented as the region between the two curves
  `λ x, - sqrt (r ^ 2 - x ^ 2)` and `λ x, sqrt (r ^ 2 - x ^ 2)`. -/
theorem disc_eq_regionBetween :
    disc r =
      regionBetween (fun x => -sqrt (r ^ 2 - x ^ 2)) (fun x => sqrt (r ^ 2 - x ^ 2)) (Ioc (-r) r) :=
  by
  ext p
  simp only [disc, regionBetween, mem_set_of_eq, mem_Ioo, mem_Ioc, Pi.neg_apply]
  constructor <;> intro h
  · cases abs_lt_of_sq_lt_sq' (lt_of_add_lt_of_nonneg_left h (sq_nonneg p.2)) r.2
    rw [add_comm, ← lt_sub_iff_add_lt] at h 
    exact ⟨⟨left, right.le⟩, sq_lt.mp h⟩
  · rw [add_comm, ← lt_sub_iff_add_lt]
    exact sq_lt.mpr h.2
#align theorems_100.disc_eq_region_between Theorems100.disc_eq_regionBetween

/-- The disc is a `measurable_set`. -/
theorem measurableSet_disc : MeasurableSet (disc r) := by
  apply measurableSet_lt <;> apply Continuous.measurable <;> continuity
#align theorems_100.measurable_set_disc Theorems100.measurableSet_disc

/-- **Area of a Circle**: The area of a disc with radius `r` is `π * r ^ 2`. -/
theorem area_disc : volume (disc r) = NNReal.pi * r ^ 2 := by
  let f x := sqrt (r ^ 2 - x ^ 2)
  let F x := (r : ℝ) ^ 2 * arcsin (r⁻¹ * x) + x * sqrt (r ^ 2 - x ^ 2)
  have hf : Continuous f := by continuity
  suffices ∫ x in -r..r, 2 * f x = NNReal.pi * r ^ 2 by
    have h : integrable_on f (Ioc (-r) r) := hf.integrable_on_Icc.mono_set Ioc_subset_Icc_self
    calc
      volume (disc r) = volume (regionBetween (fun x => -f x) f (Ioc (-r) r)) := by
        rw [disc_eq_region_between]
      _ = ENNReal.ofReal (∫ x in Ioc (-r : ℝ) r, (f - Neg.neg ∘ f) x) :=
        (volume_regionBetween_eq_integral h.neg h measurableSet_Ioc fun x hx =>
          neg_le_self (sqrt_nonneg _))
      _ = ENNReal.ofReal (∫ x in (-r : ℝ)..r, 2 * f x) := by simp [two_mul, integral_of_le]
      _ = NNReal.pi * r ^ 2 := by rw_mod_cast [this, ← ENNReal.coe_nnreal_eq]
  obtain ⟨hle, heq | hlt⟩ := NNReal.coe_nonneg r, hle.eq_or_lt; · simp [← HEq]
  have hderiv : ∀ x ∈ Ioo (-r : ℝ) r, HasDerivAt F (2 * f x) x := by
    rintro x ⟨hx1, hx2⟩
    convert
      ((hasDerivAt_const x ((r : ℝ) ^ 2)).mul
            ((has_deriv_at_arcsin _ _).comp x
              ((hasDerivAt_const x (r : ℝ)⁻¹).mul (hasDerivAt_id' x)))).add
        ((hasDerivAt_id' x).mul ((((hasDerivAt_id' x).pow 2).const_sub ((r : ℝ) ^ 2)).sqrt _))
    · have h : sqrt (1 - x ^ 2 / r ^ 2) * r = sqrt (r ^ 2 - x ^ 2) := by
        rw [← sqrt_sq hle, ← sqrt_mul, sub_mul, sqrt_sq hle, mul_comm_div,
          div_self (pow_ne_zero 2 hlt.ne'), one_mul, mul_one]
        simpa [sqrt_sq hle, div_le_one (pow_pos hlt 2)] using sq_le_sq' hx1.le hx2.le
      field_simp
      rw [h, mul_left_comm, ← sq, neg_mul_eq_mul_neg, mul_div_mul_left (-x ^ 2) _ two_ne_zero,
        add_left_comm, div_add_div_same, Tactic.Ring.add_neg_eq_sub, div_sqrt, two_mul]
    · suffices -(1 : ℝ) < r⁻¹ * x by exact this.ne'
      calc
        -(1 : ℝ) = r⁻¹ * -r := by simp [hlt.ne']
        _ < r⁻¹ * x := by nlinarith [inv_pos.mpr hlt]
    · suffices (r : ℝ)⁻¹ * x < 1 by exact this.ne
      calc
        (r : ℝ)⁻¹ * x < r⁻¹ * r := by nlinarith [inv_pos.mpr hlt]
        _ = 1 := inv_mul_cancel hlt.ne'
    · nlinarith
  have hcont := (by continuity : Continuous F).ContinuousOn
  calc
    ∫ x in -r..r, 2 * f x = F r - F (-r) :=
      integral_eq_sub_of_has_deriv_at_of_le (neg_le_self r.2) hcont hderiv
        (continuous_const.mul hf).ContinuousOn.IntervalIntegrable
    _ = NNReal.pi * r ^ 2 := by norm_num [F, inv_mul_cancel hlt.ne', ← mul_div_assoc, mul_comm π]
#align theorems_100.area_disc Theorems100.area_disc

end Theorems100

