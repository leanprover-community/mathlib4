/-
Copyright (c) 2021 James Arthur, Benjamin Davidson, Andrew Souther. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Arthur, Benjamin Davidson, Andrew Souther
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

#align_import wiedijk_100_theorems.area_of_a_circle from "leanprover-community/mathlib"@"5563b1b49e86e135e8c7b556da5ad2f5ff881cad"

/-!
# Freek № 9: The Area of a Circle

In this file we show that the area of a disc with nonnegative radius `r` is `π * r^2`. The main
tools our proof uses are `volume_regionBetween_eq_integral`, which allows us to represent the area
of the disc as an integral, and `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`, the
second fundamental theorem of calculus.

We begin by defining `disc` in `ℝ × ℝ`, then show that `disc` can be represented as the
`regionBetween` two functions.

Though not necessary for the main proof, we nonetheless choose to include a proof of the
measurability of the disc in order to convince the reader that the set whose volume we will be
calculating is indeed measurable and our result is therefore meaningful.

In the main proof, `area_disc`, we use `volume_regionBetween_eq_integral` followed by
`intervalIntegral.integral_of_le` to reduce our goal to a single `intervalIntegral`:
  `∫ (x : ℝ) in -r..r, 2 * sqrt (r ^ 2 - x ^ 2) = π * r ^ 2`.
After disposing of the trivial case `r = 0`, we show that `fun x => 2 * sqrt (r ^ 2 - x ^ 2)` is
equal to the derivative of `fun x => r ^ 2 * arcsin (x / r) + x * sqrt (r ^ 2 - x ^ 2)` everywhere
on `Ioo (-r) r` and that those two functions are continuous, then apply the second fundamental
theorem of calculus with those facts. Some simple algebra then completes the proof.

Note that we choose to define `disc` as a set of points in `ℝ × ℝ`. This is admittedly not ideal; it
would be more natural to define `disc` as a `Metric.ball` in `EuclideanSpace ℝ (Fin 2)` (as well as
to provide a more general proof in higher dimensions). However, our proof indirectly relies on a
number of theorems (particularly `MeasureTheory.Measure.prod_apply`) which do not yet exist for
Euclidean space, thus forcing us to use this less-preferable definition. As `MeasureTheory.pi`
continues to develop, it should eventually become possible to redefine `disc` and extend our proof
to the n-ball.
-/


open Set Real MeasureTheory intervalIntegral

open scoped Real NNReal

namespace Theorems100

/-- A disc of radius `r` is defined as the collection of points `(p.1, p.2)` in `ℝ × ℝ` such that
  `p.1 ^ 2 + p.2 ^ 2 < r ^ 2`.
  Note that this definition is not equivalent to `Metric.ball (0 : ℝ × ℝ) r`. This was done
  intentionally because `dist` in `ℝ × ℝ` is defined as the uniform norm, making the `Metric.ball`
  in `ℝ × ℝ` a square, not a disc.
  See the module docstring for an explanation of why we don't define the disc in Euclidean space. -/
def disc (r : ℝ) :=
  {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < r ^ 2}
#align theorems_100.disc Theorems100.disc

variable (r : ℝ≥0)

/-- A disc of radius `r` can be represented as the region between the two curves
  `fun x => - sqrt (r ^ 2 - x ^ 2)` and `fun x => sqrt (r ^ 2 - x ^ 2)`. -/
theorem disc_eq_regionBetween :
    disc r =
      regionBetween
        (fun x => -sqrt (r ^ 2 - x ^ 2)) (fun x => sqrt (r ^ 2 - x ^ 2)) (Ioc (-r) r) := by
  ext p
  simp only [disc, regionBetween, mem_setOf_eq, mem_Ioo, mem_Ioc, Pi.neg_apply]
  constructor <;> intro h
  · cases abs_lt_of_sq_lt_sq' (lt_of_add_lt_of_nonneg_left h (sq_nonneg p.2)) r.2 with
    | intro left right =>
      rw [add_comm, ← lt_sub_iff_add_lt] at h
      exact ⟨⟨left, right.le⟩, sq_lt.mp h⟩
  · rw [add_comm, ← lt_sub_iff_add_lt]
    exact sq_lt.mpr h.2
#align theorems_100.disc_eq_region_between Theorems100.disc_eq_regionBetween

/-- The disc is a `MeasurableSet`. -/
theorem measurableSet_disc : MeasurableSet (disc r) := by
  apply measurableSet_lt <;> apply Continuous.measurable <;> continuity
#align theorems_100.measurable_set_disc Theorems100.measurableSet_disc

/-- **Area of a Circle**: The area of a disc with radius `r` is `π * r ^ 2`. -/
theorem area_disc : volume (disc r) = NNReal.pi * r ^ 2 := by
  let f x := sqrt (r ^ 2 - x ^ 2)
  let F x := (r : ℝ) ^ 2 * arcsin (r⁻¹ * x) + x * sqrt (r ^ 2 - x ^ 2)
  have hf : Continuous f := by continuity
  suffices ∫ x in -r..r, 2 * f x = NNReal.pi * r ^ 2 by
    have h : IntegrableOn f (Ioc (-r) r) := hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    calc
      volume (disc r) = volume (regionBetween (fun x => -f x) f (Ioc (-r) r)) := by
        rw [disc_eq_regionBetween]
      _ = ENNReal.ofReal (∫ x in Ioc (-r : ℝ) r, (f - Neg.neg ∘ f) x) :=
        (volume_regionBetween_eq_integral h.neg h measurableSet_Ioc fun x _ =>
          neg_le_self (sqrt_nonneg _))
      _ = ENNReal.ofReal (∫ x in (-r : ℝ)..r, 2 * f x) := by
        rw [integral_of_le] <;> simp [two_mul, neg_le_self]
      _ = NNReal.pi * r ^ 2 := by rw_mod_cast [this, ← ENNReal.coe_nnreal_eq]
  have hle := NNReal.coe_nonneg r
  obtain heq | hlt := hle.eq_or_lt; · simp [← heq]
  have hderiv : ∀ x ∈ Ioo (-r : ℝ) r, HasDerivAt F (2 * f x) x := by
    rintro x ⟨hx1, hx2⟩
    convert
      ((hasDerivAt_const x ((r : ℝ) ^ 2)).mul
            ((hasDerivAt_arcsin _ _).comp x
              ((hasDerivAt_const x (r : ℝ)⁻¹).mul (hasDerivAt_id' x)))).add
        ((hasDerivAt_id' x).mul ((((hasDerivAt_id' x).pow 2).const_sub ((r : ℝ) ^ 2)).sqrt _))
      using 1
    · have h₁ : (r:ℝ) ^ 2 - x ^ 2 > 0 := sub_pos_of_lt (sq_lt_sq' hx1 hx2)
      have h : sqrt ((r:ℝ) ^ 2 - x ^ 2) ^ 3 = ((r:ℝ) ^ 2 - x ^ 2) * sqrt ((r: ℝ) ^ 2 - x ^ 2) := by
        rw [pow_three, ← mul_assoc, mul_self_sqrt (by positivity)]
      field_simp
      ring_nf
      rw [h]
      ring
    · suffices -(1 : ℝ) < (r : ℝ)⁻¹ * x by exact this.ne'
      calc
        -(1 : ℝ) = (r : ℝ)⁻¹ * -r := by simp [inv_mul_cancel hlt.ne']
        _ < (r : ℝ)⁻¹ * x := by nlinarith [inv_pos.mpr hlt]
    · suffices (r : ℝ)⁻¹ * x < 1 by exact this.ne
      calc
        (r : ℝ)⁻¹ * x < (r : ℝ)⁻¹ * r := by nlinarith [inv_pos.mpr hlt]
        _ = 1 := inv_mul_cancel hlt.ne'
    · nlinarith
  have hcont : ContinuousOn F (Icc (-r) r) := (by continuity : Continuous F).continuousOn
  calc
    ∫ x in -r..r, 2 * f x = F r - F (-r) :=
      integral_eq_sub_of_hasDerivAt_of_le (neg_le_self r.2) hcont hderiv
        (continuous_const.mul hf).continuousOn.intervalIntegrable
    _ = NNReal.pi * (r : ℝ) ^ 2 := by
      norm_num [F, inv_mul_cancel hlt.ne', ← mul_div_assoc, mul_comm π]
#align theorems_100.area_disc Theorems100.area_disc

end Theorems100
