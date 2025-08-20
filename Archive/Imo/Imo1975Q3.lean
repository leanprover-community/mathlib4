/-
Copyright (c) 2025 YiJian Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YiJian Li
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Data.Complex.Norm
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Complex.Trigonometric
import Mathlib.Analysis.Complex.Arg
import Mathlib.Analysis.Complex.Angle
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Simps.Basic
import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.Geometry.Euclidean.Angle.Unoriented.CrossProduct

/-!
# A right isosceles configuration in the complex plane


We formalize a triangle configuration in the complex plane. From a base segment
`AB` (with `A = 0`, `B = 1`) and an arbitrary point `C z`, we construct auxiliary
points `R, P, Q` via rotations and scalings. We prove:
* `∠QRP = π/2` (right angle at `R`),
* `dist Q R = dist R P` (isosceles at `R`).


The key step is `(Q z).z − R.z = e^{iπ/2} · ((P z).z − R.z)`.
-/

noncomputable section

open Real Complex
open scoped BigOperators

namespace IMO
namespace TriangleConfig

/-- Treat complex numbers as points in the plane. -/
structure Point where
  z : ℂ
  deriving Inhabited

/-- Induce the metric on `Point` from the metric on `ℂ`. -/
@[simp] instance : PseudoMetricSpace Point :=
  PseudoMetricSpace.induced (fun p => p.z) inferInstance

/-- Degrees to radians. -/
@[simp] def deg2rad (α : ℝ) : ℝ := α * π / 180

/-- `shrink θ₀ θ₁ := sin θ₀ / sin θ₁`. -/
@[simp] def shrink (θ₀ θ₁ : ℝ) : ℝ := Real.sin θ₀ / Real.sin θ₁

example (p q : Point) : dist p q = ‖p.z - q.z‖ := by
  simpa using Complex.dist_eq p.z q.z

/-- Base points. -/
def A : Point := ⟨0⟩
def B : Point := ⟨1⟩
def C (z : ℂ) : Point := ⟨z⟩

/-- `P`: from `B` towards `C`,
rotate by `−45°`, scale by `shrink(30°,105°)`, then translate to `B`. -/
noncomputable def P (z : ℂ) : Point :=
  ⟨((C z).z - B.z) *
    (Complex.exp (deg2rad (-45)*Complex.I))*shrink (deg2rad 30) (deg2rad 105) + B.z⟩

/-- `Q`: from `A` towards `C`,
rotate by `+45°`, scale by `shrink(30°,105°)`, then translate to `A`. -/
noncomputable def Q (z : ℂ) : Point :=
  ⟨((C z).z - A.z) *
    (Complex.exp ( (deg2rad (45)) * Complex.I)) * shrink (deg2rad 30) (deg2rad 105) + A.z⟩

/-- `R`: from `A` towards `B`,
rotate by `−15°`, scale by `shrink(15°,150°)`, then translate to `A`. -/
noncomputable def R : Point :=
  ⟨(B.z - A.z) *
    (Complex.exp (deg2rad (-15)*Complex.I ))*shrink (deg2rad 15) (deg2rad 150) + A.z⟩


/-! ### Trigonometric helper lemmas -/

@[grind]
lemma sqrt_two_times_sqrt_three : √2 * √3 = √6 := by
  rw [← sqrt_mul (Nat.ofNat_nonneg _)]
  ring_nf

/-- `cos(π/12) = (√6 + √2)/4`. -/
@[simp]
lemma cos_pi_div_twelve : Real.cos (π / 12) = (√6 + √2) / 4 := by
  have pi_div_twelve : π / 12 = π / 4 - π / 6 := by
    ring_nf
  simp [pi_div_twelve, Real.cos_sub]
  grind

/-- `sin(π/12) = (√6 − √2)/4`. -/
@[simp]
lemma sin_pi_div_twelve : Real.sin (π / 12) = (√6 - √2) / 4 := by
  have pi_div_twelve : π / 12 = π / 3 - π / 4 := by
    ring_nf
  simp [pi_div_twelve, Real.sin_sub]
  grind

/-- `sin(7π/12) = (√6 + √2)/4`. -/
@[simp]
lemma sin_seven_pi_div_twelve : Real.sin (7 * π / 12) = (√6 + √2) / 4 := by
  have seven_pi_div_twelve : 7 * π / 12 = π / 3 + π / 4 := by
    ring_nf
  simp [seven_pi_div_twelve, Real.sin_add]
  grind

@[simp]
lemma complex_sin_five_pi_div_six : sin (π * 5 / 6 : ℂ) = (1 / 2 : ℂ) := by
  norm_cast
  rw [← Real.sin_pi_sub]
  ring_nf
  field_simp

@[simp]
lemma complex_sin_pi_div_six : sin (π / 6 : ℂ) = 1 / 2 := by
  norm_cast
  simp

lemma mul_I_into_exp_neg_quarter_pi (x : ℂ) :
    x * I * cexp (π * I * (-1 / 4)) = x * cexp (π * I * (1 / 4)) := by
  rw [mul_assoc, mul_eq_mul_left_iff]
  field_simp [Complex.ext_iff, exp_re, exp_im]
  simp [neg_div, Real.sin_neg]

/-- Algebraic identity used to rationalize and collect coefficients:
`2√6 + 2√2 = 8 / (√6 − √2)` (as complex numbers). -/
lemma sqrt_combo_rationalize :
    √6 * 2 + √2 * 2 = 8 / (√6 - √2) := by
  have : √6 - √2 ≠ 0 := by
    simp [sub_eq_zero]
  field_simp
  ring_nf
  norm_num

/-! ### Core geometric step -/

/-- `(Q z).z − R.z = ((P z).z − R.z) · e^{iπ/2}`.
Interpretation: the vector `QR` is a 90° CCW rotation of `PR`. -/
lemma PQR_rot90 (z : ℂ) :
    (Q z).z - R.z = ((P z).z - R.z) * (Complex.exp (Real.pi / 2 * I)) := by
  -- expand definitions and normalize
  simp [Q, P, R, deg2rad, shrink, A, B, C]
  simp [mul_comm]
  ring_nf
  -- push `I` into the exponential
  rw[mul_I_into_exp_neg_quarter_pi,mul_comm]
  -- numeric/trig cleanup
  norm_num
  field_simp
  simp[complex_sin_five_pi_div_six,complex_sin_pi_div_six]
  simp_rw [
    show -(↑π * I) / 12 = ↑(-π / 12) * I by (field_simp;),
    show -(↑π * I) / 4 = ↑(-π / 4) * I by (field_simp;),
    Complex.exp_mul_I
  ]
  norm_cast
  have h2 : Real.sin (-π / 12) = Real.sin (-(π / 12)) := by ring_nf
  rw [h2,Real.sin_neg,mul_comm π 7]
  simp [sin_seven_pi_div_twelve, sin_pi_div_twelve,cos_neg_pi_div_twelve]
  norm_cast
  -- Algebraic cleanup: expand definitions and normalize trigonometric constants.
  -- Final coefficient collection after rationalizing denominators.
  ring_nf
  norm_num [I_sq]
  rw [← sub_eq_zero]
  field_simp
  ring_nf
  field_simp
  norm_cast
  norm_num[sin_pi_div_four,cos_pi_div_four]
  field_simp
  ring_nf
  field_simp
  norm_cast
  rw[sqrt_combo_rationalize]
  field_simp
  ring_nf
  simp[pow_two]
  -- final rationalization
  have h1 : (√2 : ℂ) * (√2 : ℂ) = (2 : ℂ) := by
    have h2 : (√2 : ℂ) ^ 2 = (2 : ℂ) := by
      simp [pow_two, Complex.ext_iff]
    calc
      (√2 : ℂ) * (√2 : ℂ) = (√2 : ℂ) ^ 2 := by ring
      _ = (2 : ℂ) := h2
  rw [h1]
  ring_nf

/-- Distances from `R` to `Q` and `P` are equal: multiplying by a unit complex preserves norm. -/
lemma dist_eq_of_rot90 (z : ℂ) :
    dist (Q z) R = dist R (P z) := by
  change dist (Q z).z R.z = dist R.z (P z).z
  have hnorm :
      ‖(Q z).z - R.z‖ = ‖((P z).z - R.z) * cexp (π / 2 * I)‖ := by
    simpa using congrArg (fun w : ℂ => ‖w‖) (PQR_rot90 z)
  have hunit : ‖cexp (π / 2 * I)‖ = 1 := by
    have habs :
        norm (cexp (π / 2 * I))
          = Real.exp (Complex.re ((π / 2 : ℝ) * I)) := by
      simp
    have hre : Complex.re ((π / 2 : ℝ) * I) = 0 := by simp
    simp
  calc
    ‖(Q z).z - R.z‖
        = ‖((P z).z - R.z) * Complex.exp (Real.pi / 2 * Complex.I)‖ := hnorm
    _ = ‖(P z).z - R.z‖ * ‖Complex.exp (Real.pi / 2 * Complex.I)‖ := by
      simp
    _ = ‖(P z).z - R.z‖ * 1 := by simp
    _ = ‖(P z).z - R.z‖ := by simp
  simp[Complex.dist_eq,norm_sub_rev]

/-- Angle `∠QRP = π/2` from the rotation relation. -/
lemma angle_pi_div_two_of_rot90
  (z : ℂ) (hPR : (P z).z ≠ R.z) :
  EuclideanGeometry.angle (Q z).z R.z (P z).z = Real.pi / 2 := by
  set u : ℂ := (Q z).z - R.z
  set v : ℂ := (P z).z - R.z
  have exp_I_half_pi : Complex.exp (I * (Real.pi / 2)) = I := by
    simpa [mul_comm] using exp_pi_div_two_I
  have hI : u = I * v := by
    simpa [u, v, exp_I_half_pi, mul_comm] using PQR_rot90 z
  have hv_ne : v ≠ 0 := sub_ne_zero.mpr hPR
  have hu_ne : u ≠ 0 := by
    have : I * v ≠ 0 := mul_ne_zero (by simp) hv_ne
    simpa [hI]
  -- show `Re(u * conj v) = 0`
  have horth : Complex.re (u * star v) = 0 := by
    calc
      Complex.re (u * star v)
          = Complex.re (I * v * star v) := by
              simp [hI]
      _ = Complex.re (I * (v * star v)) := by ring_nf
      _ = 0 := by
        have hmul : v * star v = (Complex.normSq v : ℝ) := by
          simpa using Complex.mul_conj v
        simp
        ring_nf
  -- Bridge: angle is π/2 iff the (real) inner product is zero.
  have hiff :
      (EuclideanGeometry.angle (Q z).z R.z (P z).z = Real.pi / 2) ↔
      (Complex.re (u * star v) = 0) := by
        have h₁ :
        (EuclideanGeometry.angle (Q z).z R.z (P z).z = Real.pi / 2)
        ↔ inner ℝ u v = 0 := by
          simpa [u, v, sub_eq_add_neg] using
            (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two
              ((Q z).z - R.z) ((P z).z - R.z)).symm
        have h₂ : inner ℝ u v = Complex.re (u * star v) := by
          simp[Complex.inner,u,v]
          ring_nf
        simpa [h₂] using h₁
  exact hiff.mpr horth

/-- Main theorem: for any `z : ℂ` with `(P z).z ≠ R.z`, we have `∠QRP = π/2` and
`dist Q R = dist R P`. -/
theorem geometry_main_theorem
    (z : ℂ)
    (hPR : (P z).z ≠ R.z) :
    (EuclideanGeometry.angle (Q z).z R.z (P z).z = π / 2) ∧ (dist (Q z) R = dist R (P z)) := by
  refine ⟨?h90, ?heq⟩
  · exact angle_pi_div_two_of_rot90 z hPR
  · exact dist_eq_of_rot90 z

end TriangleConfig
end IMO

end
