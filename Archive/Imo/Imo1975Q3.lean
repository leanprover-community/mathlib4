/-
Copyright (c) 2025 YiJian Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YiJian Li
-/
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine

/-!
# A right isosceles configuration in the complex plane


We formalize a triangle configuration in the complex plane. From a base segment
`AB` (with `A = 0`, `B = 1`) and an arbitrary point `C z`, we construct auxiliary
points `R, P, Q` via rotations and scalings. We prove:
* `∠QRP = π/2` (right angle at `R`),
* `dist Q R = dist R P` (isosceles at `R`).


The key step is `Q z − R = e^{iπ/2} · (P z − R)`.
-/

noncomputable section

open Real Complex
open scoped BigOperators EuclideanGeometry

namespace IMO
namespace TriangleConfig

/-- Treat complex numbers as points in the plane. -/
abbrev Point := ℂ

/-- Degrees to radians. -/
@[simp] def deg2rad (α : ℝ) : ℝ := α * π / 180

/-- `shrink θ₀ θ₁ := sin θ₀ / sin θ₁`. -/
@[simp] def shrink (θ₀ θ₁ : ℝ) : ℝ := Real.sin θ₀ / Real.sin θ₁

noncomputable section
variable (z : ℂ)

/-- Base points. -/
@[simp] def A : Point := 0
@[simp] def B : Point := 1
@[simp] def C : Point := z

/-- `P`: from `B` towards `C`,
rotate by `−45°`, scale by `shrink(30°,105°)`, then translate to `B`. -/
noncomputable def P : Point :=
  (z - B) * Complex.exp (deg2rad (-45) * Complex.I) * shrink (deg2rad 30) (deg2rad 105) + B

/-- `Q`: from `A` towards `C`,
rotate by `+45°`, scale by `shrink(30°,105°)`, then translate to `A`. -/
noncomputable def Q : Point :=
  (z - A) * Complex.exp (deg2rad 45 * Complex.I) * shrink (deg2rad 30) (deg2rad 105) + A

/-- `R`: from `A` towards `B`,
rotate by `−15°`, scale by `shrink(15°,150°)`, then translate to `A`. -/
noncomputable def R : Point :=
  (B - A) * Complex.exp (deg2rad (-15) * Complex.I) * shrink (deg2rad 15) (deg2rad 150) + A


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

/-- `(Q z) − R = ((P z) − R) · e^{iπ/2}`.
Interpretation: the vector `QR` is a 90° CCW rotation of `PR`. -/
lemma PQR_rot90 (z : ℂ) :
    Q z - R = (P z - R) * Complex.exp (π / 2 * I) := by
  -- expand definitions and normalize
  simp [Q, P, R, A, B]
  simp [mul_comm]
  ring_nf
  -- push `I` into the exponential
  rw [mul_I_into_exp_neg_quarter_pi, mul_comm]
  -- numeric/trig cleanup
  field_simp
  simp_rw [
    show -(π * I) / 12 = (-π / 12) * I by field_simp,
    show -(π * I) / 4 = (-π / 4) * I by field_simp,
    exp_mul_I
  ]
  norm_cast
  simp [mul_comm π 7]
  -- Cleanup
  ring_nf
  norm_num
  field_simp
  ring_nf
  field_simp
  norm_cast
  field_simp
  rw [← sub_eq_zero]
  ring_nf
  norm_cast
  field_simp [sqrt_combo_rationalize]
  ring_nf
  simp [pow_two, Complex.ext_iff]
  ring_nf

/-- Distances from `R` to `Q` and `P` are equal: multiplying by a unit complex preserves norm. -/
lemma dist_eq_of_rot90 (z : ℂ) :
    dist (Q z) R = dist R (P z) := by
  have hnorm :
      ‖Q z - R‖ = ‖(P z - R) * cexp (π / 2 * I)‖ := by
    simpa using congrArg norm (PQR_rot90 z)
  simp [Complex.dist_eq, hnorm, norm_sub_rev]

/-- Angle `∠QRP = π/2` from the rotation relation. -/
lemma angle_pi_div_two_of_rot90 (z : ℂ) :
    ∠ (Q z) R (P z) = π / 2 := by
  set u : ℂ := (Q z) - R
  set v : ℂ := (P z) - R
  have exp_I_half_pi : Complex.exp (I * (π / 2)) = I := by
    simpa [mul_comm] using Complex.exp_pi_div_two_mul_I
  have hI : u = I * v := by
    simpa [u, v, exp_I_half_pi, mul_comm] using PQR_rot90 z
  -- show `Re(u * conj v) = 0`
  have horth : re (u * star v) = 0 := by
    simp [hI]
    ring_nf
  -- Bridge: angle is π/2 iff the (real) inner product is zero.
  have hiff : (∠ (Q z) R (P z) = π / 2) ↔ (re (u * star v) = 0) := by
        have h₁ : (∠ (Q z) R (P z) = π / 2) ↔ inner ℝ u v = 0 := by
          simpa [u, v, sub_eq_add_neg] using
            (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two
              (Q z - R) (P z - R)).symm
        have h₂ : inner ℝ u v = re (u * star v) := by
          simp [u, v]
          ring_nf
        simpa [h₂] using h₁
  exact hiff.mpr horth

/-- Main theorem: for any `z : ℂ` with `(P z) ≠ R`, we have `∠QRP = π/2` and
`dist Q R = dist R P`. -/
theorem geometry_main_theorem (z : ℂ) :
    (∠ (Q z) R (P z) = π / 2) ∧ (dist (Q z) R = dist R (P z)) :=
    ⟨angle_pi_div_two_of_rot90 z, dist_eq_of_rot90 z⟩

end -- section

end TriangleConfig
end IMO

end
