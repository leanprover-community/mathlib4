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

/-- `P`: from `B` towards `C`, rotate by `−45°`, scale by `shrink(30°,105°)`, then translate to `B`. -/
noncomputable def P (z : ℂ) : Point :=
  ⟨((C z).z - B.z) * (Complex.exp (deg2rad (-45)*Complex.I))*shrink (deg2rad 30) (deg2rad 105) + B.z⟩

/-- `Q`: from `A` towards `C`, rotate by `+45°`, scale by `shrink(30°,105°)`, then translate to `A`. -/
noncomputable def Q (z : ℂ) : Point :=
  ⟨((C z).z - A.z) * (Complex.exp ( (deg2rad (45)) * Complex.I)) * shrink (deg2rad 30) (deg2rad 105) + A.z⟩

/-- `R`: from `A` towards `B`, rotate by `−15°`, scale by `shrink(15°,150°)`, then translate to `A`. -/
noncomputable def R : Point :=
  ⟨(B.z - A.z) * (Complex.exp (deg2rad (-15)*Complex.I ))*shrink (deg2rad 15) (deg2rad 150) + A.z⟩


/-! ### Trigonometric helper lemmas -/

/-- `cos(π/12) = (√6 + √2)/4`. -/
lemma cos_pi_div_twelve : Real.cos (π / 12) = (sqrt 6 + sqrt 2) / 4 := by
  have h1 : Real.cos (π / 12) = Real.cos (π / 4 - π / 6) := by
    ring_nf
  rw [h1]
  rw [Real.cos_sub]
  have h2 : Real.cos (π / 4) = Real.sqrt 2 / 2 := by
    exact Real.cos_pi_div_four
  have h3 : Real.sin (π / 4) = Real.sqrt 2 / 2 := by
    exact Real.sin_pi_div_four
  have h4 : Real.cos (π / 6) = Real.sqrt 3 / 2 := by
    exact Real.cos_pi_div_six
  have h5 : Real.sin (π / 6) = 1 / 2 := by
    exact Real.sin_pi_div_six
  rw [h2, h3, h4, h5]
  have h6 : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by
    have h7 : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt (2 * 3) := by
      rw [Real.sqrt_mul (by norm_num)]
    rw [h7]
    all_goals norm_num
  have h7 : (Real.sqrt 2 / 2 : ℝ) * (Real.sqrt 3 / 2 : ℝ) = Real.sqrt 6 / 4 := by
    calc
      (Real.sqrt 2 / 2 : ℝ) * (Real.sqrt 3 / 2 : ℝ) = (Real.sqrt 2 * Real.sqrt 3) / 4 := by ring
      _ = (Real.sqrt 6) / 4 := by
        rw [show Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 by linarith [h6]]
  have h8 : (Real.sqrt 2 / 2 : ℝ) * (1 / 2 : ℝ) = Real.sqrt 2 / 4 := by
    ring_nf
  linarith [h7, h8]

/-- `sin(π/12) = (√6 − √2)/4`. -/
lemma sin_pi_div_twelve : Real.sin (π / 12) = (sqrt 6 - sqrt 2) / 4 := by
  have h1 : Real.sin (π / 12) = Real.sin (π / 3 - π / 4) := by
    have h2 : π / 12 = π / 3 - π / 4 := by
      linarith [Real.pi_pos]
    rw [h2]
  rw [h1]
  have h2 : Real.sin (π / 3 - π / 4) = Real.sin (π / 3) * Real.cos (π / 4) - Real.cos (π / 3) * Real.sin (π / 4) := by
    rw [Real.sin_sub]
  rw [h2]
  have h3 : Real.sin (π / 3) = Real.sqrt 3 / 2 := by
    exact sin_pi_div_three
  have h4 : Real.cos (π / 4) = Real.sqrt 2 / 2 := by
    exact cos_pi_div_four
  have h5 : Real.cos (π / 3) = 1 / 2 := by
    exact cos_pi_div_three
  have h6 : Real.sin (π / 4) = Real.sqrt 2 / 2 := by
    exact sin_pi_div_four
  rw [h3, h4, h5, h6]
  have h7 : Real.sqrt 3 * Real.sqrt 2 = Real.sqrt 6 := by
    have h8 : Real.sqrt 3 * Real.sqrt 2 = Real.sqrt (3 * 2) := by
      rw [Real.sqrt_mul (by norm_num)]
    rw [h8]
    all_goals norm_num
  have h8 : (Real.sqrt 3 / 2 * (Real.sqrt 2 / 2) - (1 / 2) * (Real.sqrt 2 / 2)) = (Real.sqrt 6 - Real.sqrt 2) / 4 := by
    have h9 : Real.sqrt 3 * Real.sqrt 2 = Real.sqrt 6 := h7
    have eq1 : Real.sqrt 3 / 2 * (Real.sqrt 2 / 2) = (Real.sqrt 6) / 4 := by
      calc
        Real.sqrt 3 / 2 * (Real.sqrt 2 / 2) = (Real.sqrt 3 * Real.sqrt 2) / 4 := by ring_nf
        _ = (Real.sqrt 6) / 4 := by
          rw [show Real.sqrt 3 * Real.sqrt 2 = Real.sqrt 6 by linarith [h9]]
    have eq2 : (1 / 2 : ℝ) * (Real.sqrt 2 / 2) = (Real.sqrt 2) / 4 := by
      ring_nf
    calc
      (Real.sqrt 3 / 2 * (Real.sqrt 2 / 2) - (1 / 2) * (Real.sqrt 2 / 2))
          = ( (Real.sqrt 6) / 4 ) - ( (Real.sqrt 2) / 4 ) := by
            rw [eq1, eq2]
      _ = (Real.sqrt 6 - Real.sqrt 2) / 4 := by
        ring_nf
  linarith [h8]

/-- `sin(7π/12) = (√6 + √2)/4`. -/
lemma sin_seven_pi_div_twelve : Real.sin (7 * π / 12) = (sqrt 6 + sqrt 2) / 4 := by
  have h1 : 7 * π / 12 = π / 3 + π / 4 := by
    linarith [Real.pi_pos]
  rw [h1]
  have h2 : Real.sin (π / 3 + π / 4) = Real.sin (π / 3) * Real.cos (π / 4) + Real.cos (π / 3) * Real.sin (π / 4) := by
    rw [Real.sin_add]
  rw [h2]
  have h3 : Real.sin (π / 3) = Real.sqrt 3 / 2 := by
    exact sin_pi_div_three
  have h4 : Real.cos (π / 4) = Real.sqrt 2 / 2 := by
    exact cos_pi_div_four
  have h5 : Real.cos (π / 3) = 1 / 2 := by
    exact cos_pi_div_three
  have h6 : Real.sin (π / 4) = Real.sqrt 2 / 2 := by
    exact sin_pi_div_four
  rw [h3, h4, h5, h6]
  have h7 : Real.sqrt 3 * Real.sqrt 2 = Real.sqrt 6 := by
    have h8 : Real.sqrt 3 * Real.sqrt 2 = Real.sqrt (3 * 2) := by
      rw [Real.sqrt_mul (by norm_num)]
    rw [h8]
    all_goals norm_num
  nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num : (2 : ℝ) > 0),
  Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)),
  Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)),
  Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num : (0 : ℝ) ≤ (6 : ℝ)), h7]

/-- `cexp( (π/2) I ) = I`. -/
lemma exp_pi_div_two_I : cexp (π / 2 * I) = I := by
  have : cexp ((π / 2 : ℝ) * I) = (Real.cos (π / 2) : ℂ) + (Real.sin (π / 2) : ℂ) * I := by
    simp[Complex.exp_mul_I (π / 2)]
  simp

/-- Pull an `I` into the exponential: `I * e^{-iπ/4} = e^{+iπ/4}`. -/
lemma I_mul_exp_neg_quarter_pi : I * exp (Real.pi * I * (-1 / 4)) = exp (Real.pi * I * (1 / 4)) := by
  have h1 : Real.pi * I * (-1 / 4 : ℂ) = (- (Real.pi / 4) : ℂ) * I := by
    ring_nf
  have h2 : Real.pi * I * (1 / 4 : ℂ) = (Real.pi / 4 : ℂ) * I := by
    ring_nf
  rw [h1, h2]
  have h3 : exp ((- (Real.pi / 4) : ℂ) * I) = (Real.sqrt 2 / 2 : ℂ) - I * (Real.sqrt 2 / 2 : ℂ) := by
    have h4 : (- (Real.pi / 4) : ℂ) * I = (- (Real.pi / 4 : ℝ) ) * I := by simp
    rw [h4]
    simp [Complex.ext_iff, Complex.exp_re, Complex.exp_im,  Complex.mul_re, Complex.mul_im,
    Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four]
  have h4 : exp ((Real.pi / 4 : ℂ) * I) = (Real.sqrt 2 / 2 : ℂ) + I * (Real.sqrt 2 / 2 : ℂ) := by
    have h5 : (Real.pi / 4 : ℂ) * I = (Real.pi / 4 : ℝ) * I := by simp
    rw [h5]
    simp [Complex.ext_iff, Complex.exp_re, Complex.exp_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Real.cos_pi_div_four, Real.sin_pi_div_four]
  rw [h3, h4]
  ring_nf
  simp [pow_two, Complex.ext_iff, Complex.mul_re, Complex.mul_im]
  ring_nf

/-- A convenient rewrite form of the previous lemma. -/
lemma mul_I_into_exp_neg_quarter_pi (x : ℂ) :
  x * I * cexp (π * I * (-1 / 4)) = x * cexp (π * I * (1 / 4)) := by
  rw[mul_assoc]
  rw [I_mul_exp_neg_quarter_pi]

lemma sin_five_pi_div_six : Real.sin (5 * π / 6) = 1 / 2 := by
  have h1 : 5 * π / 6 = π - (π / 6) := by
    linarith [Real.pi_pos]
  rw [h1]
  rw [Real.sin_pi_sub]
  have h2 : Real.sin (π / 6) = 1 / 2 := by
    exact sin_pi_div_six
  rw [h2]

lemma complex_sin_five_pi_div_six : Complex.sin (↑π * 5 / 6) = (1 / 2 : ℂ) := by
  have h_arg_eq : (↑π * 5 / 6 : ℂ) = ↑(π * 5 / 6 : ℝ) := by
    norm_cast
  rw [h_arg_eq]
  rw [← Complex.ofReal_sin]
  have h_mul_comm : π * 5 / 6 = 5 * π / 6 := by
    ring
  rw [congr_arg Real.sin h_mul_comm]
  rw [sin_five_pi_div_six]
  simp

lemma complex_sin_pi_div_six : Complex.sin (π/6) = 1/2 := by
  have h1 : Complex.sin (π / 6 : ℂ) = (Complex.exp (-( (π / 6 : ℂ) * Complex.I )) - Complex.exp ( (π / 6 : ℂ) * Complex.I )) * Complex.I / 2 := by
    simp [Complex.sin]
  rw [h1]
  have h6 : Complex.exp ( (π / 6 : ℂ) * Complex.I ) = (Real.cos (π / 6 : ℝ) + Complex.I * Real.sin (π / 6 : ℝ)) := by
    simp [Complex.ext_iff, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.exp_re, Complex.exp_im]
  have h7 : Complex.exp (-( (π / 6 : ℂ) * Complex.I ) ) = (Real.cos (π / 6 : ℝ) - Complex.I * Real.sin (π / 6 : ℝ)) := by
    simp [Complex.ext_iff,  Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.exp_re, Complex.exp_im]
  rw [h6, h7]
  have h8 : Real.sin (π / 6 : ℝ) = 1 / 2 := Real.sin_pi_div_six
  have h9 : Real.cos (π / 6 : ℝ) = Real.sqrt 3 / 2 := Real.cos_pi_div_six
  simp [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, h8, h9]


/-- `cos(−π/12) = cos(π/12) = (√6 + √2)/4`. -/
lemma cos_neg_pi_div_twelve : Real.cos (-π / 12) = (sqrt 6 + sqrt 2) / 4 := by
  have h1 : Real.cos (-π / 12) = Real.cos (π / 12) := by
    have h2 : -π / 12 = - (π / 12) := by ring
    rw [h2]
    rw [Real.cos_neg]
  rw [h1]
  have h3 : π / 12 = (π / 3) - (π / 4) := by
    linarith [Real.pi_pos]
  rw [h3]
  rw [Real.cos_sub]
  have h4 : Real.cos (π / 3) = 1 / 2 := by
    exact cos_pi_div_three
  have h5 : Real.sin (π / 3) = Real.sqrt 3 / 2 := by
    have h6 : Real.sin (π / 3) = Real.sqrt 3 / 2 := by
      exact sin_pi_div_three
    linarith
  have h7 : Real.cos (π / 4) = Real.sqrt 2 / 2 := by
    have h8 : Real.cos (π / 4) = Real.sqrt 2 / 2 := by
      exact cos_pi_div_four
    linarith
  have h9 : Real.sin (π / 4) = Real.sqrt 2 / 2 := by
    have h10 : Real.sin (π / 4) = Real.sqrt 2 / 2 := by
      exact sin_pi_div_four
    linarith
  rw [h4, h5, h7, h9]
  have h13 : Real.sqrt 3 * Real.sqrt 2 = Real.sqrt 6 := by
    have h14 : Real.sqrt 3 * Real.sqrt 2 = Real.sqrt (3 * 2) := by
      rw [Real.sqrt_mul (by norm_num)]
    rw [h14]
    all_goals norm_num
  field_simp [h13]
  all_goals nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num),
  Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num),
  mul_nonneg (Real.sqrt_nonneg 6) (Real.sqrt_nonneg 2), mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 2)]


/-- Algebraic identity used to rationalize and collect coefficients:
`2√6 + 2√2 = 8 / (√6 − √2)` (as complex numbers). -/
lemma sqrt_combo_rationalize :
    ↑√6 * 2 + ↑√2 * 2 = ↑(8 / (√ 6 - √ 2)) := by
  have h1 : Real.sqrt 6 > 0 := by positivity
  have h2 : Real.sqrt 2 > 0 := by positivity
  have h3 : Real.sqrt 6 - Real.sqrt 2 ≠ 0 := by
    nlinarith [Real.sqrt_pos.mpr (show (6 : ℝ) > 0 by norm_num), Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num),
                Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num),
                Real.sqrt_nonneg 6, Real.sqrt_nonneg 2,
                sq_nonneg (Real.sqrt 6 - Real.sqrt 2), sq_nonneg (Real.sqrt 6 + Real.sqrt 2),
                mul_nonneg (Real.sqrt_nonneg 6) (Real.sqrt_nonneg 2)
              ]
  have h4 : (8 / (Real.sqrt 6 - Real.sqrt 2) : ℝ) = 2 * Real.sqrt 6 + 2 * Real.sqrt 2 := by
    field_simp [h3]
    ; nlinarith [Real.sqrt_pos.mpr (show (6 : ℝ) > 0 by norm_num), Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num),
                Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num),
                Real.sqrt_nonneg 6, Real.sqrt_nonneg 2,
                sq_nonneg (Real.sqrt 6 - Real.sqrt 2), sq_nonneg (Real.sqrt 6 + Real.sqrt 2),
                mul_nonneg (Real.sqrt_nonneg 6) (Real.sqrt_nonneg 2),
                mul_pos (show 0 < Real.sqrt 6 by positivity) (show 0 < Real.sqrt 2 by positivity)
              ]
  rw [h4]
  all_goals ring_nf

/-! ### Core geometric step -/

/-- `(Q z).z − R.z = ((P z).z − R.z) · e^{iπ/2}`.
Interpretation: the vector `QR` is a 90° CCW rotation of `PR`. -/
lemma PQR_rot90(z : ℂ) :
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
