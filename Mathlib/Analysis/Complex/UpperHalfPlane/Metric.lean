/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Geometry.Euclidean.Inversion.Basic

#align_import analysis.complex.upper_half_plane.metric from "leanprover-community/mathlib"@"caa58cbf5bfb7f81ccbaca4e8b8ac4bc2b39cc1c"

/-!
# Metric on the upper half-plane

In this file we define a `MetricSpace` structure on the `UpperHalfPlane`. We use hyperbolic
(Poincaré) distance given by
`dist z w = 2 * arsinh (dist (z : ℂ) w / (2 * Real.sqrt (z.im * w.im)))` instead of the induced
Euclidean distance because the hyperbolic distance is invariant under holomorphic automorphisms of
the upper half-plane. However, we ensure that the projection to `TopologicalSpace` is
definitionally equal to the induced topological space structure.

We also prove that a metric ball/closed ball/sphere in Poincaré metric is a Euclidean ball/closed
ball/sphere with another center and radius.

-/


noncomputable section

open scoped UpperHalfPlane ComplexConjugate NNReal Topology MatrixGroups

open Set Metric Filter Real

variable {z w : ℍ} {r R : ℝ}

namespace UpperHalfPlane

instance : Dist ℍ :=
  ⟨fun z w => 2 * arsinh (dist (z : ℂ) w / (2 * sqrt (z.im * w.im)))⟩

theorem dist_eq (z w : ℍ) : dist z w = 2 * arsinh (dist (z : ℂ) w / (2 * sqrt (z.im * w.im))) :=
  rfl
#align upper_half_plane.dist_eq UpperHalfPlane.dist_eq

theorem sinh_half_dist (z w : ℍ) :
    sinh (dist z w / 2) = dist (z : ℂ) w / (2 * sqrt (z.im * w.im)) := by
  rw [dist_eq, mul_div_cancel_left (arsinh _) two_ne_zero, sinh_arsinh]
  -- 🎉 no goals
#align upper_half_plane.sinh_half_dist UpperHalfPlane.sinh_half_dist

theorem cosh_half_dist (z w : ℍ) :
    cosh (dist z w / 2) = dist (z : ℂ) (conj (w : ℂ)) / (2 * sqrt (z.im * w.im)) := by
  have H₁ : (2 ^ 2 : ℝ) = 4 := by norm_num1
  -- ⊢ cosh (dist z w / 2) = dist (↑z) (↑(starRingEnd ℂ) ↑w) / (2 * sqrt (im z * im …
  have H₂ : 0 < z.im * w.im := mul_pos z.im_pos w.im_pos
  -- ⊢ cosh (dist z w / 2) = dist (↑z) (↑(starRingEnd ℂ) ↑w) / (2 * sqrt (im z * im …
  have H₃ : 0 < 2 * sqrt (z.im * w.im) := mul_pos two_pos (sqrt_pos.2 H₂)
  -- ⊢ cosh (dist z w / 2) = dist (↑z) (↑(starRingEnd ℂ) ↑w) / (2 * sqrt (im z * im …
  rw [← sq_eq_sq (cosh_pos _).le (div_nonneg dist_nonneg H₃.le), cosh_sq', sinh_half_dist, div_pow,
    div_pow, one_add_div (pow_ne_zero 2 H₃.ne'), mul_pow, sq_sqrt H₂.le, H₁]
  congr 1
  -- ⊢ 4 * (im z * im w) + dist ↑z ↑w ^ 2 = dist (↑z) (↑(starRingEnd ℂ) ↑w) ^ 2
  simp only [Complex.dist_eq, Complex.sq_abs, Complex.normSq_sub, Complex.normSq_conj,
    Complex.conj_conj, Complex.mul_re, Complex.conj_re, Complex.conj_im, coe_im]
  ring
  -- 🎉 no goals
#align upper_half_plane.cosh_half_dist UpperHalfPlane.cosh_half_dist

theorem tanh_half_dist (z w : ℍ) :
    tanh (dist z w / 2) = dist (z : ℂ) w / dist (z : ℂ) (conj ↑w) := by
  rw [tanh_eq_sinh_div_cosh, sinh_half_dist, cosh_half_dist, div_div_div_comm, div_self, div_one]
  -- ⊢ 2 * sqrt (im z * im w) ≠ 0
  exact (mul_pos (zero_lt_two' ℝ) (sqrt_pos.2 <| mul_pos z.im_pos w.im_pos)).ne'
  -- 🎉 no goals
#align upper_half_plane.tanh_half_dist UpperHalfPlane.tanh_half_dist

theorem exp_half_dist (z w : ℍ) :
    exp (dist z w / 2) = (dist (z : ℂ) w + dist (z : ℂ) (conj ↑w)) / (2 * sqrt (z.im * w.im)) := by
  rw [← sinh_add_cosh, sinh_half_dist, cosh_half_dist, add_div]
  -- 🎉 no goals
#align upper_half_plane.exp_half_dist UpperHalfPlane.exp_half_dist

theorem cosh_dist (z w : ℍ) : cosh (dist z w) = 1 + dist (z : ℂ) w ^ 2 / (2 * z.im * w.im) := by
  rw [dist_eq, cosh_two_mul, cosh_sq', add_assoc, ← two_mul, sinh_arsinh, div_pow, mul_pow,
    sq_sqrt (mul_pos z.im_pos w.im_pos).le, sq (2 : ℝ), mul_assoc, ← mul_div_assoc, mul_assoc,
    mul_div_mul_left _ _ (two_ne_zero' ℝ)]
#align upper_half_plane.cosh_dist UpperHalfPlane.cosh_dist

theorem sinh_half_dist_add_dist (a b c : ℍ) : sinh ((dist a b + dist b c) / 2) =
    (dist (a : ℂ) b * dist (c : ℂ) (conj ↑b) + dist (b : ℂ) c * dist (a : ℂ) (conj ↑b)) /
      (2 * sqrt (a.im * c.im) * dist (b : ℂ) (conj ↑b)) := by
  simp only [add_div _ _ (2 : ℝ), sinh_add, sinh_half_dist, cosh_half_dist, div_mul_div_comm]
  -- ⊢ dist ↑a ↑b * dist (↑b) (↑(starRingEnd ℂ) ↑c) / (2 * sqrt (im a * im b) * (2  …
  rw [← add_div, Complex.dist_self_conj, coe_im, abs_of_pos b.im_pos, mul_comm (dist (b : ℂ) _),
    dist_comm (b : ℂ), Complex.dist_conj_comm, mul_mul_mul_comm, mul_mul_mul_comm _ _ _ b.im]
  congr 2
  -- ⊢ sqrt (im a * im b) * sqrt (im b * im c) = sqrt (im a * im c) * im b
  rw [sqrt_mul, sqrt_mul, sqrt_mul, mul_comm (sqrt a.im), mul_mul_mul_comm, mul_self_sqrt,
      mul_comm] <;> exact (im_pos _).le
                    -- 🎉 no goals
                    -- 🎉 no goals
                    -- 🎉 no goals
                    -- 🎉 no goals
#align upper_half_plane.sinh_half_dist_add_dist UpperHalfPlane.sinh_half_dist_add_dist

protected theorem dist_comm (z w : ℍ) : dist z w = dist w z := by
  simp only [dist_eq, dist_comm (z : ℂ), mul_comm]
  -- 🎉 no goals
#align upper_half_plane.dist_comm UpperHalfPlane.dist_comm

theorem dist_le_iff_le_sinh :
    dist z w ≤ r ↔ dist (z : ℂ) w / (2 * sqrt (z.im * w.im)) ≤ sinh (r / 2) := by
  rw [← div_le_div_right (zero_lt_two' ℝ), ← sinh_le_sinh, sinh_half_dist]
  -- 🎉 no goals
#align upper_half_plane.dist_le_iff_le_sinh UpperHalfPlane.dist_le_iff_le_sinh

theorem dist_eq_iff_eq_sinh :
    dist z w = r ↔ dist (z : ℂ) w / (2 * sqrt (z.im * w.im)) = sinh (r / 2) := by
  rw [← div_left_inj' (two_ne_zero' ℝ), ← sinh_inj, sinh_half_dist]
  -- 🎉 no goals
#align upper_half_plane.dist_eq_iff_eq_sinh UpperHalfPlane.dist_eq_iff_eq_sinh

theorem dist_eq_iff_eq_sq_sinh (hr : 0 ≤ r) :
    dist z w = r ↔ dist (z : ℂ) w ^ 2 / (4 * z.im * w.im) = sinh (r / 2) ^ 2 := by
  rw [dist_eq_iff_eq_sinh, ← sq_eq_sq, div_pow, mul_pow, sq_sqrt, mul_assoc]
  · norm_num
    -- 🎉 no goals
  · exact (mul_pos z.im_pos w.im_pos).le
    -- 🎉 no goals
  · exact div_nonneg dist_nonneg (mul_nonneg zero_le_two <| sqrt_nonneg _)
    -- 🎉 no goals
  · exact sinh_nonneg_iff.2 (div_nonneg hr zero_le_two)
    -- 🎉 no goals
#align upper_half_plane.dist_eq_iff_eq_sq_sinh UpperHalfPlane.dist_eq_iff_eq_sq_sinh

protected theorem dist_triangle (a b c : ℍ) : dist a c ≤ dist a b + dist b c := by
  rw [dist_le_iff_le_sinh, sinh_half_dist_add_dist, div_mul_eq_div_div _ _ (dist _ _), le_div_iff,
    div_mul_eq_mul_div]
  · exact div_le_div_of_le (mul_nonneg zero_le_two (sqrt_nonneg _))
      (EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist (a : ℂ) b c (conj (b : ℂ)))
  · rw [dist_comm, dist_pos, Ne.def, Complex.conj_eq_iff_im]
    -- ⊢ ¬(↑b).im = 0
    exact b.im_ne_zero
    -- 🎉 no goals
#align upper_half_plane.dist_triangle UpperHalfPlane.dist_triangle

theorem dist_le_dist_coe_div_sqrt (z w : ℍ) : dist z w ≤ dist (z : ℂ) w / sqrt (z.im * w.im) := by
  rw [dist_le_iff_le_sinh, ← div_mul_eq_div_div_swap, self_le_sinh_iff]
  -- ⊢ 0 ≤ dist ↑z ↑w / (2 * sqrt (im z * im w))
  exact div_nonneg dist_nonneg (mul_nonneg zero_le_two (sqrt_nonneg _))
  -- 🎉 no goals
#align upper_half_plane.dist_le_dist_coe_div_sqrt UpperHalfPlane.dist_le_dist_coe_div_sqrt

/-- An auxiliary `MetricSpace` instance on the upper half-plane. This instance has bad projection
to `TopologicalSpace`. We replace it later. -/
def metricSpaceAux : MetricSpace ℍ where
  dist := dist
  dist_self z := by rw [dist_eq, dist_self, zero_div, arsinh_zero, mul_zero]
                    -- 🎉 no goals
  dist_comm := UpperHalfPlane.dist_comm
  dist_triangle := UpperHalfPlane.dist_triangle
  eq_of_dist_eq_zero {z w} h := by
    simpa [dist_eq, Real.sqrt_eq_zero', (mul_pos z.im_pos w.im_pos).not_le, ext_iff] using h
    -- 🎉 no goals
                       -- 🎉 no goals
  edist_dist _ _ := by exact ENNReal.coe_nnreal_eq _
#align upper_half_plane.metric_space_aux UpperHalfPlane.metricSpaceAux

open Complex

theorem cosh_dist' (z w : ℍ) :
    Real.cosh (dist z w) = ((z.re - w.re) ^ 2 + z.im ^ 2 + w.im ^ 2) / (2 * z.im * w.im) := by
  have H : 0 < 2 * z.im * w.im := mul_pos (mul_pos two_pos z.im_pos) w.im_pos
  -- ⊢ Real.cosh (dist z w) = ((re z - re w) ^ 2 + im z ^ 2 + im w ^ 2) / (2 * im z …
  field_simp [cosh_dist, Complex.dist_eq, Complex.sq_abs, normSq_apply, H, H.ne']
  -- ⊢ 2 * im z * im w + ((re z - re w) * (re z - re w) + (im z - im w) * (im z - i …
  ring
  -- 🎉 no goals
#align upper_half_plane.cosh_dist' UpperHalfPlane.cosh_dist'

/-- Euclidean center of the circle with center `z` and radius `r` in the hyperbolic metric. -/
def center (z : ℍ) (r : ℝ) : ℍ :=
  ⟨⟨z.re, z.im * Real.cosh r⟩, mul_pos z.im_pos (cosh_pos _)⟩
#align upper_half_plane.center UpperHalfPlane.center

@[simp]
theorem center_re (z r) : (center z r).re = z.re :=
  rfl
#align upper_half_plane.center_re UpperHalfPlane.center_re

@[simp]
theorem center_im (z r) : (center z r).im = z.im * Real.cosh r :=
  rfl
#align upper_half_plane.center_im UpperHalfPlane.center_im

@[simp]
theorem center_zero (z : ℍ) : center z 0 = z :=
  ext' rfl <| by rw [center_im, Real.cosh_zero, mul_one]
                 -- 🎉 no goals
#align upper_half_plane.center_zero UpperHalfPlane.center_zero

theorem dist_coe_center_sq (z w : ℍ) (r : ℝ) : dist (z : ℂ) (w.center r) ^ 2 =
    2 * z.im * w.im * (Real.cosh (dist z w) - Real.cosh r) + (w.im * Real.sinh r) ^ 2 := by
  have H : 2 * z.im * w.im ≠ 0 := by apply_rules [mul_ne_zero, two_ne_zero, im_ne_zero]
  -- ⊢ dist ↑z ↑(center w r) ^ 2 = 2 * im z * im w * (Real.cosh (dist z w) - Real.c …
  simp only [Complex.dist_eq, Complex.sq_abs, normSq_apply, coe_re, coe_im, center_re, center_im,
    cosh_dist', mul_div_cancel' _ H, sub_sq z.im, mul_pow, Real.cosh_sq, sub_re, sub_im, mul_sub, ←
    sq]
  ring
  -- 🎉 no goals
#align upper_half_plane.dist_coe_center_sq UpperHalfPlane.dist_coe_center_sq

theorem dist_coe_center (z w : ℍ) (r : ℝ) : dist (z : ℂ) (w.center r) =
    sqrt (2 * z.im * w.im * (Real.cosh (dist z w) - Real.cosh r) + (w.im * Real.sinh r) ^ 2) := by
  rw [← sqrt_sq dist_nonneg, dist_coe_center_sq]
  -- 🎉 no goals
#align upper_half_plane.dist_coe_center UpperHalfPlane.dist_coe_center

theorem cmp_dist_eq_cmp_dist_coe_center (z w : ℍ) (r : ℝ) :
    cmp (dist z w) r = cmp (dist (z : ℂ) (w.center r)) (w.im * Real.sinh r) := by
  letI := metricSpaceAux
  -- ⊢ cmp (dist z w) r = cmp (dist ↑z ↑(center w r)) (im w * Real.sinh r)
  cases' lt_or_le r 0 with hr₀ hr₀
  -- ⊢ cmp (dist z w) r = cmp (dist ↑z ↑(center w r)) (im w * Real.sinh r)
  · trans Ordering.gt
    -- ⊢ cmp (dist z w) r = Ordering.gt
    exacts [(hr₀.trans_le dist_nonneg).cmp_eq_gt,
      ((mul_neg_of_pos_of_neg w.im_pos (sinh_neg_iff.2 hr₀)).trans_le dist_nonneg).cmp_eq_gt.symm]
  have hr₀' : 0 ≤ w.im * Real.sinh r := mul_nonneg w.im_pos.le (sinh_nonneg_iff.2 hr₀)
  -- ⊢ cmp (dist z w) r = cmp (dist ↑z ↑(center w r)) (im w * Real.sinh r)
  have hzw₀ : 0 < 2 * z.im * w.im := mul_pos (mul_pos two_pos z.im_pos) w.im_pos
  -- ⊢ cmp (dist z w) r = cmp (dist ↑z ↑(center w r)) (im w * Real.sinh r)
  simp only [← cosh_strictMonoOn.cmp_map_eq dist_nonneg hr₀, ←
    (@strictMonoOn_pow ℝ _ _ two_pos).cmp_map_eq dist_nonneg hr₀', dist_coe_center_sq]
  rw [← cmp_mul_pos_left hzw₀, ← cmp_sub_zero, ← mul_sub, ← cmp_add_right, zero_add]
  -- 🎉 no goals
#align upper_half_plane.cmp_dist_eq_cmp_dist_coe_center UpperHalfPlane.cmp_dist_eq_cmp_dist_coe_center

theorem dist_eq_iff_dist_coe_center_eq :
    dist z w = r ↔ dist (z : ℂ) (w.center r) = w.im * Real.sinh r :=
  eq_iff_eq_of_cmp_eq_cmp (cmp_dist_eq_cmp_dist_coe_center z w r)
#align upper_half_plane.dist_eq_iff_dist_coe_center_eq UpperHalfPlane.dist_eq_iff_dist_coe_center_eq

@[simp]
theorem dist_self_center (z : ℍ) (r : ℝ) :
    dist (z : ℂ) (z.center r) = z.im * (Real.cosh r - 1) := by
  rw [dist_of_re_eq (z.center_re r).symm, dist_comm, Real.dist_eq, mul_sub, mul_one]
  -- ⊢ |(↑(center z r)).im - (↑z).im| = im z * Real.cosh r - im z
  exact abs_of_nonneg (sub_nonneg.2 <| le_mul_of_one_le_right z.im_pos.le (one_le_cosh _))
  -- 🎉 no goals
#align upper_half_plane.dist_self_center UpperHalfPlane.dist_self_center

@[simp]
theorem dist_center_dist (z w : ℍ) :
    dist (z : ℂ) (w.center (dist z w)) = w.im * Real.sinh (dist z w) :=
  dist_eq_iff_dist_coe_center_eq.1 rfl
#align upper_half_plane.dist_center_dist UpperHalfPlane.dist_center_dist

theorem dist_lt_iff_dist_coe_center_lt :
    dist z w < r ↔ dist (z : ℂ) (w.center r) < w.im * Real.sinh r :=
  lt_iff_lt_of_cmp_eq_cmp (cmp_dist_eq_cmp_dist_coe_center z w r)
#align upper_half_plane.dist_lt_iff_dist_coe_center_lt UpperHalfPlane.dist_lt_iff_dist_coe_center_lt

theorem lt_dist_iff_lt_dist_coe_center :
    r < dist z w ↔ w.im * Real.sinh r < dist (z : ℂ) (w.center r) :=
  lt_iff_lt_of_cmp_eq_cmp (cmp_eq_cmp_symm.1 <| cmp_dist_eq_cmp_dist_coe_center z w r)
#align upper_half_plane.lt_dist_iff_lt_dist_coe_center UpperHalfPlane.lt_dist_iff_lt_dist_coe_center

theorem dist_le_iff_dist_coe_center_le :
    dist z w ≤ r ↔ dist (z : ℂ) (w.center r) ≤ w.im * Real.sinh r :=
  le_iff_le_of_cmp_eq_cmp (cmp_dist_eq_cmp_dist_coe_center z w r)
#align upper_half_plane.dist_le_iff_dist_coe_center_le UpperHalfPlane.dist_le_iff_dist_coe_center_le

theorem le_dist_iff_le_dist_coe_center :
    r < dist z w ↔ w.im * Real.sinh r < dist (z : ℂ) (w.center r) :=
  lt_iff_lt_of_cmp_eq_cmp (cmp_eq_cmp_symm.1 <| cmp_dist_eq_cmp_dist_coe_center z w r)
#align upper_half_plane.le_dist_iff_le_dist_coe_center UpperHalfPlane.le_dist_iff_le_dist_coe_center

/-- For two points on the same vertical line, the distance is equal to the distance between the
logarithms of their imaginary parts. -/
nonrec theorem dist_of_re_eq (h : z.re = w.re) : dist z w = dist (log z.im) (log w.im) := by
  have h₀ : 0 < z.im / w.im := div_pos z.im_pos w.im_pos
  -- ⊢ dist z w = dist (log (im z)) (log (im w))
  rw [dist_eq_iff_dist_coe_center_eq, Real.dist_eq, ← abs_sinh, ← log_div z.im_ne_zero w.im_ne_zero,
    sinh_log h₀, dist_of_re_eq, coe_im, coe_im, center_im, cosh_abs, cosh_log h₀, inv_div] <;>
  [skip; exact h]
  nth_rw 4 [← abs_of_pos w.im_pos]
  -- ⊢ dist (im z) (im w * ((im z / im w + im w / im z) / 2)) = |im w| * |(im z / i …
  simp only [← _root_.abs_mul, coe_im, Real.dist_eq]
  -- ⊢ |im z - im w * ((im z / im w + im w / im z) / 2)| = |im w * ((im z / im w -  …
  congr 1
  -- ⊢ im z - im w * ((im z / im w + im w / im z) / 2) = im w * ((im z / im w - im  …
  field_simp [z.im_pos, w.im_pos, z.im_ne_zero, w.im_ne_zero]
  -- ⊢ im z * (im w * im z * 2) - im w * (im z * im z + im w * im w) = im w * (im z …
  ring
  -- 🎉 no goals
#align upper_half_plane.dist_of_re_eq UpperHalfPlane.dist_of_re_eq

/-- Hyperbolic distance between two points is greater than or equal to the distance between the
logarithms of their imaginary parts. -/
theorem dist_log_im_le (z w : ℍ) : dist (log z.im) (log w.im) ≤ dist z w :=
  calc
    dist (log z.im) (log w.im) = dist (mk ⟨0, z.im⟩ z.im_pos) (mk ⟨0, w.im⟩ w.im_pos) :=
      Eq.symm <| dist_of_re_eq rfl
    _ ≤ dist z w := mul_le_mul_of_nonneg_left (arsinh_le_arsinh.2 <|
      div_le_div_of_le (mul_nonneg zero_le_two (sqrt_nonneg _)) <| by
        simpa [sqrt_sq_eq_abs] using Complex.abs_im_le_abs (z - w)) zero_le_two
        -- 🎉 no goals
#align upper_half_plane.dist_log_im_le UpperHalfPlane.dist_log_im_le

theorem im_le_im_mul_exp_dist (z w : ℍ) : z.im ≤ w.im * Real.exp (dist z w) := by
  rw [← div_le_iff' w.im_pos, ← exp_log z.im_pos, ← exp_log w.im_pos, ← Real.exp_sub, exp_le_exp]
  -- ⊢ log (im z) - log (im w) ≤ dist z w
  exact (le_abs_self _).trans (dist_log_im_le z w)
  -- 🎉 no goals
#align upper_half_plane.im_le_im_mul_exp_dist UpperHalfPlane.im_le_im_mul_exp_dist

theorem im_div_exp_dist_le (z w : ℍ) : z.im / Real.exp (dist z w) ≤ w.im :=
  (div_le_iff (exp_pos _)).2 (im_le_im_mul_exp_dist z w)
#align upper_half_plane.im_div_exp_dist_le UpperHalfPlane.im_div_exp_dist_le

/-- An upper estimate on the complex distance between two points in terms of the hyperbolic distance
and the imaginary part of one of the points. -/
theorem dist_coe_le (z w : ℍ) : dist (z : ℂ) w ≤ w.im * (Real.exp (dist z w) - 1) :=
  calc
    dist (z : ℂ) w ≤ dist (z : ℂ) (w.center (dist z w)) + dist (w : ℂ) (w.center (dist z w)) :=
      dist_triangle_right _ _ _
    _ = w.im * (Real.exp (dist z w) - 1) := by
      rw [dist_center_dist, dist_self_center, ← mul_add, ← add_sub_assoc, Real.sinh_add_cosh]
      -- 🎉 no goals
#align upper_half_plane.dist_coe_le UpperHalfPlane.dist_coe_le

/-- An upper estimate on the complex distance between two points in terms of the hyperbolic distance
and the imaginary part of one of the points. -/
theorem le_dist_coe (z w : ℍ) : w.im * (1 - Real.exp (-dist z w)) ≤ dist (z : ℂ) w :=
  calc
    w.im * (1 - Real.exp (-dist z w)) =
        dist (z : ℂ) (w.center (dist z w)) - dist (w : ℂ) (w.center (dist z w)) := by
      rw [dist_center_dist, dist_self_center, ← Real.cosh_sub_sinh]; ring
      -- ⊢ im w * (1 - (Real.cosh (dist z w) - Real.sinh (dist z w))) = im w * Real.sin …
                                                                     -- 🎉 no goals
    _ ≤ dist (z : ℂ) w := sub_le_iff_le_add.2 <| dist_triangle _ _ _
#align upper_half_plane.le_dist_coe UpperHalfPlane.le_dist_coe

/-- The hyperbolic metric on the upper half plane. We ensure that the projection to
`TopologicalSpace` is definitionally equal to the subtype topology. -/
instance : MetricSpace ℍ :=
  metricSpaceAux.replaceTopology <| by
    refine' le_antisymm (continuous_id_iff_le.1 _) _
    -- ⊢ Continuous id
    · refine' (@continuous_iff_continuous_dist ℍ ℍ metricSpaceAux.toPseudoMetricSpace _ _).2 _
      -- ⊢ Continuous fun x => dist (id x.fst) (id x.snd)
      have : ∀ x : ℍ × ℍ, 2 * Real.sqrt (x.1.im * x.2.im) ≠ 0 := fun x =>
        mul_ne_zero two_ne_zero (Real.sqrt_pos.2 <| mul_pos x.1.im_pos x.2.im_pos).ne'
      -- `continuity` fails to apply `Continuous.div`
      apply_rules [Continuous.div, Continuous.mul, continuous_const, Continuous.arsinh,
        Continuous.dist, continuous_coe.comp, continuous_fst, continuous_snd,
        Real.continuous_sqrt.comp, continuous_im.comp]
    · letI : MetricSpace ℍ := metricSpaceAux
      -- ⊢ UniformSpace.toTopologicalSpace ≤ instTopologicalSpaceUpperHalfPlane
      refine' le_of_nhds_le_nhds fun z => _
      -- ⊢ 𝓝 z ≤ 𝓝 z
      rw [nhds_induced]
      -- ⊢ 𝓝 z ≤ comap Subtype.val (𝓝 ↑z)
      refine' (nhds_basis_ball.le_basis_iff (nhds_basis_ball.comap _)).2 fun R hR => _
      -- ⊢ ∃ i, 0 < i ∧ ball z i ⊆ Subtype.val ⁻¹' ball (↑z) R
      have h₁ : 1 < R / im z + 1 := lt_add_of_pos_left _ (div_pos hR z.im_pos)
      -- ⊢ ∃ i, 0 < i ∧ ball z i ⊆ Subtype.val ⁻¹' ball (↑z) R
      have h₀ : 0 < R / im z + 1 := one_pos.trans h₁
      -- ⊢ ∃ i, 0 < i ∧ ball z i ⊆ Subtype.val ⁻¹' ball (↑z) R
      refine' ⟨log (R / im z + 1), Real.log_pos h₁, _⟩
      -- ⊢ ball z (log (R / im z + 1)) ⊆ Subtype.val ⁻¹' ball (↑z) R
      refine' fun w hw => (dist_coe_le w z).trans_lt _
      -- ⊢ im z * (Real.exp (dist w z) - 1) < R
      rwa [← lt_div_iff' z.im_pos, sub_lt_iff_lt_add, ← Real.lt_log_iff_exp_lt h₀]
      -- 🎉 no goals

theorem im_pos_of_dist_center_le {z : ℍ} {r : ℝ} {w : ℂ}
    (h : dist w (center z r) ≤ z.im * Real.sinh r) : 0 < w.im :=
  calc
    0 < z.im * (Real.cosh r - Real.sinh r) := mul_pos z.im_pos (sub_pos.2 <| sinh_lt_cosh _)
    _ = (z.center r).im - z.im * Real.sinh r := (mul_sub _ _ _)
    _ ≤ (z.center r).im - dist (z.center r : ℂ) w := (sub_le_sub_left (by rwa [dist_comm]) _)
                                                                          -- 🎉 no goals
    _ ≤ w.im := sub_le_comm.1 <| (le_abs_self _).trans (abs_im_le_abs <| z.center r - w)
#align upper_half_plane.im_pos_of_dist_center_le UpperHalfPlane.im_pos_of_dist_center_le

theorem image_coe_closedBall (z : ℍ) (r : ℝ) :
    ((↑) : ℍ → ℂ) '' closedBall (α := ℍ) z r = closedBall ↑(z.center r) (z.im * Real.sinh r) := by
  ext w; constructor
  -- ⊢ w ∈ UpperHalfPlane.coe '' closedBall z r ↔ w ∈ closedBall (↑(center z r)) (i …
         -- ⊢ w ∈ UpperHalfPlane.coe '' closedBall z r → w ∈ closedBall (↑(center z r)) (i …
  · rintro ⟨w, hw, rfl⟩
    -- ⊢ ↑w ∈ closedBall (↑(center z r)) (im z * Real.sinh r)
    exact dist_le_iff_dist_coe_center_le.1 hw
    -- 🎉 no goals
  · intro hw
    -- ⊢ w ∈ UpperHalfPlane.coe '' closedBall z r
    lift w to ℍ using im_pos_of_dist_center_le hw
    -- ⊢ ↑w ∈ UpperHalfPlane.coe '' closedBall z r
    exact mem_image_of_mem _ (dist_le_iff_dist_coe_center_le.2 hw)
    -- 🎉 no goals
#align upper_half_plane.image_coe_closed_ball UpperHalfPlane.image_coe_closedBall

theorem image_coe_ball (z : ℍ) (r : ℝ) :
    ((↑) : ℍ → ℂ) '' ball (α := ℍ) z r = ball ↑(z.center r) (z.im * Real.sinh r) := by
  ext w; constructor
  -- ⊢ w ∈ UpperHalfPlane.coe '' ball z r ↔ w ∈ ball (↑(center z r)) (im z * Real.s …
         -- ⊢ w ∈ UpperHalfPlane.coe '' ball z r → w ∈ ball (↑(center z r)) (im z * Real.s …
  · rintro ⟨w, hw, rfl⟩
    -- ⊢ ↑w ∈ ball (↑(center z r)) (im z * Real.sinh r)
    exact dist_lt_iff_dist_coe_center_lt.1 hw
    -- 🎉 no goals
  · intro hw
    -- ⊢ w ∈ UpperHalfPlane.coe '' ball z r
    lift w to ℍ using im_pos_of_dist_center_le (ball_subset_closedBall hw)
    -- ⊢ ↑w ∈ UpperHalfPlane.coe '' ball z r
    exact mem_image_of_mem _ (dist_lt_iff_dist_coe_center_lt.2 hw)
    -- 🎉 no goals
#align upper_half_plane.image_coe_ball UpperHalfPlane.image_coe_ball

theorem image_coe_sphere (z : ℍ) (r : ℝ) :
    ((↑) : ℍ → ℂ) '' sphere (α := ℍ) z r = sphere ↑(z.center r) (z.im * Real.sinh r) := by
  ext w; constructor
  -- ⊢ w ∈ UpperHalfPlane.coe '' sphere z r ↔ w ∈ sphere (↑(center z r)) (im z * Re …
         -- ⊢ w ∈ UpperHalfPlane.coe '' sphere z r → w ∈ sphere (↑(center z r)) (im z * Re …
  · rintro ⟨w, hw, rfl⟩
    -- ⊢ ↑w ∈ sphere (↑(center z r)) (im z * Real.sinh r)
    exact dist_eq_iff_dist_coe_center_eq.1 hw
    -- 🎉 no goals
  · intro hw
    -- ⊢ w ∈ UpperHalfPlane.coe '' sphere z r
    lift w to ℍ using im_pos_of_dist_center_le (sphere_subset_closedBall hw)
    -- ⊢ ↑w ∈ UpperHalfPlane.coe '' sphere z r
    exact mem_image_of_mem _ (dist_eq_iff_dist_coe_center_eq.2 hw)
    -- 🎉 no goals
#align upper_half_plane.image_coe_sphere UpperHalfPlane.image_coe_sphere

instance : ProperSpace ℍ := by
  refine' ⟨fun z r => _⟩
  -- ⊢ IsCompact (closedBall z r)
  rw [← inducing_subtype_val.isCompact_iff (f := ((↑) : ℍ → ℂ)), image_coe_closedBall]
  -- ⊢ IsCompact (closedBall (↑(center z r)) (im z * Real.sinh r))
  apply isCompact_closedBall
  -- 🎉 no goals

theorem isometry_vertical_line (a : ℝ) : Isometry fun y => mk ⟨a, exp y⟩ (exp_pos y) := by
  refine' Isometry.of_dist_eq fun y₁ y₂ => _
  -- ⊢ dist (mk { re := a, im := Real.exp y₁ } (_ : 0 < Real.exp y₁)) (mk { re := a …
  rw [dist_of_re_eq]
  -- ⊢ dist (log (im (mk { re := a, im := Real.exp y₁ } (_ : 0 < Real.exp y₁)))) (l …
  exacts [congr_arg₂ _ (log_exp _) (log_exp _), rfl]
  -- 🎉 no goals
#align upper_half_plane.isometry_vertical_line UpperHalfPlane.isometry_vertical_line

theorem isometry_real_vadd (a : ℝ) : Isometry ((· +ᵥ ·) a : ℍ → ℍ) :=
  Isometry.of_dist_eq fun y₁ y₂ => by simp only [dist_eq, coe_vadd, vadd_im, dist_add_left]
                                      -- 🎉 no goals
#align upper_half_plane.isometry_real_vadd UpperHalfPlane.isometry_real_vadd

theorem isometry_pos_mul (a : { x : ℝ // 0 < x }) : Isometry ((· • ·) a : ℍ → ℍ) := by
  refine' Isometry.of_dist_eq fun y₁ y₂ => _
  -- ⊢ dist ((fun x x_1 => x • x_1) a y₁) ((fun x x_1 => x • x_1) a y₂) = dist y₁ y₂
  simp only [dist_eq, coe_pos_real_smul, pos_real_im]; congr 2
  -- ⊢ 2 * arsinh (dist (↑a • ↑y₁) (↑a • ↑y₂) / (2 * sqrt (↑a * im y₁ * (↑a * im y₂ …
                                                       -- ⊢ dist (↑a • ↑y₁) (↑a • ↑y₂) / (2 * sqrt (↑a * im y₁ * (↑a * im y₂))) = dist ↑ …
  rw [dist_smul₀, mul_mul_mul_comm, Real.sqrt_mul (mul_self_nonneg _), Real.sqrt_mul_self_eq_abs,
    Real.norm_eq_abs, mul_left_comm]
  exact mul_div_mul_left _ _ (mt _root_.abs_eq_zero.1 a.2.ne')
  -- 🎉 no goals
#align upper_half_plane.isometry_pos_mul UpperHalfPlane.isometry_pos_mul

/-- `SL(2, ℝ)` acts on the upper half plane as an isometry.-/
instance : IsometricSMul SL(2, ℝ) ℍ :=
  ⟨fun g => by
    have h₀ : Isometry (fun z => ModularGroup.S • z : ℍ → ℍ) :=
      Isometry.of_dist_eq fun y₁ y₂ => by
        have h₁ : 0 ≤ im y₁ * im y₂ := mul_nonneg y₁.property.le y₂.property.le
        have h₂ : Complex.abs (y₁ * y₂) ≠ 0 := by simp [y₁.ne_zero, y₂.ne_zero]
        simp only [dist_eq, modular_S_smul, inv_neg, neg_div, div_mul_div_comm, coe_mk, mk_im,
          div_one, Complex.inv_im, Complex.neg_im, coe_im, neg_neg, Complex.normSq_neg,
          mul_eq_mul_left_iff, Real.arsinh_inj, bit0_eq_zero, one_ne_zero, or_false_iff,
          dist_neg_neg, mul_neg, neg_mul, dist_inv_inv₀ y₁.ne_zero y₂.ne_zero, ←
          AbsoluteValue.map_mul, ← Complex.normSq_mul, Real.sqrt_div h₁, ← Complex.abs_apply,
          mul_div (2 : ℝ), div_div_div_comm, div_self h₂, Complex.norm_eq_abs]
    by_cases hc : g 1 0 = 0
    -- ⊢ Isometry fun x => g • x
    · obtain ⟨u, v, h⟩ := exists_SL2_smul_eq_of_apply_zero_one_eq_zero g hc
      -- ⊢ Isometry fun x => g • x
      dsimp only at h
      -- ⊢ Isometry fun x => g • x
      rw [h]
      -- ⊢ Isometry ((fun z => v +ᵥ z) ∘ fun z => u • z)
      exact (isometry_real_vadd v).comp (isometry_pos_mul u)
      -- 🎉 no goals
    · obtain ⟨u, v, w, h⟩ := exists_SL2_smul_eq_of_apply_zero_one_ne_zero g hc
      -- ⊢ Isometry fun x => g • x
      dsimp only at h
      -- ⊢ Isometry fun x => g • x
      rw [h]
      -- ⊢ Isometry ((fun x => w +ᵥ x) ∘ (fun x => ModularGroup.S • x) ∘ (fun x => v +ᵥ …
      exact
        (isometry_real_vadd w).comp (h₀.comp <| (isometry_real_vadd v).comp <| isometry_pos_mul u)⟩

end UpperHalfPlane
