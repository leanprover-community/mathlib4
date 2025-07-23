/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Geometry.Euclidean.Inversion.Basic

/-!
# Metric on the upper half-plane

In this file we define a `MetricSpace` structure on the `UpperHalfPlane`. We use hyperbolic
(Poincaré) distance given by
`dist z w = 2 * arsinh (dist (z : ℂ) w / (2 * √(z.im * w.im)))` instead of the induced
Euclidean distance because the hyperbolic distance is invariant under holomorphic automorphisms of
the upper half-plane. However, we ensure that the projection to `TopologicalSpace` is
definitionally equal to the induced topological space structure.

We also prove that a metric ball/closed ball/sphere in Poincaré metric is a Euclidean ball/closed
ball/sphere with another center and radius.

-/


noncomputable section

open Filter Metric Real Set Topology
open scoped UpperHalfPlane ComplexConjugate NNReal Topology MatrixGroups

variable {z w : ℍ} {r : ℝ}

namespace UpperHalfPlane

instance : Dist ℍ :=
  ⟨fun z w => 2 * arsinh (dist (z : ℂ) w / (2 * √(z.im * w.im)))⟩

theorem dist_eq (z w : ℍ) : dist z w = 2 * arsinh (dist (z : ℂ) w / (2 * √(z.im * w.im))) :=
  rfl

theorem sinh_half_dist (z w : ℍ) :
    sinh (dist z w / 2) = dist (z : ℂ) w / (2 * √(z.im * w.im)) := by
  rw [dist_eq, mul_div_cancel_left₀ (arsinh _) two_ne_zero, sinh_arsinh]

theorem cosh_half_dist (z w : ℍ) :
    cosh (dist z w / 2) = dist (z : ℂ) (conj (w : ℂ)) / (2 * √(z.im * w.im)) := by
  rw [← sq_eq_sq₀, cosh_sq', sinh_half_dist, div_pow, div_pow, one_add_div, mul_pow, sq_sqrt]
  · congr 1
    simp only [Complex.dist_eq, Complex.sq_norm, Complex.normSq_sub, Complex.normSq_conj,
      Complex.conj_conj, Complex.mul_re, Complex.conj_re, Complex.conj_im, coe_im]
    ring
  all_goals positivity

theorem tanh_half_dist (z w : ℍ) :
    tanh (dist z w / 2) = dist (z : ℂ) w / dist (z : ℂ) (conj ↑w) := by
  rw [tanh_eq_sinh_div_cosh, sinh_half_dist, cosh_half_dist, div_div_div_comm, div_self, div_one]
  positivity

theorem exp_half_dist (z w : ℍ) :
    exp (dist z w / 2) = (dist (z : ℂ) w + dist (z : ℂ) (conj ↑w)) / (2 * √(z.im * w.im)) := by
  rw [← sinh_add_cosh, sinh_half_dist, cosh_half_dist, add_div]

theorem cosh_dist (z w : ℍ) : cosh (dist z w) = 1 + dist (z : ℂ) w ^ 2 / (2 * z.im * w.im) := by
  rw [dist_eq, cosh_two_mul, cosh_sq', add_assoc, ← two_mul, sinh_arsinh, div_pow, mul_pow,
    sq_sqrt, sq (2 : ℝ), mul_assoc, ← mul_div_assoc, mul_assoc, mul_div_mul_left] <;> positivity

theorem sinh_half_dist_add_dist (a b c : ℍ) : sinh ((dist a b + dist b c) / 2) =
    (dist (a : ℂ) b * dist (c : ℂ) (conj ↑b) + dist (b : ℂ) c * dist (a : ℂ) (conj ↑b)) /
      (2 * √(a.im * c.im) * dist (b : ℂ) (conj ↑b)) := by
  simp only [add_div _ _ (2 : ℝ), sinh_add, sinh_half_dist, cosh_half_dist, div_mul_div_comm]
  rw [← add_div, Complex.dist_self_conj, coe_im, abs_of_pos b.im_pos, mul_comm (dist (b : ℂ) _),
    dist_comm (b : ℂ), Complex.dist_conj_comm, mul_mul_mul_comm, mul_mul_mul_comm _ _ _ b.im]
  congr 2
  rw [sqrt_mul, sqrt_mul, sqrt_mul, mul_comm (√a.im), mul_mul_mul_comm, mul_self_sqrt,
      mul_comm] <;> exact (im_pos _).le

protected theorem dist_comm (z w : ℍ) : dist z w = dist w z := by
  simp only [dist_eq, dist_comm (z : ℂ), mul_comm]

theorem dist_le_iff_le_sinh :
    dist z w ≤ r ↔ dist (z : ℂ) w / (2 * √(z.im * w.im)) ≤ sinh (r / 2) := by
  rw [← div_le_div_iff_of_pos_right (zero_lt_two' ℝ), ← sinh_le_sinh, sinh_half_dist]

theorem dist_eq_iff_eq_sinh :
    dist z w = r ↔ dist (z : ℂ) w / (2 * √(z.im * w.im)) = sinh (r / 2) := by
  rw [← div_left_inj' (two_ne_zero' ℝ), ← sinh_inj, sinh_half_dist]

theorem dist_eq_iff_eq_sq_sinh (hr : 0 ≤ r) :
    dist z w = r ↔ dist (z : ℂ) w ^ 2 / (4 * z.im * w.im) = sinh (r / 2) ^ 2 := by
  rw [dist_eq_iff_eq_sinh, ← sq_eq_sq₀, div_pow, mul_pow, sq_sqrt, mul_assoc]
  · norm_num
  all_goals positivity

protected theorem dist_triangle (a b c : ℍ) : dist a c ≤ dist a b + dist b c := by
  rw [dist_le_iff_le_sinh, sinh_half_dist_add_dist, div_mul_eq_div_div _ _ (dist _ _), le_div_iff₀,
    div_mul_eq_mul_div]
  · gcongr
    exact EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist (a : ℂ) b c (conj (b : ℂ))
  · rw [dist_comm, dist_pos, Ne, Complex.conj_eq_iff_im]
    exact b.im_ne_zero

theorem dist_le_dist_coe_div_sqrt (z w : ℍ) : dist z w ≤ dist (z : ℂ) w / √(z.im * w.im) := by
  rw [dist_le_iff_le_sinh, ← div_mul_eq_div_div_swap, self_le_sinh_iff]
  positivity

/-- An auxiliary `MetricSpace` instance on the upper half-plane. This instance has bad projection
to `TopologicalSpace`. We replace it later. -/
def metricSpaceAux : MetricSpace ℍ where
  dist := dist
  dist_self z := by rw [dist_eq, dist_self, zero_div, arsinh_zero, mul_zero]
  dist_comm := UpperHalfPlane.dist_comm
  dist_triangle := UpperHalfPlane.dist_triangle
  eq_of_dist_eq_zero {z w} h := by
    simpa [dist_eq, Real.sqrt_eq_zero', (mul_pos z.im_pos w.im_pos).not_ge, Set.ext_iff] using h

open Complex

theorem cosh_dist' (z w : ℍ) :
    Real.cosh (dist z w) = ((z.re - w.re) ^ 2 + z.im ^ 2 + w.im ^ 2) / (2 * z.im * w.im) := by
  field_simp [cosh_dist, Complex.dist_eq, Complex.sq_norm, normSq_apply]
  ring

/-- Euclidean center of the circle with center `z` and radius `r` in the hyperbolic metric. -/
def center (z : ℍ) (r : ℝ) : ℍ :=
  ⟨⟨z.re, z.im * Real.cosh r⟩, by positivity⟩

@[simp]
theorem center_re (z r) : (center z r).re = z.re :=
  rfl

@[simp]
theorem center_im (z r) : (center z r).im = z.im * Real.cosh r :=
  rfl

@[simp]
theorem center_zero (z : ℍ) : center z 0 = z :=
  ext' rfl <| by rw [center_im, Real.cosh_zero, mul_one]

theorem dist_coe_center_sq (z w : ℍ) (r : ℝ) : dist (z : ℂ) (w.center r) ^ 2 =
    2 * z.im * w.im * (Real.cosh (dist z w) - Real.cosh r) + (w.im * Real.sinh r) ^ 2 := by
  have H : 2 * z.im * w.im ≠ 0 := by positivity
  simp only [Complex.dist_eq, Complex.sq_norm, normSq_apply, coe_re, coe_im, center_re, center_im,
    cosh_dist', mul_div_cancel₀ _ H, sub_sq z.im, mul_pow, Real.cosh_sq, sub_re, sub_im, mul_sub, ←
    sq]
  ring

theorem dist_coe_center (z w : ℍ) (r : ℝ) : dist (z : ℂ) (w.center r) =
    √(2 * z.im * w.im * (Real.cosh (dist z w) - Real.cosh r) + (w.im * Real.sinh r) ^ 2) := by
  rw [← sqrt_sq dist_nonneg, dist_coe_center_sq]

theorem cmp_dist_eq_cmp_dist_coe_center (z w : ℍ) (r : ℝ) :
    cmp (dist z w) r = cmp (dist (z : ℂ) (w.center r)) (w.im * Real.sinh r) := by
  letI := metricSpaceAux
  rcases lt_or_ge r 0 with hr₀ | hr₀
  · trans Ordering.gt
    exacts [(hr₀.trans_le dist_nonneg).cmp_eq_gt,
      ((mul_neg_of_pos_of_neg w.im_pos (sinh_neg_iff.2 hr₀)).trans_le dist_nonneg).cmp_eq_gt.symm]
  have hr₀' : 0 ≤ w.im * Real.sinh r := by positivity
  have hzw₀ : 0 < 2 * z.im * w.im := by positivity
  simp only [← cosh_strictMonoOn.cmp_map_eq dist_nonneg hr₀,
    ← (pow_left_strictMonoOn₀ (M₀ := ℝ) two_ne_zero).cmp_map_eq dist_nonneg hr₀',
    dist_coe_center_sq]
  rw [← cmp_mul_pos_left hzw₀, ← cmp_sub_zero, ← mul_sub, ← cmp_add_right, zero_add]

theorem dist_eq_iff_dist_coe_center_eq :
    dist z w = r ↔ dist (z : ℂ) (w.center r) = w.im * Real.sinh r :=
  eq_iff_eq_of_cmp_eq_cmp (cmp_dist_eq_cmp_dist_coe_center z w r)

@[simp]
theorem dist_self_center (z : ℍ) (r : ℝ) :
    dist (z : ℂ) (z.center r) = z.im * (Real.cosh r - 1) := by
  rw [dist_of_re_eq (z.center_re r).symm, dist_comm, Real.dist_eq, mul_sub, mul_one]
  exact abs_of_nonneg (sub_nonneg.2 <| le_mul_of_one_le_right z.im_pos.le (one_le_cosh _))

@[simp]
theorem dist_center_dist (z w : ℍ) :
    dist (z : ℂ) (w.center (dist z w)) = w.im * Real.sinh (dist z w) :=
  dist_eq_iff_dist_coe_center_eq.1 rfl

theorem dist_lt_iff_dist_coe_center_lt :
    dist z w < r ↔ dist (z : ℂ) (w.center r) < w.im * Real.sinh r :=
  lt_iff_lt_of_cmp_eq_cmp (cmp_dist_eq_cmp_dist_coe_center z w r)

theorem lt_dist_iff_lt_dist_coe_center :
    r < dist z w ↔ w.im * Real.sinh r < dist (z : ℂ) (w.center r) :=
  lt_iff_lt_of_cmp_eq_cmp (cmp_eq_cmp_symm.1 <| cmp_dist_eq_cmp_dist_coe_center z w r)

theorem dist_le_iff_dist_coe_center_le :
    dist z w ≤ r ↔ dist (z : ℂ) (w.center r) ≤ w.im * Real.sinh r :=
  le_iff_le_of_cmp_eq_cmp (cmp_dist_eq_cmp_dist_coe_center z w r)

theorem le_dist_iff_le_dist_coe_center :
    r < dist z w ↔ w.im * Real.sinh r < dist (z : ℂ) (w.center r) :=
  lt_iff_lt_of_cmp_eq_cmp (cmp_eq_cmp_symm.1 <| cmp_dist_eq_cmp_dist_coe_center z w r)

/-- For two points on the same vertical line, the distance is equal to the distance between the
logarithms of their imaginary parts. -/
nonrec theorem dist_of_re_eq (h : z.re = w.re) : dist z w = dist (log z.im) (log w.im) := by
  have h₀ : 0 < z.im / w.im := by positivity
  rw [dist_eq_iff_dist_coe_center_eq, Real.dist_eq, ← abs_sinh, ← log_div z.im_ne_zero w.im_ne_zero,
    sinh_log h₀, dist_of_re_eq, coe_im, coe_im, center_im, cosh_abs, cosh_log h₀, inv_div] <;>
  [skip; exact h]
  nth_rw 4 [← abs_of_pos w.im_pos]
  simp only [← _root_.abs_mul, Real.dist_eq]
  congr 1
  field_simp
  ring
/-- Hyperbolic distance between two points is greater than or equal to the distance between the
logarithms of their imaginary parts. -/
theorem dist_log_im_le (z w : ℍ) : dist (log z.im) (log w.im) ≤ dist z w :=
  calc
    dist (log z.im) (log w.im) = dist (mk ⟨0, z.im⟩ z.im_pos) (mk ⟨0, w.im⟩ w.im_pos) :=
      Eq.symm <| dist_of_re_eq rfl
    _ ≤ dist z w := by
      simp_rw [dist_eq]
      dsimp only [coe_mk, mk_im]
      gcongr
      simpa [sqrt_sq_eq_abs] using Complex.abs_im_le_norm (z - w)

theorem im_le_im_mul_exp_dist (z w : ℍ) : z.im ≤ w.im * Real.exp (dist z w) := by
  rw [← div_le_iff₀' w.im_pos, ← exp_log z.im_pos, ← exp_log w.im_pos, ← Real.exp_sub, exp_le_exp]
  exact (le_abs_self _).trans (dist_log_im_le z w)

theorem im_div_exp_dist_le (z w : ℍ) : z.im / Real.exp (dist z w) ≤ w.im :=
  (div_le_iff₀ (exp_pos _)).2 (im_le_im_mul_exp_dist z w)

/-- An upper estimate on the complex distance between two points in terms of the hyperbolic distance
and the imaginary part of one of the points. -/
theorem dist_coe_le (z w : ℍ) : dist (z : ℂ) w ≤ w.im * (Real.exp (dist z w) - 1) :=
  calc
    dist (z : ℂ) w ≤ dist (z : ℂ) (w.center (dist z w)) + dist (w : ℂ) (w.center (dist z w)) :=
      dist_triangle_right _ _ _
    _ = w.im * (Real.exp (dist z w) - 1) := by
      rw [dist_center_dist, dist_self_center, ← mul_add, ← add_sub_assoc, Real.sinh_add_cosh]

/-- An upper estimate on the complex distance between two points in terms of the hyperbolic distance
and the imaginary part of one of the points. -/
theorem le_dist_coe (z w : ℍ) : w.im * (1 - Real.exp (-dist z w)) ≤ dist (z : ℂ) w :=
  calc
    w.im * (1 - Real.exp (-dist z w)) =
        dist (z : ℂ) (w.center (dist z w)) - dist (w : ℂ) (w.center (dist z w)) := by
      rw [dist_center_dist, dist_self_center, ← Real.cosh_sub_sinh]; ring
    _ ≤ dist (z : ℂ) w := sub_le_iff_le_add.2 <| dist_triangle _ _ _

/-- The hyperbolic metric on the upper half plane. We ensure that the projection to
`TopologicalSpace` is definitionally equal to the subtype topology. -/
instance : MetricSpace ℍ :=
  metricSpaceAux.replaceTopology <| by
    refine le_antisymm (continuous_id_iff_le.1 ?_) ?_
    · refine (@continuous_iff_continuous_dist ℍ ℍ metricSpaceAux.toPseudoMetricSpace _ _).2 ?_
      have : ∀ x : ℍ × ℍ, 2 * √(x.1.im * x.2.im) ≠ 0 := fun x => by positivity
      -- `continuity` fails to apply `Continuous.div`
      apply_rules [Continuous.div, Continuous.mul, continuous_const, Continuous.arsinh,
        Continuous.dist, continuous_coe.comp, continuous_fst, continuous_snd,
        Real.continuous_sqrt.comp, continuous_im.comp]
    · letI : MetricSpace ℍ := metricSpaceAux
      refine le_of_nhds_le_nhds fun z => ?_
      rw [nhds_induced]
      refine (nhds_basis_ball.le_basis_iff (nhds_basis_ball.comap _)).2 fun R hR => ?_
      have h₁ : 1 < R / im z + 1 := lt_add_of_pos_left _ (div_pos hR z.im_pos)
      have h₀ : 0 < R / im z + 1 := one_pos.trans h₁
      refine ⟨log (R / im z + 1), Real.log_pos h₁, ?_⟩
      refine fun w hw => (dist_coe_le w z).trans_lt ?_
      rwa [← lt_div_iff₀' z.im_pos, sub_lt_iff_lt_add, ← Real.lt_log_iff_exp_lt h₀]

theorem im_pos_of_dist_center_le {z : ℍ} {r : ℝ} {w : ℂ}
    (h : dist w (center z r) ≤ z.im * Real.sinh r) : 0 < w.im :=
  calc
    0 < z.im * (Real.cosh r - Real.sinh r) := mul_pos z.im_pos (sub_pos.2 <| sinh_lt_cosh _)
    _ = (z.center r).im - z.im * Real.sinh r := mul_sub _ _ _
    _ ≤ (z.center r).im - dist (z.center r : ℂ) w := sub_le_sub_left (by rwa [dist_comm]) _
    _ ≤ w.im := sub_le_comm.1 <| (le_abs_self _).trans (abs_im_le_norm <| z.center r - w)

theorem image_coe_closedBall (z : ℍ) (r : ℝ) :
    ((↑) : ℍ → ℂ) '' closedBall (α := ℍ) z r = closedBall ↑(z.center r) (z.im * Real.sinh r) := by
  ext w; constructor
  · rintro ⟨w, hw, rfl⟩
    exact dist_le_iff_dist_coe_center_le.1 hw
  · intro hw
    lift w to ℍ using im_pos_of_dist_center_le hw
    exact mem_image_of_mem _ (dist_le_iff_dist_coe_center_le.2 hw)

theorem image_coe_ball (z : ℍ) (r : ℝ) :
    ((↑) : ℍ → ℂ) '' ball (α := ℍ) z r = ball ↑(z.center r) (z.im * Real.sinh r) := by
  ext w; constructor
  · rintro ⟨w, hw, rfl⟩
    exact dist_lt_iff_dist_coe_center_lt.1 hw
  · intro hw
    lift w to ℍ using im_pos_of_dist_center_le (ball_subset_closedBall hw)
    exact mem_image_of_mem _ (dist_lt_iff_dist_coe_center_lt.2 hw)

theorem image_coe_sphere (z : ℍ) (r : ℝ) :
    ((↑) : ℍ → ℂ) '' sphere (α := ℍ) z r = sphere ↑(z.center r) (z.im * Real.sinh r) := by
  ext w; constructor
  · rintro ⟨w, hw, rfl⟩
    exact dist_eq_iff_dist_coe_center_eq.1 hw
  · intro hw
    lift w to ℍ using im_pos_of_dist_center_le (sphere_subset_closedBall hw)
    exact mem_image_of_mem _ (dist_eq_iff_dist_coe_center_eq.2 hw)

instance : ProperSpace ℍ := by
  refine ⟨fun z r => ?_⟩
  rw [IsInducing.subtypeVal.isCompact_iff (f := ((↑) : ℍ → ℂ)), image_coe_closedBall]
  apply isCompact_closedBall

theorem isometry_vertical_line (a : ℝ) : Isometry fun y => mk ⟨a, exp y⟩ (exp_pos y) := by
  refine Isometry.of_dist_eq fun y₁ y₂ => ?_
  rw [dist_of_re_eq]
  exacts [congr_arg₂ _ (log_exp _) (log_exp _), rfl]

theorem isometry_real_vadd (a : ℝ) : Isometry (a +ᵥ · : ℍ → ℍ) :=
  Isometry.of_dist_eq fun y₁ y₂ => by simp only [dist_eq, coe_vadd, vadd_im, dist_add_left]

theorem isometry_pos_mul (a : { x : ℝ // 0 < x }) : Isometry (a • · : ℍ → ℍ) := by
  refine Isometry.of_dist_eq fun y₁ y₂ => ?_
  simp only [dist_eq, coe_pos_real_smul, pos_real_im]; congr 2
  rw [dist_smul₀, mul_mul_mul_comm, Real.sqrt_mul (mul_self_nonneg _), Real.sqrt_mul_self_eq_abs,
    Real.norm_eq_abs, mul_left_comm]
  exact mul_div_mul_left _ _ (mt _root_.abs_eq_zero.1 a.2.ne')

/-- `SL(2, ℝ)` acts on the upper half plane as an isometry. -/
instance : IsIsometricSMul SL(2, ℝ) ℍ :=
  ⟨fun g => by
    have h₀ : Isometry (fun z => ModularGroup.S • z : ℍ → ℍ) :=
      Isometry.of_dist_eq fun y₁ y₂ => by
        have h₁ : 0 ≤ im y₁ * im y₂ := mul_nonneg y₁.property.le y₂.property.le
        have h₂ : ‖(y₁ * y₂ : ℂ)‖ ≠ 0 := by simp [y₁.ne_zero, y₂.ne_zero]
        simp_rw [modular_S_smul, inv_neg, dist_eq, coe_mk, dist_neg_neg,
          dist_inv_inv₀ y₁.ne_zero y₂.ne_zero, mk_im, neg_im, inv_im, coe_im, neg_div, neg_neg,
          div_mul_div_comm, ← normSq_mul, Real.sqrt_div h₁, ← norm_def, mul_div (2 : ℝ)]
        rw [div_div_div_comm, ← norm_mul, div_self h₂, div_one]
    by_cases hc : g 1 0 = 0
    · obtain ⟨u, v, h⟩ := exists_SL2_smul_eq_of_apply_zero_one_eq_zero g hc
      rw [h]
      exact (isometry_real_vadd v).comp (isometry_pos_mul u)
    · obtain ⟨u, v, w, h⟩ := exists_SL2_smul_eq_of_apply_zero_one_ne_zero g hc
      rw [h]
      exact
        (isometry_real_vadd w).comp (h₀.comp <| (isometry_real_vadd v).comp <| isometry_pos_mul u)⟩

end UpperHalfPlane
