/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov

! This file was ported from Lean 3 source module geometry.euclidean.inversion
! leanprover-community/mathlib commit 46b633fd842bef9469441c0209906f6dddd2b4f5
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Euclidean.PerpBisector

/-!
# Inversion in an affine space

In this file we define inversion in a sphere in an affine space. This map sends each point `x` to
the point `y` such that `y -ᵥ c = (R / dist x c) ^ 2 • (x -ᵥ c)`, where `c` and `R` are the center
and the radius the sphere.

In many applications, it is convenient to assume that the inversions swaps the center and the point
at infinity. In order to stay in the original affine space, we define the map so that it sends
center to itself.

Currently, we prove only a few basic lemmas needed to prove Ptolemy's inequality, see
`EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist`.
-/

noncomputable section

open Metric Real Function AffineMap Set AffineSubspace

namespace EuclideanGeometry

variable {V P : Type _} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] {a b c d x y z : P} {r R : ℝ}

/-- Inversion in a sphere in an affine space. This map sends each point `x` to the point `y` such
that `y -ᵥ c = (R / dist x c) ^ 2 • (x -ᵥ c)`, where `c` and `R` are the center and the radius the
sphere. -/
def inversion (c : P) (R : ℝ) (x : P) : P :=
  (R / dist x c) ^ 2 • (x -ᵥ c) +ᵥ c
#align euclidean_geometry.inversion EuclideanGeometry.inversion

/-!
### Basic properties

In this section we prove that `EuclideanGeometry.inversion c R` is involutive and preserves the
sphere `Metric.sphere c R`. We also prove that the distance to the center of the image of `x` under
this inversion is given by `R ^ 2 / dist x c`.
-/

theorem inversion_eq_lineMap (c : P) (R : ℝ) (x : P) :
    inversion c R x = lineMap c x ((R / dist x c) ^ 2) :=
  rfl

theorem inversion_vsub_center (c : P) (R : ℝ) (x : P) :
    inversion c R x -ᵥ c = (R / dist x c) ^ 2 • (x -ᵥ c) :=
  vadd_vsub _ _
#align euclidean_geometry.inversion_vsub_center EuclideanGeometry.inversion_vsub_center

@[simp]
theorem inversion_self (c : P) (R : ℝ) : inversion c R c = c := by simp [inversion]
#align euclidean_geometry.inversion_self EuclideanGeometry.inversion_self

@[simp]
theorem inversion_zero_radius (c x : P) : inversion c 0 x = c := by simp [inversion]

@[simp]
theorem inversion_dist_center (c x : P) : inversion c (dist x c) x = x := by
  rcases eq_or_ne x c with (rfl | hne)
  · apply inversion_self
  · rw [inversion, div_self, one_pow, one_smul, vsub_vadd]
    rwa [dist_ne_zero]
#align euclidean_geometry.inversion_dist_center EuclideanGeometry.inversion_dist_center

theorem inversion_of_mem_sphere (h : x ∈ Metric.sphere c R) : inversion c R x = x :=
  h.out ▸ inversion_dist_center c x
#align euclidean_geometry.inversion_of_mem_sphere EuclideanGeometry.inversion_of_mem_sphere

/-- Distance from the image of a point under inversion to the center. This formula accidentally
works for `x = c`. -/
theorem dist_inversion_center (c x : P) (R : ℝ) : dist (inversion c R x) c = R ^ 2 / dist x c := by
  rcases eq_or_ne x c with (rfl | hx)
  · simp
  have : dist x c ≠ 0 := dist_ne_zero.2 hx
  field_simp [inversion, norm_smul, abs_div, ← dist_eq_norm_vsub, sq, mul_assoc]
#align euclidean_geometry.dist_inversion_center EuclideanGeometry.dist_inversion_center

/-- Distance from the center of an inversion to the image of a point under the inversion. This
formula accidentally works for `x = c`. -/
theorem dist_center_inversion (c x : P) (R : ℝ) : dist c (inversion c R x) = R ^ 2 / dist c x := by
  rw [dist_comm c, dist_comm c, dist_inversion_center]
#align euclidean_geometry.dist_center_inversion EuclideanGeometry.dist_center_inversion

@[simp]
theorem inversion_inversion (c : P) {R : ℝ} (hR : R ≠ 0) (x : P) :
    inversion c R (inversion c R x) = x := by
  rcases eq_or_ne x c with (rfl | hne)
  · rw [inversion_self, inversion_self]
  · rw [inversion, dist_inversion_center, inversion_vsub_center, smul_smul, ← mul_pow,
      div_mul_div_comm, div_mul_cancel _ (dist_ne_zero.2 hne), ← sq, div_self, one_pow, one_smul,
      vsub_vadd]
    exact pow_ne_zero _ hR
#align euclidean_geometry.inversion_inversion EuclideanGeometry.inversion_inversion

theorem inversion_involutive (c : P) {R : ℝ} (hR : R ≠ 0) : Involutive (inversion c R) :=
  inversion_inversion c hR
#align euclidean_geometry.inversion_involutive EuclideanGeometry.inversion_involutive

theorem inversion_surjective (c : P) {R : ℝ} (hR : R ≠ 0) : Surjective (inversion c R) :=
  (inversion_involutive c hR).surjective
#align euclidean_geometry.inversion_surjective EuclideanGeometry.inversion_surjective

theorem inversion_injective (c : P) {R : ℝ} (hR : R ≠ 0) : Injective (inversion c R) :=
  (inversion_involutive c hR).injective
#align euclidean_geometry.inversion_injective EuclideanGeometry.inversion_injective

theorem inversion_bijective (c : P) {R : ℝ} (hR : R ≠ 0) : Bijective (inversion c R) :=
  (inversion_involutive c hR).bijective
#align euclidean_geometry.inversion_bijective EuclideanGeometry.inversion_bijective

theorem inversion_eq_center (hR : R ≠ 0) : inversion c R x = c ↔ x = c :=
  (inversion_injective c hR).eq_iff' <| inversion_self _ _

@[simp]
theorem inversion_eq_center' : inversion c R x = c ↔ x = c ∨ R = 0 := by
  by_cases hR : R = 0 <;> simp [inversion_eq_center, hR]

theorem center_eq_inversion (hR : R ≠ 0) : c = inversion c R x ↔ x = c :=
  eq_comm.trans (inversion_eq_center hR)

@[simp]
theorem center_eq_inversion' : c = inversion c R x ↔ x = c ∨ R = 0 :=
  eq_comm.trans inversion_eq_center'

/-!
### Similarity of triangles

If inversion with center `O` sends `A` to `A'` and `B` to `B'`, then the triangle `OB'A'` is similar
to the triangle `OAB` with coefficient `R ^ 2 / (|OA|*|OB|)` and the triangle `OA'B` is similar to
the triangle `OAB'` with coefficient `|OB|/|OA|`. We formulate these statements in terms of ratios
of the lengths of their sides.
-/

/-- Distance between the images of two points under an inversion. -/
theorem dist_inversion_inversion (hx : x ≠ c) (hy : y ≠ c) (R : ℝ) :
    dist (inversion c R x) (inversion c R y) = R ^ 2 / (dist x c * dist y c) * dist x y := by
  dsimp only [inversion]
  simp_rw [dist_vadd_cancel_right, dist_eq_norm_vsub V _ c]
  simpa only [dist_vsub_cancel_right] using
    dist_div_norm_sq_smul (vsub_ne_zero.2 hx) (vsub_ne_zero.2 hy) R
#align euclidean_geometry.dist_inversion_inversion EuclideanGeometry.dist_inversion_inversion

theorem dist_inversion_mul_dist_center_eq (hx : x ≠ c) (hy : y ≠ c) :
    dist (inversion c R x) y * dist x c = dist x (inversion c R y) * dist y c := by
  rcases eq_or_ne R 0 with rfl | hR; · simp [dist_comm, mul_comm]
  have hy' : inversion c R y ≠ c := by simp [*]
  conv in dist _ y => rw [← inversion_inversion c hR y]
  rw [dist_inversion_inversion hx hy', dist_inversion_center]
  have : dist x c ≠ 0 := dist_ne_zero.2 hx
  field_simp; ring

/-!
### Ptolemy's inequality
-/

/-- **Ptolemy's inequality**: in a quadrangle `ABCD`, `|AC| * |BD| ≤ |AB| * |CD| + |BC| * |AD|`. If
`ABCD` is a convex cyclic polygon, then this inequality becomes an equality, see
`EuclideanGeometry.mul_dist_add_mul_dist_eq_mul_dist_of_cospherical`. -/
theorem mul_dist_le_mul_dist_add_mul_dist (a b c d : P) :
    dist a c * dist b d ≤ dist a b * dist c d + dist b c * dist a d := by
  -- If one of the points `b`, `c`, `d` is equal to `a`, then the inequality is trivial.
  rcases eq_or_ne b a with (rfl | hb)
  · rw [dist_self, MulZeroClass.zero_mul, zero_add]
  rcases eq_or_ne c a with (rfl | hc)
  · rw [dist_self, MulZeroClass.zero_mul]
    apply_rules [add_nonneg, mul_nonneg, dist_nonneg]
  rcases eq_or_ne d a with (rfl | hd)
  · rw [dist_self, MulZeroClass.mul_zero, add_zero, dist_comm d, dist_comm d, mul_comm]
  /- Otherwise, we apply the triangle inequality to `EuclideanGeometry.inversion a 1 b`,
    `EuclideanGeometry.inversion a 1 c`, and `EuclideanGeometry.inversion a 1 d`. -/
  have H := dist_triangle (inversion a 1 b) (inversion a 1 c) (inversion a 1 d)
  rw [dist_inversion_inversion hb hd, dist_inversion_inversion hb hc,
    dist_inversion_inversion hc hd, one_pow] at H
  rw [← dist_pos] at hb hc hd
  rw [← div_le_div_right (mul_pos hb (mul_pos hc hd))]
  convert H using 1 <;> (field_simp [hb.ne', hc.ne', hd.ne', dist_comm a]; ring)
#align euclidean_geometry.mul_dist_le_mul_dist_add_mul_dist EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist

/-!
### Images of spheres and hyperplanes

In this section we prove that the inversion with center `c` and radius `R ≠ 0` maps a sphere passing
through the center to a hyperplane. More precisely, it maps a sphere with center `y ≠ c` and radius
`dist y c` to the hyperplane `AffineSubspace.perpBisector c (EuclideanGeometry.inversion c R y)`.

-/

/-- The inversion with center `c` and radius `R` maps a sphere passing through the center to a
hyperplane. -/
theorem inversion_mem_perpBisector_inversion_iff (hR : R ≠ 0) (hx : x ≠ c) (hy : y ≠ c) :
    inversion c R x ∈ perpBisector c (inversion c R y) ↔ dist x y = dist y c := by
  rw [mem_perpBisector_iff_dist_eq, dist_inversion_inversion hx hy, dist_inversion_center]
  have hx' := dist_ne_zero.2 hx
  have hy' := dist_ne_zero.2 hy
  field_simp [mul_assoc, mul_comm, hx, hx.symm, eq_comm]

/-- The inversion with center `c` and radius `R` maps a sphere passing through the center to a
hyperplane. -/
theorem inversion_mem_perpBisector_inversion_iff' (hR : R ≠ 0) (hy : y ≠ c) :
    inversion c R x ∈ perpBisector c (inversion c R y) ↔ dist x y = dist y c ∧ x ≠ c := by
  rcases eq_or_ne x c with rfl | hx
  · simp [*]
  · simp [inversion_mem_perpBisector_inversion_iff hR hx hy, hx]

theorem preimage_inversion_perpBisector (hR : R ≠ 0) (hy : y ≠ c) :
    inversion c R ⁻¹' perpBisector c y = sphere (inversion c R y) (R ^ 2 / dist y c) \ {c} := by
  ext x
  nth_rewrite 1 [← inversion_inversion c hR y]
  rw [← dist_inversion_center, mem_preimage, SetLike.mem_coe,
    inversion_mem_perpBisector_inversion_iff' hR, mem_diff, mem_sphere, mem_singleton_iff]
  simp [*]

theorem image_inversion_perpBisector (hR : R ≠ 0) (hy : y ≠ c) :
    inversion c R '' perpBisector c y = sphere (inversion c R y) (R ^ 2 / dist y c) \ {c} := by
  rw [image_eq_preimage_of_inverse (inversion_involutive _ hR) (inversion_involutive _ hR),
    preimage_inversion_perpBisector hR hy]

theorem preimage_inversion_sphere_dist_center (hR : R ≠ 0) (hy : y ≠ c) :
    inversion c R ⁻¹' sphere y (dist y c) =
      insert c (perpBisector c (inversion c R y) : Set P) := by
  ext x
  rcases eq_or_ne x c with rfl | hx; · simp [dist_comm]
  rw [mem_preimage, mem_sphere, ← inversion_mem_perpBisector_inversion_iff hR] <;> simp [*]

theorem image_inversion_sphere_dist_center (hR : R ≠ 0) (hy : y ≠ c) :
    inversion c R '' sphere y (dist y c) = insert c (perpBisector c (inversion c R y) : Set P) := by
  rw [image_eq_preimage_of_inverse (inversion_involutive _ hR) (inversion_involutive _ hR),
    preimage_inversion_sphere_dist_center hR hy]

end EuclideanGeometry
