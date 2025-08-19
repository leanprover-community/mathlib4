/-
Copyright (c) 2021 Manuel Candales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Candales, Benjamin Davidson
-/
import Mathlib.Geometry.Euclidean.Sphere.Power
import Mathlib.Geometry.Euclidean.Triangle

/-!
# Ptolemy's theorem

This file proves Ptolemy's theorem on the lengths of the diagonals and sides of a cyclic
quadrilateral.

## Main theorems

* `mul_dist_add_mul_dist_eq_mul_dist_of_cospherical`: Ptolemy’s Theorem (Freek No. 95).

TODO: The current statement of Ptolemy’s theorem works around the lack of a "cyclic polygon" concept
in mathlib, which is what the theorem statement would naturally use (or two such concepts, since
both a strict version, where all vertices must be distinct, and a weak version, where consecutive
vertices may be equal, would be useful; Ptolemy's theorem should then use the weak one).

An API needs to be built around that concept, which would include:
- strict cyclic implies weak cyclic,
- weak cyclic and consecutive points distinct implies strict cyclic,
- weak/strict cyclic implies weak/strict cyclic for any subsequence,
- any three points on a sphere are weakly or strictly cyclic according to whether they are distinct,
- any number of points on a sphere intersected with a two-dimensional affine subspace are cyclic in
  some order,
- a list of points is cyclic if and only if its reversal is,
- a list of points is cyclic if and only if any cyclic permutation is, while other permutations
  are not when the points are distinct,
- a point P where the diagonals of a cyclic polygon cross exists (and is unique) with weak/strict
  betweenness depending on weak/strict cyclicity,
- four points on a sphere with such a point P are cyclic in the appropriate order,
and so on.
-/


open Real

open scoped EuclideanGeometry RealInnerProductSpace Real

namespace EuclideanGeometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {P : Type*} [MetricSpace P] [NormedAddTorsor V P]

/-- **Ptolemy’s Theorem**. -/
theorem mul_dist_add_mul_dist_eq_mul_dist_of_cospherical {a b c d p : P}
    (h : Cospherical ({a, b, c, d} : Set P)) (hapc : ∠ a p c = π) (hbpd : ∠ b p d = π) :
    dist a b * dist c d + dist b c * dist d a = dist a c * dist b d := by
  have h' : Cospherical ({a, c, b, d} : Set P) := by rwa [Set.insert_comm c b {d}]
  have hmul := mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi h' hapc hbpd
  have hbp := left_dist_ne_zero_of_angle_eq_pi hbpd
  have h₁ : dist c d = dist c p / dist b p * dist a b := by
    rw [dist_mul_of_eq_angle_of_dist_mul b p a c p d, dist_comm a b]
    · rw [angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi hbpd hapc, angle_comm]
    all_goals simp [field, mul_comm, hmul]
  have h₂ : dist d a = dist a p / dist b p * dist b c := by
    rw [dist_mul_of_eq_angle_of_dist_mul c p b d p a, dist_comm c b]
    · rwa [angle_comm, angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi]; rwa [angle_comm]
    all_goals simp [field, mul_comm, hmul]
  have h₃ : dist d p = dist a p * dist c p / dist b p := by simp [field, hmul]
  have h₄ : ∀ x y : ℝ, x * (y * x) = x * x * y := fun x y => by rw [mul_left_comm, mul_comm]
  -- takes 450ms, but the "equivalent" simp call leaves some remaining goals
  simp [field, h₁, h₂, dist_eq_add_dist_of_angle_eq_pi hbpd, h₃, dist_comm a b, h₄, ← sq,
    dist_sq_mul_dist_add_dist_sq_mul_dist b, hapc]

end EuclideanGeometry
