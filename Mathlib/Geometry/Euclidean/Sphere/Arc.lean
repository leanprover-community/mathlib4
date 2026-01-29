/-
Copyright (c) 2026 Li Jiale. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Jiale
-/
module

public import Mathlib.Geometry.Euclidean.Angle.Sphere
public import Mathlib.Geometry.Euclidean.Sphere.Basic
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine

/-!
# Arcs on Spheres

This file defines arcs on spheres (circles in 2D, great circle arcs in higher dimensions)
and proves basic properties.

## Main definitions

* `EuclideanGeometry.Sphere.Arc`: An arc on a sphere, defined by the sphere and two endpoints.
* `EuclideanGeometry.Sphere.Arc.centerAngle`: The central angle of an arc.
* `EuclideanGeometry.Sphere.Arc.minorSet`: The set of points on the minor arc.
* `EuclideanGeometry.Sphere.Arc.majorSet`: The set of points on the major arc.

-/

open scoped EuclideanGeometry RealInnerProductSpace

variable {V : Type*} {Pt : Type*} [NormedAddCommGroup V] [MetricSpace Pt]
  [NormedAddTorsor V Pt]

noncomputable section

namespace EuclideanGeometry

namespace Sphere

public section

/-- An arc on a sphere, defined by the sphere and two distinct endpoints on the sphere. -/
structure Arc (Pt : Type*) [MetricSpace Pt] where
  /-- The underlying sphere containing the arc. -/
  sphere : Sphere Pt
  /-- The left endpoint of the arc. -/
  left : Pt
  /-- The right endpoint of the arc. -/
  right : Pt
  /-- Proof that the left endpoint lies on the sphere. -/
  left_mem : left ∈ sphere
  /-- Proof that the right endpoint lies on the sphere. -/
  right_mem : right ∈ sphere
  /-- Proof that the two endpoints are distinct. -/
  left_ne_right : left ≠ right

namespace Arc

variable (a : Arc Pt)

/-- The center of the sphere containing the arc. -/
abbrev center : Pt := a.sphere.center

lemma radius_pos : 0 < a.sphere.radius := by
  by_contra h
  push_neg at h
  have hl : dist a.left a.center = a.sphere.radius := a.left_mem
  have hr : dist a.right a.center = a.sphere.radius := a.right_mem
  have hl0 : a.left = a.center :=
    dist_eq_zero.mp (by linarith [dist_nonneg (α := Pt) (x := a.left) (y := a.center)])
  have hr0 : a.right = a.center :=
    dist_eq_zero.mp (by linarith [dist_nonneg (α := Pt) (x := a.right) (y := a.center)])
  exact a.left_ne_right (hl0.trans hr0.symm)

lemma left_ne_center : a.left ≠ a.center := by
  intro h
  have : dist a.left a.center = a.sphere.radius := a.left_mem
  rw [h, dist_self] at this
  linarith [a.radius_pos]

lemma right_ne_center : a.right ≠ a.center := by
  intro h
  have : dist a.right a.center = a.sphere.radius := a.right_mem
  rw [h, dist_self] at this
  linarith [a.radius_pos]

lemma left_vsub_center_ne_zero : a.left -ᵥ a.center ≠ 0 := by
  rw [vsub_ne_zero]
  exact a.left_ne_center

lemma right_vsub_center_ne_zero : a.right -ᵥ a.center ≠ 0 := by
  rw [vsub_ne_zero]
  exact a.right_ne_center

variable [InnerProductSpace ℝ V]

/-- The central angle of the arc, i.e., the angle at the center between the two endpoints.
This is an unoriented angle with values in `[0, π]`. -/
def centerAngle : ℝ :=
  InnerProductGeometry.angle (a.left -ᵥ a.center) (a.right -ᵥ a.center)

/-- An arc is a minor arc if its central angle is strictly less than `π`. -/
def IsMinor : Prop := a.centerAngle < Real.pi

/-- An arc is a semicircle if its central angle equals `π`. -/
def IsSemicircle : Prop := a.centerAngle = Real.pi

/-- An arc is nondegenerate if its central angle is positive. -/
def IsNondegenerate : Prop := a.centerAngle > 0

/-- The set of points on the minor arc. A point `P` is on the minor arc if it lies on the
sphere and satisfies the angle addition condition `∠(left, center, P) + ∠(P, center, right) =
∠(left, center, right)`. This definition includes the condition `centerAngle < π` to avoid
degeneracy in the semicircle case. -/
def minorSet : Set Pt :=
  { P | P ∈ a.sphere ∧
        a.centerAngle < Real.pi ∧
        InnerProductGeometry.angle (a.left -ᵥ a.center) (P -ᵥ a.center) +
        InnerProductGeometry.angle (P -ᵥ a.center) (a.right -ᵥ a.center) =
        a.centerAngle }

/-- The set of points on the major arc. This is defined as the complement of the interior
of the minor arc within the sphere, preserving the endpoints. -/
def majorSet : Set Pt :=
  (a.sphere : Set Pt) \ (a.minorSet \ {a.left, a.right})

/-- The reverse of an arc, with endpoints swapped. -/
def reverse : Arc Pt :=
  ⟨a.sphere, a.right, a.left, a.right_mem, a.left_mem, a.left_ne_right.symm⟩

lemma centerAngle_nonneg : 0 ≤ a.centerAngle :=
  InnerProductGeometry.angle_nonneg _ _

lemma centerAngle_le_pi : a.centerAngle ≤ Real.pi :=
  InnerProductGeometry.angle_le_pi _ _

@[simp]
lemma reverse_centerAngle : a.reverse.centerAngle = a.centerAngle := by
  simp only [reverse, centerAngle]
  exact InnerProductGeometry.angle_comm _ _

lemma left_mem_minorSet (h : a.IsMinor) : a.left ∈ a.minorSet := by
  refine ⟨a.left_mem, h, ?_⟩
  rw [InnerProductGeometry.angle_self a.left_vsub_center_ne_zero, zero_add]
  exact Real.ext_cauchy rfl

lemma right_mem_minorSet (h : a.IsMinor) : a.right ∈ a.minorSet := by
  refine ⟨a.right_mem, h, ?_⟩
  rw [InnerProductGeometry.angle_self a.right_vsub_center_ne_zero, add_zero]
  exact Real.ext_cauchy rfl

lemma left_mem_majorSet : a.left ∈ a.majorSet := by
  simp only [majorSet, Set.mem_diff]
  exact ⟨a.left_mem, fun ⟨_, hne⟩ => by simp at hne⟩

lemma right_mem_majorSet : a.right ∈ a.majorSet := by
  simp only [majorSet, Set.mem_diff]
  exact ⟨a.right_mem, fun ⟨_, hne⟩ => by simp at hne⟩

lemma minorSet_empty_of_isSemicircle (h : a.IsSemicircle) : a.minorSet = ∅ := by
  ext P
  simp only [minorSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro _ hlt
  rw [IsSemicircle] at h
  linarith

lemma majorSet_eq_sphere_of_isSemicircle (h : a.IsSemicircle) : a.majorSet = a.sphere := by
  simp only [majorSet, a.minorSet_empty_of_isSemicircle h, Set.empty_diff, Set.diff_empty]

end Arc

end

end Sphere

end EuclideanGeometry
