/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Manuel Candales
-/
import Mathlib.Analysis.Convex.Between
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

#align_import geometry.euclidean.angle.unoriented.affine from "leanprover-community/mathlib"@"46b633fd842bef9469441c0209906f6dddd2b4f5"

/-!
# Angles between points

This file defines unoriented angles in Euclidean affine spaces.

## Main definitions

* `EuclideanGeometry.angle`, with notation `∠`, is the undirected angle determined by three
  points.

-/


noncomputable section

open BigOperators Real RealInnerProductSpace

namespace EuclideanGeometry

open InnerProductGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- The undirected angle at `p2` between the line segments to `p1` and
`p3`. If either of those points equals `p2`, this is π/2. Use
`open scoped EuclideanGeometry` to access the `∠ p1 p2 p3`
notation. -/
nonrec def angle (p1 p2 p3 : P) : ℝ :=
  angle (p1 -ᵥ p2 : V) (p3 -ᵥ p2)
#align euclidean_geometry.angle EuclideanGeometry.angle

scoped notation "∠" => EuclideanGeometry.angle

theorem continuousAt_angle {x : P × P × P} (hx12 : x.1 ≠ x.2.1) (hx32 : x.2.2 ≠ x.2.1) :
    ContinuousAt (fun y : P × P × P => ∠ y.1 y.2.1 y.2.2) x := by
  let f : P × P × P → V × V := fun y => (y.1 -ᵥ y.2.1, y.2.2 -ᵥ y.2.1)
  -- ⊢ ContinuousAt (fun y => ∠ y.fst y.snd.fst y.snd.snd) x
  have hf1 : (f x).1 ≠ 0 := by simp [hx12]
  -- ⊢ ContinuousAt (fun y => ∠ y.fst y.snd.fst y.snd.snd) x
  have hf2 : (f x).2 ≠ 0 := by simp [hx32]
  -- ⊢ ContinuousAt (fun y => ∠ y.fst y.snd.fst y.snd.snd) x
  exact (InnerProductGeometry.continuousAt_angle hf1 hf2).comp
    ((continuous_fst.vsub continuous_snd.fst).prod_mk
      (continuous_snd.snd.vsub continuous_snd.fst)).continuousAt
#align euclidean_geometry.continuous_at_angle EuclideanGeometry.continuousAt_angle

@[simp]
theorem _root_.AffineIsometry.angle_map {V₂ P₂ : Type*} [NormedAddCommGroup V₂]
    [InnerProductSpace ℝ V₂] [MetricSpace P₂] [NormedAddTorsor V₂ P₂]
    (f : P →ᵃⁱ[ℝ] P₂) (p₁ p₂ p₃ : P) : ∠ (f p₁) (f p₂) (f p₃) = ∠ p₁ p₂ p₃ := by
  simp_rw [angle, ← AffineIsometry.map_vsub, LinearIsometry.angle_map]
  -- 🎉 no goals
#align affine_isometry.angle_map AffineIsometry.angle_map

@[simp, norm_cast]
theorem _root_.AffineSubspace.angle_coe {s : AffineSubspace ℝ P} (p₁ p₂ p₃ : s) :
    haveI : Nonempty s := ⟨p₁⟩
    ∠ (p₁ : P) (p₂ : P) (p₃ : P) = ∠ p₁ p₂ p₃ :=
  haveI : Nonempty s := ⟨p₁⟩
  s.subtypeₐᵢ.angle_map p₁ p₂ p₃
#align affine_subspace.angle_coe AffineSubspace.angle_coe

/-- Angles are translation invariant -/
@[simp]
theorem angle_const_vadd (v : V) (p₁ p₂ p₃ : P) : ∠ (v +ᵥ p₁) (v +ᵥ p₂) (v +ᵥ p₃) = ∠ p₁ p₂ p₃ :=
  (AffineIsometryEquiv.constVAdd ℝ P v).toAffineIsometry.angle_map _ _ _
#align euclidean_geometry.angle_const_vadd EuclideanGeometry.angle_const_vadd

/-- Angles are translation invariant -/
@[simp]
theorem angle_vadd_const (v₁ v₂ v₃ : V) (p : P) : ∠ (v₁ +ᵥ p) (v₂ +ᵥ p) (v₃ +ᵥ p) = ∠ v₁ v₂ v₃ :=
  (AffineIsometryEquiv.vaddConst ℝ p).toAffineIsometry.angle_map _ _ _
#align euclidean_geometry.angle_vadd_const EuclideanGeometry.angle_vadd_const

/-- Angles are translation invariant -/
@[simp]
theorem angle_const_vsub (p p₁ p₂ p₃ : P) : ∠ (p -ᵥ p₁) (p -ᵥ p₂) (p -ᵥ p₃) = ∠ p₁ p₂ p₃ :=
  (AffineIsometryEquiv.constVSub ℝ p).toAffineIsometry.angle_map _ _ _
#align euclidean_geometry.angle_const_vsub EuclideanGeometry.angle_const_vsub

/-- Angles are translation invariant -/
@[simp]
theorem angle_vsub_const (p₁ p₂ p₃ p : P) : ∠ (p₁ -ᵥ p) (p₂ -ᵥ p) (p₃ -ᵥ p) = ∠ p₁ p₂ p₃ :=
  (AffineIsometryEquiv.vaddConst ℝ p).symm.toAffineIsometry.angle_map _ _ _
#align euclidean_geometry.angle_vsub_const EuclideanGeometry.angle_vsub_const

/-- Angles in a vector space are translation invariant -/
@[simp]
theorem angle_add_const (v₁ v₂ v₃ : V) (v : V) : ∠ (v₁ + v) (v₂ + v) (v₃ + v) = ∠ v₁ v₂ v₃ :=
  angle_vadd_const _ _ _ _
#align euclidean_geometry.angle_add_const EuclideanGeometry.angle_add_const

/-- Angles in a vector space are translation invariant -/
@[simp]
theorem angle_const_add (v : V) (v₁ v₂ v₃ : V) : ∠ (v + v₁) (v + v₂) (v + v₃) = ∠ v₁ v₂ v₃ :=
  angle_const_vadd _ _ _ _
#align euclidean_geometry.angle_const_add EuclideanGeometry.angle_const_add

/-- Angles in a vector space are translation invariant -/
@[simp]
theorem angle_sub_const (v₁ v₂ v₃ : V) (v : V) : ∠ (v₁ - v) (v₂ - v) (v₃ - v) = ∠ v₁ v₂ v₃ := by
  simpa only [vsub_eq_sub] using angle_vsub_const v₁ v₂ v₃ v
  -- 🎉 no goals
#align euclidean_geometry.angle_sub_const EuclideanGeometry.angle_sub_const

/-- Angles in a vector space are invariant to inversion -/
@[simp]
theorem angle_const_sub (v : V) (v₁ v₂ v₃ : V) : ∠ (v - v₁) (v - v₂) (v - v₃) = ∠ v₁ v₂ v₃ := by
  simpa only [vsub_eq_sub] using angle_const_vsub v v₁ v₂ v₃
  -- 🎉 no goals
#align euclidean_geometry.angle_const_sub EuclideanGeometry.angle_const_sub

/-- Angles in a vector space are invariant to inversion -/
@[simp]
theorem angle_neg (v₁ v₂ v₃ : V) : ∠ (-v₁) (-v₂) (-v₃) = ∠ v₁ v₂ v₃ := by
  simpa only [zero_sub] using angle_const_sub 0 v₁ v₂ v₃
  -- 🎉 no goals
#align euclidean_geometry.angle_neg EuclideanGeometry.angle_neg

/-- The angle at a point does not depend on the order of the other two
points. -/
nonrec theorem angle_comm (p1 p2 p3 : P) : ∠ p1 p2 p3 = ∠ p3 p2 p1 :=
  angle_comm _ _
#align euclidean_geometry.angle_comm EuclideanGeometry.angle_comm

/-- The angle at a point is nonnegative. -/
nonrec theorem angle_nonneg (p1 p2 p3 : P) : 0 ≤ ∠ p1 p2 p3 :=
  angle_nonneg _ _
#align euclidean_geometry.angle_nonneg EuclideanGeometry.angle_nonneg

/-- The angle at a point is at most π. -/
nonrec theorem angle_le_pi (p1 p2 p3 : P) : ∠ p1 p2 p3 ≤ π :=
  angle_le_pi _ _
#align euclidean_geometry.angle_le_pi EuclideanGeometry.angle_le_pi

/-- The angle ∠AAB at a point. -/
theorem angle_eq_left (p1 p2 : P) : ∠ p1 p1 p2 = π / 2 := by
  unfold angle
  -- ⊢ InnerProductGeometry.angle (p1 -ᵥ p1) (p2 -ᵥ p1) = π / 2
  rw [vsub_self]
  -- ⊢ InnerProductGeometry.angle 0 (p2 -ᵥ p1) = π / 2
  exact angle_zero_left _
  -- 🎉 no goals
#align euclidean_geometry.angle_eq_left EuclideanGeometry.angle_eq_left

/-- The angle ∠ABB at a point. -/
theorem angle_eq_right (p1 p2 : P) : ∠ p1 p2 p2 = π / 2 := by rw [angle_comm, angle_eq_left]
                                                              -- 🎉 no goals
#align euclidean_geometry.angle_eq_right EuclideanGeometry.angle_eq_right

/-- The angle ∠ABA at a point. -/
theorem angle_eq_of_ne {p1 p2 : P} (h : p1 ≠ p2) : ∠ p1 p2 p1 = 0 :=
  angle_self fun he => h (vsub_eq_zero_iff_eq.1 he)
#align euclidean_geometry.angle_eq_of_ne EuclideanGeometry.angle_eq_of_ne

/-- If the angle ∠ABC at a point is π, the angle ∠BAC is 0. -/
theorem angle_eq_zero_of_angle_eq_pi_left {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = π) : ∠ p2 p1 p3 = 0 := by
  unfold angle at h
  -- ⊢ ∠ p2 p1 p3 = 0
  rw [angle_eq_pi_iff] at h
  -- ⊢ ∠ p2 p1 p3 = 0
  rcases h with ⟨hp1p2, ⟨r, ⟨hr, hpr⟩⟩⟩
  -- ⊢ ∠ p2 p1 p3 = 0
  unfold angle
  -- ⊢ InnerProductGeometry.angle (p2 -ᵥ p1) (p3 -ᵥ p1) = 0
  rw [angle_eq_zero_iff]
  -- ⊢ p2 -ᵥ p1 ≠ 0 ∧ ∃ r, 0 < r ∧ p3 -ᵥ p1 = r • (p2 -ᵥ p1)
  rw [← neg_vsub_eq_vsub_rev, neg_ne_zero] at hp1p2
  -- ⊢ p2 -ᵥ p1 ≠ 0 ∧ ∃ r, 0 < r ∧ p3 -ᵥ p1 = r • (p2 -ᵥ p1)
  use hp1p2, -r + 1, add_pos (neg_pos_of_neg hr) zero_lt_one
  -- ⊢ p3 -ᵥ p1 = (-r + 1) • (p2 -ᵥ p1)
  rw [add_smul, ← neg_vsub_eq_vsub_rev p1 p2, smul_neg]
  -- ⊢ p3 -ᵥ p1 = -(-r • (p1 -ᵥ p2)) + 1 • -(p1 -ᵥ p2)
  simp [← hpr]
  -- 🎉 no goals
#align euclidean_geometry.angle_eq_zero_of_angle_eq_pi_left EuclideanGeometry.angle_eq_zero_of_angle_eq_pi_left

/-- If the angle ∠ABC at a point is π, the angle ∠BCA is 0. -/
theorem angle_eq_zero_of_angle_eq_pi_right {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = π) :
    ∠ p2 p3 p1 = 0 := by
  rw [angle_comm] at h
  -- ⊢ ∠ p2 p3 p1 = 0
  exact angle_eq_zero_of_angle_eq_pi_left h
  -- 🎉 no goals
#align euclidean_geometry.angle_eq_zero_of_angle_eq_pi_right EuclideanGeometry.angle_eq_zero_of_angle_eq_pi_right

/-- If ∠BCD = π, then ∠ABC = ∠ABD. -/
theorem angle_eq_angle_of_angle_eq_pi (p1 : P) {p2 p3 p4 : P} (h : ∠ p2 p3 p4 = π) :
    ∠ p1 p2 p3 = ∠ p1 p2 p4 := by
  unfold angle at *
  -- ⊢ InnerProductGeometry.angle (p1 -ᵥ p2) (p3 -ᵥ p2) = InnerProductGeometry.angl …
  rcases angle_eq_pi_iff.1 h with ⟨_, ⟨r, ⟨hr, hpr⟩⟩⟩
  -- ⊢ InnerProductGeometry.angle (p1 -ᵥ p2) (p3 -ᵥ p2) = InnerProductGeometry.angl …
  rw [eq_comm]
  -- ⊢ InnerProductGeometry.angle (p1 -ᵥ p2) (p4 -ᵥ p2) = InnerProductGeometry.angl …
  convert angle_smul_right_of_pos (p1 -ᵥ p2) (p3 -ᵥ p2) (add_pos (neg_pos_of_neg hr) zero_lt_one)
  -- ⊢ p4 -ᵥ p2 = (-r + 1) • (p3 -ᵥ p2)
  rw [add_smul, ← neg_vsub_eq_vsub_rev p2 p3, smul_neg, neg_smul, ← hpr]
  -- ⊢ p4 -ᵥ p2 = - -(p4 -ᵥ p3) + 1 • -(p2 -ᵥ p3)
  simp
  -- 🎉 no goals
#align euclidean_geometry.angle_eq_angle_of_angle_eq_pi EuclideanGeometry.angle_eq_angle_of_angle_eq_pi

/-- If ∠BCD = π, then ∠ACB + ∠ACD = π. -/
nonrec theorem angle_add_angle_eq_pi_of_angle_eq_pi (p1 : P) {p2 p3 p4 : P} (h : ∠ p2 p3 p4 = π) :
    ∠ p1 p3 p2 + ∠ p1 p3 p4 = π := by
  unfold angle at h
  -- ⊢ ∠ p1 p3 p2 + ∠ p1 p3 p4 = π
  rw [angle_comm p1 p3 p2, angle_comm p1 p3 p4]
  -- ⊢ ∠ p2 p3 p1 + ∠ p4 p3 p1 = π
  unfold angle
  -- ⊢ InnerProductGeometry.angle (p2 -ᵥ p3) (p1 -ᵥ p3) + InnerProductGeometry.angl …
  exact angle_add_angle_eq_pi_of_angle_eq_pi _ h
  -- 🎉 no goals
#align euclidean_geometry.angle_add_angle_eq_pi_of_angle_eq_pi EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi

/-- Vertical Angles Theorem: angles opposite each other, formed by two intersecting straight
lines, are equal. -/
theorem angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi {p1 p2 p3 p4 p5 : P} (hapc : ∠ p1 p5 p3 = π)
    (hbpd : ∠ p2 p5 p4 = π) : ∠ p1 p5 p2 = ∠ p3 p5 p4 := by
  linarith [angle_add_angle_eq_pi_of_angle_eq_pi p1 hbpd, angle_comm p4 p5 p1,
    angle_add_angle_eq_pi_of_angle_eq_pi p4 hapc, angle_comm p4 p5 p3]
#align euclidean_geometry.angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi EuclideanGeometry.angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi

/-- If ∠ABC = π then dist A B ≠ 0. -/
theorem left_dist_ne_zero_of_angle_eq_pi {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = π) : dist p1 p2 ≠ 0 := by
  by_contra heq
  -- ⊢ False
  rw [dist_eq_zero] at heq
  -- ⊢ False
  rw [heq, angle_eq_left] at h
  -- ⊢ False
  exact Real.pi_ne_zero (by linarith)
  -- 🎉 no goals
#align euclidean_geometry.left_dist_ne_zero_of_angle_eq_pi EuclideanGeometry.left_dist_ne_zero_of_angle_eq_pi

/-- If ∠ABC = π then dist C B ≠ 0. -/
theorem right_dist_ne_zero_of_angle_eq_pi {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = π) : dist p3 p2 ≠ 0 :=
  left_dist_ne_zero_of_angle_eq_pi <| (angle_comm _ _ _).trans h
#align euclidean_geometry.right_dist_ne_zero_of_angle_eq_pi EuclideanGeometry.right_dist_ne_zero_of_angle_eq_pi

/-- If ∠ABC = π, then (dist A C) = (dist A B) + (dist B C). -/
theorem dist_eq_add_dist_of_angle_eq_pi {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = π) :
    dist p1 p3 = dist p1 p2 + dist p3 p2 := by
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, dist_eq_norm_vsub V, ← vsub_sub_vsub_cancel_right]
  -- ⊢ ‖p1 -ᵥ ?p3 - (p3 -ᵥ ?p3)‖ = ‖p1 -ᵥ p2‖ + ‖p3 -ᵥ p2‖
  exact norm_sub_eq_add_norm_of_angle_eq_pi h
  -- 🎉 no goals
#align euclidean_geometry.dist_eq_add_dist_of_angle_eq_pi EuclideanGeometry.dist_eq_add_dist_of_angle_eq_pi

/-- If A ≠ B and C ≠ B then ∠ABC = π if and only if (dist A C) = (dist A B) + (dist B C). -/
theorem dist_eq_add_dist_iff_angle_eq_pi {p1 p2 p3 : P} (hp1p2 : p1 ≠ p2) (hp3p2 : p3 ≠ p2) :
    dist p1 p3 = dist p1 p2 + dist p3 p2 ↔ ∠ p1 p2 p3 = π := by
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, dist_eq_norm_vsub V, ← vsub_sub_vsub_cancel_right]
  -- ⊢ ‖p1 -ᵥ ?p3 - (p3 -ᵥ ?p3)‖ = ‖p1 -ᵥ p2‖ + ‖p3 -ᵥ p2‖ ↔ ∠ p1 p2 p3 = π
  exact
    norm_sub_eq_add_norm_iff_angle_eq_pi (fun he => hp1p2 (vsub_eq_zero_iff_eq.1 he)) fun he =>
      hp3p2 (vsub_eq_zero_iff_eq.1 he)
#align euclidean_geometry.dist_eq_add_dist_iff_angle_eq_pi EuclideanGeometry.dist_eq_add_dist_iff_angle_eq_pi

/-- If ∠ABC = 0, then (dist A C) = abs ((dist A B) - (dist B C)). -/
theorem dist_eq_abs_sub_dist_of_angle_eq_zero {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = 0) :
    dist p1 p3 = |dist p1 p2 - dist p3 p2| := by
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, dist_eq_norm_vsub V, ← vsub_sub_vsub_cancel_right]
  -- ⊢ ‖p1 -ᵥ ?p3 - (p3 -ᵥ ?p3)‖ = |‖p1 -ᵥ p2‖ - ‖p3 -ᵥ p2‖|
  exact norm_sub_eq_abs_sub_norm_of_angle_eq_zero h
  -- 🎉 no goals
#align euclidean_geometry.dist_eq_abs_sub_dist_of_angle_eq_zero EuclideanGeometry.dist_eq_abs_sub_dist_of_angle_eq_zero

/-- If A ≠ B and C ≠ B then ∠ABC = 0 if and only if (dist A C) = abs ((dist A B) - (dist B C)). -/
theorem dist_eq_abs_sub_dist_iff_angle_eq_zero {p1 p2 p3 : P} (hp1p2 : p1 ≠ p2) (hp3p2 : p3 ≠ p2) :
    dist p1 p3 = |dist p1 p2 - dist p3 p2| ↔ ∠ p1 p2 p3 = 0 := by
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, dist_eq_norm_vsub V, ← vsub_sub_vsub_cancel_right]
  -- ⊢ ‖p1 -ᵥ ?p3 - (p3 -ᵥ ?p3)‖ = |‖p1 -ᵥ p2‖ - ‖p3 -ᵥ p2‖| ↔ ∠ p1 p2 p3 = 0
  exact
    norm_sub_eq_abs_sub_norm_iff_angle_eq_zero (fun he => hp1p2 (vsub_eq_zero_iff_eq.1 he))
      fun he => hp3p2 (vsub_eq_zero_iff_eq.1 he)
#align euclidean_geometry.dist_eq_abs_sub_dist_iff_angle_eq_zero EuclideanGeometry.dist_eq_abs_sub_dist_iff_angle_eq_zero

/-- If M is the midpoint of the segment AB, then ∠AMB = π. -/
theorem angle_midpoint_eq_pi (p1 p2 : P) (hp1p2 : p1 ≠ p2) : ∠ p1 (midpoint ℝ p1 p2) p2 = π := by
  simp [angle, hp1p2, -zero_lt_one]
  -- ⊢ InnerProductGeometry.angle (p1 -ᵥ p2) (p2 -ᵥ p1) = π
  rw [← neg_vsub_eq_vsub_rev p1 p2]
  -- ⊢ InnerProductGeometry.angle (p1 -ᵥ p2) (-(p1 -ᵥ p2)) = π
  apply angle_self_neg_of_nonzero
  -- ⊢ p1 -ᵥ p2 ≠ 0
  simpa only [ne_eq, vsub_eq_zero_iff_eq]
  -- 🎉 no goals
#align euclidean_geometry.angle_midpoint_eq_pi EuclideanGeometry.angle_midpoint_eq_pi

/-- If M is the midpoint of the segment AB and C is the same distance from A as it is from B
then ∠CMA = π / 2. -/
theorem angle_left_midpoint_eq_pi_div_two_of_dist_eq {p1 p2 p3 : P} (h : dist p3 p1 = dist p3 p2) :
    ∠ p3 (midpoint ℝ p1 p2) p1 = π / 2 := by
  let m : P := midpoint ℝ p1 p2
  -- ⊢ ∠ p3 (midpoint ℝ p1 p2) p1 = π / 2
  have h1 : p3 -ᵥ p1 = p3 -ᵥ m - (p1 -ᵥ m) := (vsub_sub_vsub_cancel_right p3 p1 m).symm
  -- ⊢ ∠ p3 (midpoint ℝ p1 p2) p1 = π / 2
  have h2 : p3 -ᵥ p2 = p3 -ᵥ m + (p1 -ᵥ m) := by
    rw [left_vsub_midpoint, ← midpoint_vsub_right, vsub_add_vsub_cancel]
  rw [dist_eq_norm_vsub V p3 p1, dist_eq_norm_vsub V p3 p2, h1, h2] at h
  -- ⊢ ∠ p3 (midpoint ℝ p1 p2) p1 = π / 2
  exact (norm_add_eq_norm_sub_iff_angle_eq_pi_div_two (p3 -ᵥ m) (p1 -ᵥ m)).mp h.symm
  -- 🎉 no goals
#align euclidean_geometry.angle_left_midpoint_eq_pi_div_two_of_dist_eq EuclideanGeometry.angle_left_midpoint_eq_pi_div_two_of_dist_eq

/-- If M is the midpoint of the segment AB and C is the same distance from A as it is from B
then ∠CMB = π / 2. -/
theorem angle_right_midpoint_eq_pi_div_two_of_dist_eq {p1 p2 p3 : P} (h : dist p3 p1 = dist p3 p2) :
    ∠ p3 (midpoint ℝ p1 p2) p2 = π / 2 := by
  rw [midpoint_comm p1 p2, angle_left_midpoint_eq_pi_div_two_of_dist_eq h.symm]
  -- 🎉 no goals
#align euclidean_geometry.angle_right_midpoint_eq_pi_div_two_of_dist_eq EuclideanGeometry.angle_right_midpoint_eq_pi_div_two_of_dist_eq

/-- If the second of three points is strictly between the other two, the angle at that point
is π. -/
theorem _root_.Sbtw.angle₁₂₃_eq_pi {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) : ∠ p₁ p₂ p₃ = π := by
  rw [angle, angle_eq_pi_iff]
  -- ⊢ p₁ -ᵥ p₂ ≠ 0 ∧ ∃ r, r < 0 ∧ p₃ -ᵥ p₂ = r • (p₁ -ᵥ p₂)
  rcases h with ⟨⟨r, ⟨hr0, hr1⟩, hp₂⟩, hp₂p₁, hp₂p₃⟩
  -- ⊢ p₁ -ᵥ p₂ ≠ 0 ∧ ∃ r, r < 0 ∧ p₃ -ᵥ p₂ = r • (p₁ -ᵥ p₂)
  refine' ⟨vsub_ne_zero.2 hp₂p₁.symm, -(1 - r) / r, _⟩
  -- ⊢ -(1 - r) / r < 0 ∧ p₃ -ᵥ p₂ = (-(1 - r) / r) • (p₁ -ᵥ p₂)
  have hr0' : r ≠ 0 := by
    rintro rfl
    rw [← hp₂] at hp₂p₁
    simp at hp₂p₁
  have hr1' : r ≠ 1 := by
    rintro rfl
    rw [← hp₂] at hp₂p₃
    simp at hp₂p₃
  replace hr0 := hr0.lt_of_ne hr0'.symm
  -- ⊢ -(1 - r) / r < 0 ∧ p₃ -ᵥ p₂ = (-(1 - r) / r) • (p₁ -ᵥ p₂)
  replace hr1 := hr1.lt_of_ne hr1'
  -- ⊢ -(1 - r) / r < 0 ∧ p₃ -ᵥ p₂ = (-(1 - r) / r) • (p₁ -ᵥ p₂)
  refine' ⟨div_neg_of_neg_of_pos (Left.neg_neg_iff.2 (sub_pos.2 hr1)) hr0, _⟩
  -- ⊢ p₃ -ᵥ p₂ = (-(1 - r) / r) • (p₁ -ᵥ p₂)
  rw [← hp₂, AffineMap.lineMap_apply, vsub_vadd_eq_vsub_sub, vsub_vadd_eq_vsub_sub, vsub_self,
    zero_sub, smul_neg, smul_smul, div_mul_cancel _ hr0', neg_smul, neg_neg, sub_eq_iff_eq_add, ←
    add_smul, sub_add_cancel, one_smul]
#align sbtw.angle₁₂₃_eq_pi Sbtw.angle₁₂₃_eq_pi

/-- If the second of three points is strictly between the other two, the angle at that point
(reversed) is π. -/
theorem _root_.Sbtw.angle₃₂₁_eq_pi {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) : ∠ p₃ p₂ p₁ = π := by
  rw [← h.angle₁₂₃_eq_pi, angle_comm]
  -- 🎉 no goals
#align sbtw.angle₃₂₁_eq_pi Sbtw.angle₃₂₁_eq_pi

/-- The angle between three points is π if and only if the second point is strictly between the
other two. -/
theorem angle_eq_pi_iff_sbtw {p₁ p₂ p₃ : P} : ∠ p₁ p₂ p₃ = π ↔ Sbtw ℝ p₁ p₂ p₃ := by
  refine' ⟨_, fun h => h.angle₁₂₃_eq_pi⟩
  -- ⊢ ∠ p₁ p₂ p₃ = π → Sbtw ℝ p₁ p₂ p₃
  rw [angle, angle_eq_pi_iff]
  -- ⊢ (p₁ -ᵥ p₂ ≠ 0 ∧ ∃ r, r < 0 ∧ p₃ -ᵥ p₂ = r • (p₁ -ᵥ p₂)) → Sbtw ℝ p₁ p₂ p₃
  rintro ⟨hp₁p₂, r, hr, hp₃p₂⟩
  -- ⊢ Sbtw ℝ p₁ p₂ p₃
  refine' ⟨⟨1 / (1 - r), ⟨div_nonneg zero_le_one (sub_nonneg.2 (hr.le.trans zero_le_one)),
    (div_le_one (sub_pos.2 (hr.trans zero_lt_one))).2 ((le_sub_self_iff 1).2 hr.le)⟩, _⟩,
    (vsub_ne_zero.1 hp₁p₂).symm, _⟩
  · rw [← eq_vadd_iff_vsub_eq] at hp₃p₂
    -- ⊢ ↑(AffineMap.lineMap p₁ p₃) (1 / (1 - r)) = p₂
    rw [AffineMap.lineMap_apply, hp₃p₂, vadd_vsub_assoc, ← neg_vsub_eq_vsub_rev p₂ p₁, smul_neg, ←
      neg_smul, smul_add, smul_smul, ← add_smul, eq_comm, eq_vadd_iff_vsub_eq]
    convert (one_smul ℝ (p₂ -ᵥ p₁)).symm
    -- ⊢ 1 / (1 - r) * -r + 1 / (1 - r) = 1
    field_simp [(sub_pos.2 (hr.trans zero_lt_one)).ne.symm]
    -- ⊢ -(r * (1 - r)) + (1 - r) = (1 - r) * (1 - r)
    ring
    -- 🎉 no goals
  · rw [ne_comm, ← @vsub_ne_zero V, hp₃p₂, smul_ne_zero_iff]
    -- ⊢ r ≠ 0 ∧ p₁ -ᵥ p₂ ≠ 0
    exact ⟨hr.ne, hp₁p₂⟩
    -- 🎉 no goals
#align euclidean_geometry.angle_eq_pi_iff_sbtw EuclideanGeometry.angle_eq_pi_iff_sbtw

/-- If the second of three points is weakly between the other two, and not equal to the first,
the angle at the first point is zero. -/
theorem _root_.Wbtw.angle₂₁₃_eq_zero_of_ne {p₁ p₂ p₃ : P} (h : Wbtw ℝ p₁ p₂ p₃) (hp₂p₁ : p₂ ≠ p₁) :
    ∠ p₂ p₁ p₃ = 0 := by
  rw [angle, angle_eq_zero_iff]
  -- ⊢ p₂ -ᵥ p₁ ≠ 0 ∧ ∃ r, 0 < r ∧ p₃ -ᵥ p₁ = r • (p₂ -ᵥ p₁)
  rcases h with ⟨r, ⟨hr0, hr1⟩, rfl⟩
  -- ⊢ ↑(AffineMap.lineMap p₁ p₃) r -ᵥ p₁ ≠ 0 ∧ ∃ r_1, 0 < r_1 ∧ p₃ -ᵥ p₁ = r_1 • ( …
  have hr0' : r ≠ 0 := by
    rintro rfl
    simp at hp₂p₁
  replace hr0 := hr0.lt_of_ne hr0'.symm
  -- ⊢ ↑(AffineMap.lineMap p₁ p₃) r -ᵥ p₁ ≠ 0 ∧ ∃ r_1, 0 < r_1 ∧ p₃ -ᵥ p₁ = r_1 • ( …
  refine' ⟨vsub_ne_zero.2 hp₂p₁, r⁻¹, inv_pos.2 hr0, _⟩
  -- ⊢ p₃ -ᵥ p₁ = r⁻¹ • (↑(AffineMap.lineMap p₁ p₃) r -ᵥ p₁)
  rw [AffineMap.lineMap_apply, vadd_vsub_assoc, vsub_self, add_zero, smul_smul, inv_mul_cancel hr0',
    one_smul]
#align wbtw.angle₂₁₃_eq_zero_of_ne Wbtw.angle₂₁₃_eq_zero_of_ne

/-- If the second of three points is strictly between the other two, the angle at the first point
is zero. -/
theorem _root_.Sbtw.angle₂₁₃_eq_zero {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) : ∠ p₂ p₁ p₃ = 0 :=
  h.wbtw.angle₂₁₃_eq_zero_of_ne h.ne_left
#align sbtw.angle₂₁₃_eq_zero Sbtw.angle₂₁₃_eq_zero

/-- If the second of three points is weakly between the other two, and not equal to the first,
the angle at the first point (reversed) is zero. -/
theorem _root_.Wbtw.angle₃₁₂_eq_zero_of_ne {p₁ p₂ p₃ : P} (h : Wbtw ℝ p₁ p₂ p₃) (hp₂p₁ : p₂ ≠ p₁) :
    ∠ p₃ p₁ p₂ = 0 := by rw [← h.angle₂₁₃_eq_zero_of_ne hp₂p₁, angle_comm]
                         -- 🎉 no goals
#align wbtw.angle₃₁₂_eq_zero_of_ne Wbtw.angle₃₁₂_eq_zero_of_ne

/-- If the second of three points is strictly between the other two, the angle at the first point
(reversed) is zero. -/
theorem _root_.Sbtw.angle₃₁₂_eq_zero {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) : ∠ p₃ p₁ p₂ = 0 :=
  h.wbtw.angle₃₁₂_eq_zero_of_ne h.ne_left
#align sbtw.angle₃₁₂_eq_zero Sbtw.angle₃₁₂_eq_zero

/-- If the second of three points is weakly between the other two, and not equal to the third,
the angle at the third point is zero. -/
theorem _root_.Wbtw.angle₂₃₁_eq_zero_of_ne {p₁ p₂ p₃ : P} (h : Wbtw ℝ p₁ p₂ p₃) (hp₂p₃ : p₂ ≠ p₃) :
    ∠ p₂ p₃ p₁ = 0 :=
  h.symm.angle₂₁₃_eq_zero_of_ne hp₂p₃
#align wbtw.angle₂₃₁_eq_zero_of_ne Wbtw.angle₂₃₁_eq_zero_of_ne

/-- If the second of three points is strictly between the other two, the angle at the third point
is zero. -/
theorem _root_.Sbtw.angle₂₃₁_eq_zero {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) : ∠ p₂ p₃ p₁ = 0 :=
  h.wbtw.angle₂₃₁_eq_zero_of_ne h.ne_right
#align sbtw.angle₂₃₁_eq_zero Sbtw.angle₂₃₁_eq_zero

/-- If the second of three points is weakly between the other two, and not equal to the third,
the angle at the third point (reversed) is zero. -/
theorem _root_.Wbtw.angle₁₃₂_eq_zero_of_ne {p₁ p₂ p₃ : P} (h : Wbtw ℝ p₁ p₂ p₃) (hp₂p₃ : p₂ ≠ p₃) :
    ∠ p₁ p₃ p₂ = 0 :=
  h.symm.angle₃₁₂_eq_zero_of_ne hp₂p₃
#align wbtw.angle₁₃₂_eq_zero_of_ne Wbtw.angle₁₃₂_eq_zero_of_ne

/-- If the second of three points is strictly between the other two, the angle at the third point
(reversed) is zero. -/
theorem _root_.Sbtw.angle₁₃₂_eq_zero {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) : ∠ p₁ p₃ p₂ = 0 :=
  h.wbtw.angle₁₃₂_eq_zero_of_ne h.ne_right
#align sbtw.angle₁₃₂_eq_zero Sbtw.angle₁₃₂_eq_zero

/-- The angle between three points is zero if and only if one of the first and third points is
weakly between the other two, and not equal to the second. -/
theorem angle_eq_zero_iff_ne_and_wbtw {p₁ p₂ p₃ : P} :
    ∠ p₁ p₂ p₃ = 0 ↔ p₁ ≠ p₂ ∧ Wbtw ℝ p₂ p₁ p₃ ∨ p₃ ≠ p₂ ∧ Wbtw ℝ p₂ p₃ p₁ := by
  constructor
  -- ⊢ ∠ p₁ p₂ p₃ = 0 → p₁ ≠ p₂ ∧ Wbtw ℝ p₂ p₁ p₃ ∨ p₃ ≠ p₂ ∧ Wbtw ℝ p₂ p₃ p₁
  · rw [angle, angle_eq_zero_iff]
    -- ⊢ (p₁ -ᵥ p₂ ≠ 0 ∧ ∃ r, 0 < r ∧ p₃ -ᵥ p₂ = r • (p₁ -ᵥ p₂)) → p₁ ≠ p₂ ∧ Wbtw ℝ p …
    rintro ⟨hp₁p₂, r, hr0, hp₃p₂⟩
    -- ⊢ p₁ ≠ p₂ ∧ Wbtw ℝ p₂ p₁ p₃ ∨ p₃ ≠ p₂ ∧ Wbtw ℝ p₂ p₃ p₁
    rcases le_or_lt 1 r with (hr1 | hr1)
    -- ⊢ p₁ ≠ p₂ ∧ Wbtw ℝ p₂ p₁ p₃ ∨ p₃ ≠ p₂ ∧ Wbtw ℝ p₂ p₃ p₁
    · refine' Or.inl ⟨vsub_ne_zero.1 hp₁p₂, r⁻¹, ⟨(inv_pos.2 hr0).le, inv_le_one hr1⟩, _⟩
      -- ⊢ ↑(AffineMap.lineMap p₂ p₃) r⁻¹ = p₁
      rw [AffineMap.lineMap_apply, hp₃p₂, smul_smul, inv_mul_cancel hr0.ne.symm, one_smul,
        vsub_vadd]
    · refine' Or.inr ⟨_, r, ⟨hr0.le, hr1.le⟩, _⟩
      -- ⊢ p₃ ≠ p₂
      · rw [← @vsub_ne_zero V, hp₃p₂, smul_ne_zero_iff]
        -- ⊢ r ≠ 0 ∧ p₁ -ᵥ p₂ ≠ 0
        exact ⟨hr0.ne.symm, hp₁p₂⟩
        -- 🎉 no goals
      · rw [AffineMap.lineMap_apply, ← hp₃p₂, vsub_vadd]
        -- 🎉 no goals
  · rintro (⟨hp₁p₂, h⟩ | ⟨hp₃p₂, h⟩)
    -- ⊢ ∠ p₁ p₂ p₃ = 0
    · exact h.angle₂₁₃_eq_zero_of_ne hp₁p₂
      -- 🎉 no goals
    · exact h.angle₃₁₂_eq_zero_of_ne hp₃p₂
      -- 🎉 no goals
#align euclidean_geometry.angle_eq_zero_iff_ne_and_wbtw EuclideanGeometry.angle_eq_zero_iff_ne_and_wbtw

/-- The angle between three points is zero if and only if one of the first and third points is
strictly between the other two, or those two points are equal but not equal to the second. -/
theorem angle_eq_zero_iff_eq_and_ne_or_sbtw {p₁ p₂ p₃ : P} :
    ∠ p₁ p₂ p₃ = 0 ↔ p₁ = p₃ ∧ p₁ ≠ p₂ ∨ Sbtw ℝ p₂ p₁ p₃ ∨ Sbtw ℝ p₂ p₃ p₁ := by
  rw [angle_eq_zero_iff_ne_and_wbtw]
  -- ⊢ p₁ ≠ p₂ ∧ Wbtw ℝ p₂ p₁ p₃ ∨ p₃ ≠ p₂ ∧ Wbtw ℝ p₂ p₃ p₁ ↔ p₁ = p₃ ∧ p₁ ≠ p₂ ∨  …
  by_cases hp₁p₂ : p₁ = p₂; · simp [hp₁p₂]
  -- ⊢ p₁ ≠ p₂ ∧ Wbtw ℝ p₂ p₁ p₃ ∨ p₃ ≠ p₂ ∧ Wbtw ℝ p₂ p₃ p₁ ↔ p₁ = p₃ ∧ p₁ ≠ p₂ ∨  …
                              -- 🎉 no goals
  by_cases hp₁p₃ : p₁ = p₃; · simp [hp₁p₃]
  -- ⊢ p₁ ≠ p₂ ∧ Wbtw ℝ p₂ p₁ p₃ ∨ p₃ ≠ p₂ ∧ Wbtw ℝ p₂ p₃ p₁ ↔ p₁ = p₃ ∧ p₁ ≠ p₂ ∨  …
                              -- 🎉 no goals
  by_cases hp₃p₂ : p₃ = p₂; · simp [hp₃p₂]
  -- ⊢ p₁ ≠ p₂ ∧ Wbtw ℝ p₂ p₁ p₃ ∨ p₃ ≠ p₂ ∧ Wbtw ℝ p₂ p₃ p₁ ↔ p₁ = p₃ ∧ p₁ ≠ p₂ ∨  …
                              -- 🎉 no goals
  simp [hp₁p₂, hp₁p₃, Ne.symm hp₁p₃, Sbtw, hp₃p₂]
  -- 🎉 no goals
#align euclidean_geometry.angle_eq_zero_iff_eq_and_ne_or_sbtw EuclideanGeometry.angle_eq_zero_iff_eq_and_ne_or_sbtw

/-- Three points are collinear if and only if the first or third point equals the second or the
angle between them is 0 or π. -/
theorem collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi {p₁ p₂ p₃ : P} :
    Collinear ℝ ({p₁, p₂, p₃} : Set P) ↔ p₁ = p₂ ∨ p₃ = p₂ ∨ ∠ p₁ p₂ p₃ = 0 ∨ ∠ p₁ p₂ p₃ = π := by
  refine' ⟨fun h => _, fun h => _⟩
  -- ⊢ p₁ = p₂ ∨ p₃ = p₂ ∨ ∠ p₁ p₂ p₃ = 0 ∨ ∠ p₁ p₂ p₃ = π
  · replace h := h.wbtw_or_wbtw_or_wbtw
    -- ⊢ p₁ = p₂ ∨ p₃ = p₂ ∨ ∠ p₁ p₂ p₃ = 0 ∨ ∠ p₁ p₂ p₃ = π
    by_cases h₁₂ : p₁ = p₂
    -- ⊢ p₁ = p₂ ∨ p₃ = p₂ ∨ ∠ p₁ p₂ p₃ = 0 ∨ ∠ p₁ p₂ p₃ = π
    · exact Or.inl h₁₂
      -- 🎉 no goals
    by_cases h₃₂ : p₃ = p₂
    -- ⊢ p₁ = p₂ ∨ p₃ = p₂ ∨ ∠ p₁ p₂ p₃ = 0 ∨ ∠ p₁ p₂ p₃ = π
    · exact Or.inr (Or.inl h₃₂)
      -- 🎉 no goals
    rw [or_iff_right h₁₂, or_iff_right h₃₂]
    -- ⊢ ∠ p₁ p₂ p₃ = 0 ∨ ∠ p₁ p₂ p₃ = π
    rcases h with (h | h | h)
    · exact Or.inr (angle_eq_pi_iff_sbtw.2 ⟨h, Ne.symm h₁₂, Ne.symm h₃₂⟩)
      -- 🎉 no goals
    · exact Or.inl (h.angle₃₁₂_eq_zero_of_ne h₃₂)
      -- 🎉 no goals
    · exact Or.inl (h.angle₂₃₁_eq_zero_of_ne h₁₂)
      -- 🎉 no goals
  · rcases h with (rfl | rfl | h | h)
    · simpa using collinear_pair ℝ p₁ p₃
      -- 🎉 no goals
    · simpa using collinear_pair ℝ p₁ p₃
      -- 🎉 no goals
    · rw [angle_eq_zero_iff_ne_and_wbtw] at h
      -- ⊢ Collinear ℝ {p₁, p₂, p₃}
      rcases h with (⟨-, h⟩ | ⟨-, h⟩)
      -- ⊢ Collinear ℝ {p₁, p₂, p₃}
      · rw [Set.insert_comm]
        -- ⊢ Collinear ℝ {p₂, p₁, p₃}
        exact h.collinear
        -- 🎉 no goals
      · rw [Set.insert_comm, Set.pair_comm]
        -- ⊢ Collinear ℝ {p₂, p₃, p₁}
        exact h.collinear
        -- 🎉 no goals
    · rw [angle_eq_pi_iff_sbtw] at h
      -- ⊢ Collinear ℝ {p₁, p₂, p₃}
      exact h.wbtw.collinear
      -- 🎉 no goals
#align euclidean_geometry.collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi EuclideanGeometry.collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi

/-- If the angle between three points is 0, they are collinear. -/
theorem collinear_of_angle_eq_zero {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = 0) :
    Collinear ℝ ({p₁, p₂, p₃} : Set P) :=
  collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi.2 <| Or.inr <| Or.inr <| Or.inl h
#align euclidean_geometry.collinear_of_angle_eq_zero EuclideanGeometry.collinear_of_angle_eq_zero

/-- If the angle between three points is π, they are collinear. -/
theorem collinear_of_angle_eq_pi {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π) :
    Collinear ℝ ({p₁, p₂, p₃} : Set P) :=
  collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi.2 <| Or.inr <| Or.inr <| Or.inr h
#align euclidean_geometry.collinear_of_angle_eq_pi EuclideanGeometry.collinear_of_angle_eq_pi

/-- If three points are not collinear, the angle between them is nonzero. -/
theorem angle_ne_zero_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear ℝ ({p₁, p₂, p₃} : Set P)) :
    ∠ p₁ p₂ p₃ ≠ 0 :=
  mt collinear_of_angle_eq_zero h
#align euclidean_geometry.angle_ne_zero_of_not_collinear EuclideanGeometry.angle_ne_zero_of_not_collinear

/-- If three points are not collinear, the angle between them is not π. -/
theorem angle_ne_pi_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear ℝ ({p₁, p₂, p₃} : Set P)) :
    ∠ p₁ p₂ p₃ ≠ π :=
  mt collinear_of_angle_eq_pi h
#align euclidean_geometry.angle_ne_pi_of_not_collinear EuclideanGeometry.angle_ne_pi_of_not_collinear

/-- If three points are not collinear, the angle between them is positive. -/
theorem angle_pos_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear ℝ ({p₁, p₂, p₃} : Set P)) :
    0 < ∠ p₁ p₂ p₃ :=
  (angle_nonneg _ _ _).lt_of_ne (angle_ne_zero_of_not_collinear h).symm
#align euclidean_geometry.angle_pos_of_not_collinear EuclideanGeometry.angle_pos_of_not_collinear

/-- If three points are not collinear, the angle between them is less than π. -/
theorem angle_lt_pi_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear ℝ ({p₁, p₂, p₃} : Set P)) :
    ∠ p₁ p₂ p₃ < π :=
  (angle_le_pi _ _ _).lt_of_ne <| angle_ne_pi_of_not_collinear h
#align euclidean_geometry.angle_lt_pi_of_not_collinear EuclideanGeometry.angle_lt_pi_of_not_collinear

/-- The cosine of the angle between three points is 1 if and only if the angle is 0. -/
nonrec theorem cos_eq_one_iff_angle_eq_zero {p₁ p₂ p₃ : P} :
    Real.cos (∠ p₁ p₂ p₃) = 1 ↔ ∠ p₁ p₂ p₃ = 0 :=
  cos_eq_one_iff_angle_eq_zero
#align euclidean_geometry.cos_eq_one_iff_angle_eq_zero EuclideanGeometry.cos_eq_one_iff_angle_eq_zero

/-- The cosine of the angle between three points is 0 if and only if the angle is π / 2. -/
nonrec theorem cos_eq_zero_iff_angle_eq_pi_div_two {p₁ p₂ p₃ : P} :
    Real.cos (∠ p₁ p₂ p₃) = 0 ↔ ∠ p₁ p₂ p₃ = π / 2 :=
  cos_eq_zero_iff_angle_eq_pi_div_two
#align euclidean_geometry.cos_eq_zero_iff_angle_eq_pi_div_two EuclideanGeometry.cos_eq_zero_iff_angle_eq_pi_div_two

/-- The cosine of the angle between three points is -1 if and only if the angle is π. -/
nonrec theorem cos_eq_neg_one_iff_angle_eq_pi {p₁ p₂ p₃ : P} :
    Real.cos (∠ p₁ p₂ p₃) = -1 ↔ ∠ p₁ p₂ p₃ = π :=
  cos_eq_neg_one_iff_angle_eq_pi
#align euclidean_geometry.cos_eq_neg_one_iff_angle_eq_pi EuclideanGeometry.cos_eq_neg_one_iff_angle_eq_pi

/-- The sine of the angle between three points is 0 if and only if the angle is 0 or π. -/
nonrec theorem sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi {p₁ p₂ p₃ : P} :
    Real.sin (∠ p₁ p₂ p₃) = 0 ↔ ∠ p₁ p₂ p₃ = 0 ∨ ∠ p₁ p₂ p₃ = π :=
  sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi
#align euclidean_geometry.sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi EuclideanGeometry.sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi

/-- The sine of the angle between three points is 1 if and only if the angle is π / 2. -/
nonrec theorem sin_eq_one_iff_angle_eq_pi_div_two {p₁ p₂ p₃ : P} :
    Real.sin (∠ p₁ p₂ p₃) = 1 ↔ ∠ p₁ p₂ p₃ = π / 2 :=
  sin_eq_one_iff_angle_eq_pi_div_two
#align euclidean_geometry.sin_eq_one_iff_angle_eq_pi_div_two EuclideanGeometry.sin_eq_one_iff_angle_eq_pi_div_two

/-- Three points are collinear if and only if the first or third point equals the second or
the sine of the angle between three points is zero. -/
theorem collinear_iff_eq_or_eq_or_sin_eq_zero {p₁ p₂ p₃ : P} :
    Collinear ℝ ({p₁, p₂, p₃} : Set P) ↔ p₁ = p₂ ∨ p₃ = p₂ ∨ Real.sin (∠ p₁ p₂ p₃) = 0 := by
  rw [sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi,
    collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi]
#align euclidean_geometry.collinear_iff_eq_or_eq_or_sin_eq_zero EuclideanGeometry.collinear_iff_eq_or_eq_or_sin_eq_zero

/-- If three points are not collinear, the sine of the angle between them is positive. -/
theorem sin_pos_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear ℝ ({p₁, p₂, p₃} : Set P)) :
    0 < Real.sin (∠ p₁ p₂ p₃) :=
  Real.sin_pos_of_pos_of_lt_pi (angle_pos_of_not_collinear h) (angle_lt_pi_of_not_collinear h)
#align euclidean_geometry.sin_pos_of_not_collinear EuclideanGeometry.sin_pos_of_not_collinear

/-- If three points are not collinear, the sine of the angle between them is nonzero. -/
theorem sin_ne_zero_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear ℝ ({p₁, p₂, p₃} : Set P)) :
    Real.sin (∠ p₁ p₂ p₃) ≠ 0 :=
  ne_of_gt (sin_pos_of_not_collinear h)
#align euclidean_geometry.sin_ne_zero_of_not_collinear EuclideanGeometry.sin_ne_zero_of_not_collinear

/-- If the sine of the angle between three points is 0, they are collinear. -/
theorem collinear_of_sin_eq_zero {p₁ p₂ p₃ : P} (h : Real.sin (∠ p₁ p₂ p₃) = 0) :
    Collinear ℝ ({p₁, p₂, p₃} : Set P) := by
  revert h
  -- ⊢ sin (∠ p₁ p₂ p₃) = 0 → Collinear ℝ {p₁, p₂, p₃}
  contrapose
  -- ⊢ ¬Collinear ℝ {p₁, p₂, p₃} → ¬sin (∠ p₁ p₂ p₃) = 0
  exact sin_ne_zero_of_not_collinear
  -- 🎉 no goals
#align euclidean_geometry.collinear_of_sin_eq_zero EuclideanGeometry.collinear_of_sin_eq_zero

end EuclideanGeometry
