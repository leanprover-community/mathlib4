/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Geometry.Euclidean.NinePointCircle
public import Mathlib.Geometry.Euclidean.Incenter

import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.Geometry.Euclidean.Volume.Triangle

/-!

# Feuerbach's Theorem

This file proves Feuerbach's Theorem: the nine-point circle of a triangle is tangent to the incircle
and all three excircles.

## Reference
* Michael Scheer,
  [**A Simple Vector Proof of Feuerbach's Theorem**][scheer2011simplevectorprooffeuerbachs]

-/

public section

namespace Affine.Triangle

open Simplex EuclideanGeometry Real

variable {V P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
variable (t : Triangle ℝ P)

local notation "w" => excenterWeightsFace

private theorem dist_excenter_ninePointCircle_center_sq {signs : Finset (Fin 3)}
    (hsigns : signs = ∅ ∨ signs = {0} ∨ signs = {1} ∨ signs = {2}) :
    dist (t.excenter signs) t.ninePointCircle.center ^ 2 =
    (t.exradius signs + (if signs = ∅ then -1 else 1) * t.ninePointCircle.radius) ^ 2 := by
  have huniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by grind
  have h0 := t.sum_excenterWeightsFace_pos hsigns
  set p0 := t.points 0
  set p1 := t.points 1
  set p2 := t.points 2
  calc
    _ = (∑ i, w t signs i * dist (t.points i) (ninePointCircle t).center ^ 2) / ∑ i, w t signs i +
        (if signs = ∅ then -1 else 1) * 2 * t.circumradius * t.exradius signs := by
      simp_rw [t.dist_excenter_sq _ hsigns, t.excenterWeights_eq_excenterWeightsFace_div,
        ← mul_div_right_comm, ← Finset.sum_div]
    _ = (w t signs 0 * dist p0 (ninePointCircle t).center ^ 2 +
          w t signs 1 * dist p1 (ninePointCircle t).center ^ 2 +
          w t signs 2 * dist p2 (ninePointCircle t).center ^ 2) / ∑ i, w t signs i +
        (if signs = ∅ then -1 else 1) * 2 * t.circumradius * t.exradius signs := by
      congrm ?_ / _ + _
      simp [huniv]
      ring
    _ = ((∑ i, w t signs i) * t.circumradius ^ 2 / 4 +
          (w t signs 0 * (dist p0 p1 ^ 2 + dist p0 p2 ^ 2 - dist p1 p2 ^ 2) +
          w t signs 1 * (dist p0 p1 ^ 2 + dist p1 p2 ^ 2 - dist p0 p2 ^ 2) +
          w t signs 2 * (dist p1 p2 ^ 2 + dist p0 p2 ^ 2 - dist p0 p1 ^ 2)) / 4) /
        ∑ i, w t signs i +
        (if signs = ∅ then -1 else 1) * 2 * t.circumradius * t.exradius signs := by
      congrm ?_ / _ + _
      rw [t.dist_ninePointCircle_center_sq (i₂ := 1) (i₃ := 2) (by simp) (by simp) (by simp)]
      rw [t.dist_ninePointCircle_center_sq (i₂ := 0) (i₃ := 2) (by simp) (by simp) (by simp)]
      rw [t.dist_ninePointCircle_center_sq (i₂ := 0) (i₃ := 1) (by simp) (by simp) (by simp)]
      rw [dist_comm p2 p1, dist_comm p1 p0, dist_comm p2 p0]
      simp [huniv]
      ring
    _ = ((∑ i, w t signs i) * t.circumradius ^ 2 / 4 +
          ((dist p0 p1 + dist p0 p2 + dist p1 p2) * (-dist p0 p1 + dist p0 p2 + dist p1 p2) *
          (dist p0 p1 - dist p0 p2 + dist p1 p2) * (dist p0 p1 + dist p0 p2 - dist p1 p2) /
          ∑ i, w t signs i -
          (if signs = ∅ then -1 else 1) * 2 * (dist p0 p1 * dist p0 p2 * dist p1 p2)) / 4) /
          ∑ i, w t signs i +
        (if signs = ∅ then -1 else 1) * 2 * t.circumradius * t.exradius signs := by
      congrm (_ + ?_ / 4) / _ + _
      field_simp
      rcases hsigns with rfl | rfl | rfl | rfl
      all_goals
      · simp [huniv, excenterWeightsFace, faceOpposite_point_eq_point_succAbove, Fin.succAbove]
        ring
    _ = ((∑ i, w t signs i) * t.circumradius ^ 2 / 4 +
          (16 * t.volume ^ 2 / ∑ i, w t signs i -
          (if signs = ∅ then -1 else 1) * 2 * (dist p0 p1 * dist p0 p2 * dist p1 p2)) / 4) /
          ∑ i, w t signs i +
        (if signs = ∅ then -1 else 1) * 2 * t.circumradius * t.exradius signs := by
      congrm (_ + (?_ / _ - _) / 4) / _ + _
      rw [t.volume_sq_eq_mul_sub_mul_sub_mul_sub (i₁ := 0) (i₂ := 1) (i₃ := 2)
        (by simp) (by simp) (by simp)]
      ring
    _ = t.circumradius ^ 2 / 4 + t.exradius signs ^ 2 +
        (if signs = ∅ then -1 else 1) * t.circumradius * t.exradius signs := by
      rw [← t.four_mul_volume_mul_circumradius (by simp) (by simp) (by simp)]
      rw [(t.excenterExists signs).volume_eq_exradius_mul, abs_of_nonneg h0.le]
      field
    _ = _ := by
      rw [t.ninePointCircle_radius]
      by_cases h : signs = ∅ <;> simp [h] <;> ring

/--
**Feuerbach's Theorem** for excircles
-/
theorem isExtTangent_exsphere_ninePointCircle (i : Fin 3) :
    (t.exsphere {i}).IsExtTangent t.ninePointCircle := by
  rw [Sphere.isExtTangent_iff_dist_center]
  refine ⟨?_, t.exradius_nonneg {i}, t.ninePointCircle_radius_nonneg⟩
  rw [← sq_eq_sq₀ (by simp)
    (by exact add_nonneg (t.exradius_nonneg {i}) t.ninePointCircle_radius_nonneg)]
  rw [← excenter, t.dist_excenter_ninePointCircle_center_sq (by grind)]
  simp

/--
**Feuerbach's Theorem** for incircle
-/
theorem isIntTangent_insphere_ninePointCircle :
    t.insphere.IsIntTangent t.ninePointCircle := by
  have : Nontrivial V :=
    ⟨t.points 2 -ᵥ t.points 0, t.points 1 -ᵥ t.points 0, by simp [t.independent.injective.ne]⟩
  rw [Sphere.isIntTangent_iff_dist_center]
  refine ⟨?_, t.exradius_nonneg ∅, t.ninePointCircle_radius_nonneg⟩
  rw [← sq_eq_sq₀ (by simp) (by simpa using t.inradius_le_ninePointCircle_radius)]
  rw [← t.exsphere_empty, ← excenter, t.dist_excenter_ninePointCircle_center_sq (by grind)]
  simp
  ring

end Affine.Triangle
