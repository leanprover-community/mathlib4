/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Geometry.Euclidean.Sphere.Basic

#align_import geometry.euclidean.sphere.second_inter from "leanprover-community/mathlib"@"46b633fd842bef9469441c0209906f6dddd2b4f5"

/-!
# Second intersection of a sphere and a line

This file defines and proves basic results about the second intersection of a sphere with a line
through a point on that sphere.

## Main definitions

* `EuclideanGeometry.Sphere.secondInter` is the second intersection of a sphere with a line
  through a point on that sphere.

-/


noncomputable section

open RealInnerProductSpace

namespace EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- The second intersection of a sphere with a line through a point on that sphere; that point
if it is the only point of intersection of the line with the sphere. The intended use of this
definition is when `p ∈ s`; the definition does not use `s.radius`, so in general it returns
the second intersection with the sphere through `p` and with center `s.center`. -/
def Sphere.secondInter (s : Sphere P) (p : P) (v : V) : P :=
  (-2 * ⟪v, p -ᵥ s.center⟫ / ⟪v, v⟫) • v +ᵥ p
#align euclidean_geometry.sphere.second_inter EuclideanGeometry.Sphere.secondInter

/-- The distance between `secondInter` and the center equals the distance between the original
point and the center. -/
@[simp]
theorem Sphere.secondInter_dist (s : Sphere P) (p : P) (v : V) :
    dist (s.secondInter p v) s.center = dist p s.center := by
  rw [Sphere.secondInter]
  -- ⊢ dist ((-2 * inner v (p -ᵥ s.center) / inner v v) • v +ᵥ p) s.center = dist p …
  by_cases hv : v = 0; · simp [hv]
  -- ⊢ dist ((-2 * inner v (p -ᵥ s.center) / inner v v) • v +ᵥ p) s.center = dist p …
                         -- 🎉 no goals
  rw [dist_smul_vadd_eq_dist _ _ hv]
  -- ⊢ -2 * inner v (p -ᵥ s.center) / inner v v = 0 ∨ -2 * inner v (p -ᵥ s.center)  …
  exact Or.inr rfl
  -- 🎉 no goals
#align euclidean_geometry.sphere.second_inter_dist EuclideanGeometry.Sphere.secondInter_dist

/-- The point given by `secondInter` lies on the sphere. -/
@[simp]
theorem Sphere.secondInter_mem {s : Sphere P} {p : P} (v : V) : s.secondInter p v ∈ s ↔ p ∈ s := by
  simp_rw [mem_sphere, Sphere.secondInter_dist]
  -- 🎉 no goals
#align euclidean_geometry.sphere.second_inter_mem EuclideanGeometry.Sphere.secondInter_mem

variable (V)

/-- If the vector is zero, `secondInter` gives the original point. -/
@[simp]
theorem Sphere.secondInter_zero (s : Sphere P) (p : P) : s.secondInter p (0 : V) = p := by
  simp [Sphere.secondInter]
  -- 🎉 no goals
#align euclidean_geometry.sphere.second_inter_zero EuclideanGeometry.Sphere.secondInter_zero

variable {V}

/-- The point given by `secondInter` equals the original point if and only if the line is
orthogonal to the radius vector. -/
theorem Sphere.secondInter_eq_self_iff {s : Sphere P} {p : P} {v : V} :
    s.secondInter p v = p ↔ ⟪v, p -ᵥ s.center⟫ = 0 := by
  refine' ⟨fun hp => _, fun hp => _⟩
  -- ⊢ inner v (p -ᵥ s.center) = 0
  · by_cases hv : v = 0
    -- ⊢ inner v (p -ᵥ s.center) = 0
    · simp [hv]
      -- 🎉 no goals
    rwa [Sphere.secondInter, eq_comm, eq_vadd_iff_vsub_eq, vsub_self, eq_comm, smul_eq_zero,
      or_iff_left hv, div_eq_zero_iff, inner_self_eq_zero, or_iff_left hv, mul_eq_zero,
      or_iff_right (by norm_num : (-2 : ℝ) ≠ 0)] at hp
  · rw [Sphere.secondInter, hp, mul_zero, zero_div, zero_smul, zero_vadd]
    -- 🎉 no goals
#align euclidean_geometry.sphere.second_inter_eq_self_iff EuclideanGeometry.Sphere.secondInter_eq_self_iff

/-- A point on a line through a point on a sphere equals that point or `secondInter`. -/
theorem Sphere.eq_or_eq_secondInter_of_mem_mk'_span_singleton_iff_mem {s : Sphere P} {p : P}
    (hp : p ∈ s) {v : V} {p' : P} (hp' : p' ∈ AffineSubspace.mk' p (ℝ ∙ v)) :
    p' = p ∨ p' = s.secondInter p v ↔ p' ∈ s := by
  refine' ⟨fun h => _, fun h => _⟩
  -- ⊢ p' ∈ s
  · rcases h with (h | h)
    -- ⊢ p' ∈ s
    · rwa [h]
      -- 🎉 no goals
    · rwa [h, Sphere.secondInter_mem]
      -- 🎉 no goals
  · rw [AffineSubspace.mem_mk'_iff_vsub_mem, Submodule.mem_span_singleton] at hp'
    -- ⊢ p' = p ∨ p' = secondInter s p v
    rcases hp' with ⟨r, hr⟩
    -- ⊢ p' = p ∨ p' = secondInter s p v
    rw [eq_comm, ← eq_vadd_iff_vsub_eq] at hr
    -- ⊢ p' = p ∨ p' = secondInter s p v
    subst hr
    -- ⊢ r • v +ᵥ p = p ∨ r • v +ᵥ p = secondInter s p v
    by_cases hv : v = 0
    -- ⊢ r • v +ᵥ p = p ∨ r • v +ᵥ p = secondInter s p v
    · simp [hv]
      -- 🎉 no goals
    rw [Sphere.secondInter]
    -- ⊢ r • v +ᵥ p = p ∨ r • v +ᵥ p = (-2 * inner v (p -ᵥ s.center) / inner v v) • v …
    rw [mem_sphere] at h hp
    -- ⊢ r • v +ᵥ p = p ∨ r • v +ᵥ p = (-2 * inner v (p -ᵥ s.center) / inner v v) • v …
    rw [← hp, dist_smul_vadd_eq_dist _ _ hv] at h
    -- ⊢ r • v +ᵥ p = p ∨ r • v +ᵥ p = (-2 * inner v (p -ᵥ s.center) / inner v v) • v …
    rcases h with (h | h) <;> simp [h]
    -- ⊢ r • v +ᵥ p = p ∨ r • v +ᵥ p = (-2 * inner v (p -ᵥ s.center) / inner v v) • v …
                              -- 🎉 no goals
                              -- 🎉 no goals
#align euclidean_geometry.sphere.eq_or_eq_second_inter_of_mem_mk'_span_singleton_iff_mem EuclideanGeometry.Sphere.eq_or_eq_secondInter_of_mem_mk'_span_singleton_iff_mem

/-- `secondInter` is unchanged by multiplying the vector by a nonzero real. -/
@[simp]
theorem Sphere.secondInter_smul (s : Sphere P) (p : P) (v : V) {r : ℝ} (hr : r ≠ 0) :
    s.secondInter p (r • v) = s.secondInter p v := by
  simp_rw [Sphere.secondInter, real_inner_smul_left, inner_smul_right, smul_smul,
    div_mul_eq_div_div]
  rw [mul_comm, ← mul_div_assoc, ← mul_div_assoc, mul_div_cancel_left _ hr, mul_comm, mul_assoc,
    mul_div_cancel_left _ hr, mul_comm]
#align euclidean_geometry.sphere.second_inter_smul EuclideanGeometry.Sphere.secondInter_smul

/-- `secondInter` is unchanged by negating the vector. -/
@[simp]
theorem Sphere.secondInter_neg (s : Sphere P) (p : P) (v : V) :
    s.secondInter p (-v) = s.secondInter p v := by
  rw [← neg_one_smul ℝ v, s.secondInter_smul p v (by norm_num : (-1 : ℝ) ≠ 0)]
  -- 🎉 no goals
#align euclidean_geometry.sphere.second_inter_neg EuclideanGeometry.Sphere.secondInter_neg

/-- Applying `secondInter` twice returns the original point. -/
@[simp]
theorem Sphere.secondInter_secondInter (s : Sphere P) (p : P) (v : V) :
    s.secondInter (s.secondInter p v) v = p := by
  by_cases hv : v = 0; · simp [hv]
  -- ⊢ secondInter s (secondInter s p v) v = p
                         -- 🎉 no goals
  have hv' : ⟪v, v⟫ ≠ 0 := inner_self_ne_zero.2 hv
  -- ⊢ secondInter s (secondInter s p v) v = p
  simp only [Sphere.secondInter, vadd_vsub_assoc, vadd_vadd, inner_add_right, inner_smul_right,
    div_mul_cancel _ hv']
  rw [← @vsub_eq_zero_iff_eq V, vadd_vsub, ← add_smul, ← add_div]
  -- ⊢ ((-2 * (-2 * inner v (p -ᵥ s.center) + inner v (p -ᵥ s.center)) + -2 * inner …
  convert zero_smul ℝ (M := V) _
  -- ⊢ (-2 * (-2 * inner v (p -ᵥ s.center) + inner v (p -ᵥ s.center)) + -2 * inner  …
  convert zero_div (G₀ := ℝ) _
  -- ⊢ -2 * (-2 * inner v (p -ᵥ s.center) + inner v (p -ᵥ s.center)) + -2 * inner v …
  ring
  -- 🎉 no goals
#align euclidean_geometry.sphere.second_inter_second_inter EuclideanGeometry.Sphere.secondInter_secondInter

/-- If the vector passed to `secondInter` is given by a subtraction involving the point in
`secondInter`, the result of `secondInter` may be expressed using `lineMap`. -/
theorem Sphere.secondInter_eq_lineMap (s : Sphere P) (p p' : P) :
    s.secondInter p (p' -ᵥ p) =
      AffineMap.lineMap p p' (-2 * ⟪p' -ᵥ p, p -ᵥ s.center⟫ / ⟪p' -ᵥ p, p' -ᵥ p⟫) :=
  rfl
#align euclidean_geometry.sphere.second_inter_eq_line_map EuclideanGeometry.Sphere.secondInter_eq_lineMap

/-- If the vector passed to `secondInter` is given by a subtraction involving the point in
`secondInter`, the result lies in the span of the two points. -/
theorem Sphere.secondInter_vsub_mem_affineSpan (s : Sphere P) (p₁ p₂ : P) :
    s.secondInter p₁ (p₂ -ᵥ p₁) ∈ line[ℝ, p₁, p₂] :=
  smul_vsub_vadd_mem_affineSpan_pair _ _ _
#align euclidean_geometry.sphere.second_inter_vsub_mem_affine_span EuclideanGeometry.Sphere.secondInter_vsub_mem_affineSpan

/-- If the vector passed to `secondInter` is given by a subtraction involving the point in
`secondInter`, the three points are collinear. -/
theorem Sphere.secondInter_collinear (s : Sphere P) (p p' : P) :
    Collinear ℝ ({p, p', s.secondInter p (p' -ᵥ p)} : Set P) := by
  rw [Set.pair_comm, Set.insert_comm]
  -- ⊢ Collinear ℝ {secondInter s p (p' -ᵥ p), p, p'}
  exact
    (collinear_insert_iff_of_mem_affineSpan (s.secondInter_vsub_mem_affineSpan _ _)).2
      (collinear_pair ℝ _ _)
#align euclidean_geometry.sphere.second_inter_collinear EuclideanGeometry.Sphere.secondInter_collinear

/-- If the vector passed to `secondInter` is given by a subtraction involving the point in
`secondInter`, and the second point is not outside the sphere, the second point is weakly
between the first point and the result of `secondInter`. -/
theorem Sphere.wbtw_secondInter {s : Sphere P} {p p' : P} (hp : p ∈ s)
    (hp' : dist p' s.center ≤ s.radius) : Wbtw ℝ p p' (s.secondInter p (p' -ᵥ p)) := by
  by_cases h : p' = p; · simp [h]
  -- ⊢ Wbtw ℝ p p' (secondInter s p (p' -ᵥ p))
                         -- 🎉 no goals
  refine'
    wbtw_of_collinear_of_dist_center_le_radius (s.secondInter_collinear p p') hp hp'
      ((Sphere.secondInter_mem _).2 hp) _
  intro he
  -- ⊢ False
  rw [eq_comm, Sphere.secondInter_eq_self_iff, ← neg_neg (p' -ᵥ p), inner_neg_left,
    neg_vsub_eq_vsub_rev, neg_eq_zero, eq_comm] at he
  exact ((inner_pos_or_eq_of_dist_le_radius hp hp').resolve_right (Ne.symm h)).ne he
  -- 🎉 no goals
#align euclidean_geometry.sphere.wbtw_second_inter EuclideanGeometry.Sphere.wbtw_secondInter

/-- If the vector passed to `secondInter` is given by a subtraction involving the point in
`secondInter`, and the second point is inside the sphere, the second point is strictly between
the first point and the result of `secondInter`. -/
theorem Sphere.sbtw_secondInter {s : Sphere P} {p p' : P} (hp : p ∈ s)
    (hp' : dist p' s.center < s.radius) : Sbtw ℝ p p' (s.secondInter p (p' -ᵥ p)) := by
  refine' ⟨Sphere.wbtw_secondInter hp hp'.le, _, _⟩
  -- ⊢ p' ≠ p
  · rintro rfl
    -- ⊢ False
    rw [mem_sphere] at hp
    -- ⊢ False
    simp [hp] at hp'
    -- 🎉 no goals
  · rintro h
    -- ⊢ False
    rw [h, mem_sphere.1 ((Sphere.secondInter_mem _).2 hp)] at hp'
    -- ⊢ False
    exact lt_irrefl _ hp'
    -- 🎉 no goals
#align euclidean_geometry.sphere.sbtw_second_inter EuclideanGeometry.Sphere.sbtw_secondInter

end EuclideanGeometry
