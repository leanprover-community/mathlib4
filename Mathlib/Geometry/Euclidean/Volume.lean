/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Geometry.Euclidean.MongePoint

open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace Affine.Simplex

variable {V : Type*} {P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

/-- Get the face of `s` that doesn't include `i` -/
@[simps?]
def faceWithout {n : ℕ} (s : Affine.Simplex ℝ P (n + 1)) (i : Fin (n + 2)) :
    Affine.Simplex ℝ P n where
  points j := s.points (Fin.succAbove i j)
  independent := s.independent.comp_embedding <| (Fin.succAboveEmb i).toEmbedding


/-- The volume of a simplex. -/
protected def volume {n : ℕ} (s : Affine.Simplex ℝ P n) : ℝ :=
  match n with
  | 0 => 1
  | (n + 1) =>
    (↑(n + 1) : ℝ)⁻¹ * dist
      (s.points 0)
      ((s.faceWithout 0).orthogonalProjectionSpan (s.points 0)) * (s.faceWithout 0).volume

@[simp] theorem volume_zero (s : Affine.Simplex ℝ P 0) : s.volume = 1 := rfl

@[simp] theorem volume_one (s : Affine.Simplex ℝ P 1) :
    s.volume = dist (s.points 0) (s.points 1) := by
  simp_rw [Simplex.volume, mul_one, zero_add, Nat.cast_one, inv_one, one_mul, coe_affineSpan]
  have h1 : s.points 1 ∈ affineSpan ℝ (Set.range (s.faceWithout 0).points) := sorry
  rw [orthogonalProjectionSpan]
  simp
  have := (s.faceWithout 0).dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq
    (s.points 0) h1
  simp? [orthogonalProjectionSpan] at this
  -- set q := (EuclideanGeometry.orthogonalProjection (affineSpan ℝ (Set.range (faceWithout s 0).points))) (s.points 0)
  rw [←sq_eq_sq dist_nonneg dist_nonneg, dist_comm _ (s.points 1), sq, sq, this,
    self_eq_add_left, mul_self_eq_zero, dist_eq_zero, faceWithout]
  clear this
  simp?
  dsimp
  norm_num
  sorry
example (a b : ℤ) : a = a + b ↔ b = 0 := by exact?

/---/
theorem volume_succ {n : ℕ} (s : Affine.Simplex ℝ P (n + 1)) (i : Fin (n + 2)) :
  s.volume =
    dist
      (s.points i)
      ((s.faceWithout i).orthogonalProjectionSpan (s.points 0)) * (s.faceWithout i).volume :=
  sorry


#check AffineBasis

end Simplex

end Affine
