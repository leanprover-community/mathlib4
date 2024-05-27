/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Geometry.Euclidean.MongePoint

/-!
# Results about `volume` in euclidean space
-/

open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace Affine.Simplex

variable {V : Type*} {P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

/-- The face of `s` that doesn't include `i` -/
@[simps (config := .asFn)]
def erase {n : ℕ} (s : Affine.Simplex ℝ P (n + 1)) (i : Fin (n + 2)) :
    Affine.Simplex ℝ P n where
  points := s.points ∘ Fin.succAbove i
  independent := s.independent.comp_embedding <| (Fin.succAboveEmb i).toEmbedding

/-- The volume of a simplex. -/
protected def volume {n : ℕ} (s : Affine.Simplex ℝ P n) : ℝ :=
  match n with
  | 0 => 1
  | (n + 1) =>
    (↑(n + 1) : ℝ)⁻¹ * dist
      (s.points 0)
      ((s.erase 0).orthogonalProjectionSpan (s.points 0)) * (s.erase 0).volume

@[simp] theorem volume_zero (s : Affine.Simplex ℝ P 0) : s.volume = 1 := rfl

open EuclideanGeometry (orthogonalProjection)

/-- The volume of a one-simplex (a line segment) is its length. -/
@[simp] theorem volume_one (s : Affine.Simplex ℝ P 1) :
    s.volume = dist (s.points 0) (s.points 1) := by
  simp_rw [Simplex.volume, mul_one, zero_add, Nat.cast_one, inv_one, one_mul, coe_affineSpan]
  have h1 : s.points 1 ∈ affineSpan ℝ (Set.range (s.erase 0).points) := by
    apply mem_affineSpan
    refine ⟨0, rfl⟩
  simp only [Nat.reduceAdd, Fin.isValue, erase_points, Fin.succAbove_zero]
  have := (s.erase 0).dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq
    (s.points 0) h1
  set p0' := (s.erase 0).orthogonalProjectionSpan (s.points 0) with hp0'
  erw [← hp0']
  rw [←sq_eq_sq dist_nonneg dist_nonneg, dist_comm _ (s.points 1), sq, sq, this,
    self_eq_add_left, mul_self_eq_zero, dist_eq_zero]
  rw [hp0']
  rw [orthogonalProjection_eq_point, erase_points, Fin.succAbove_zero, Function.comp_apply,
    Fin.succ_zero_eq_one]

/-- A more general case of the equation lemma, allowing erasing an arbitrary point. -/
theorem volume_succ {n : ℕ} (s : Affine.Simplex ℝ P (n + 1)) (i : Fin (n + 2)) :
  s.volume =
    dist
      (s.points i)
      ((s.erase i).orthogonalProjectionSpan (s.points 0)) * (s.erase i).volume := by
  induction n with
  | zero =>
    -- base case: can swap two points
    rw [volume_zero, mul_one, orthogonalProjection_eq_point, volume_one]
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      obtain rfl := Subsingleton.elim i 0
      exact dist_comm _ _
  | succ n ih =>
    sorry


#check AffineBasis

end Simplex

end Affine
