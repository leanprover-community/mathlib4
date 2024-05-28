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


theorem erase_zero_erase_succ {n : ℕ} (s : Affine.Simplex ℝ P (n + 2)) (i : Fin (n + 2)) :
    (s.erase i.succ).erase 0 = (s.erase 0).erase i := by
  ext; simp

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


open EuclideanGeometry (orthogonalProjection)
/-- A more general case of the equation lemma, allowing erasing an arbitrary point. -/
theorem volume_succ {n : ℕ} (s : Affine.Simplex ℝ P (n + 1)) (i : Fin (n + 2)) :
  s.volume =
    (↑(n + 1) : ℝ)⁻¹ * dist
      (s.points i)
      ((s.erase i).orthogonalProjectionSpan (s.points i)) * (s.erase i).volume := by
  induction n with
  | zero =>
    -- base case: can swap two points
    rw [volume_zero, mul_one, orthogonalProjection_eq_point, volume_one]
    simp_rw [zero_add, Nat.cast_one, inv_one, one_mul]
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      obtain rfl := Subsingleton.elim i 0
      exact dist_comm _ _
  | succ n ih =>
    rw [Simplex.volume]
    simp_rw [mul_assoc]
    congr 1
    simp
    induction i using Fin.cases with
    | zero => rfl
    | succ i =>
      conv_lhs => rw [ih _ i, mul_assoc (_⁻¹), mul_left_comm _ (_⁻¹)]
      conv_rhs => rw [ih _ 0, mul_assoc (_⁻¹), mul_left_comm _ (_⁻¹)]
      congr 1
      rw [mul_left_comm, ← erase_zero_erase_succ]
      simp_rw [← mul_assoc]
      congr 1
      simp
      clear ih
      set p0 := s.points 0
      set pi := s.points i.succ
      -- Projection of p0 onto `S / {0}`
      set q0 : P := ↑((s.erase 0).orthogonalProjectionSpan p0) with hq0
      -- Projection of pi onto `S / {i}`
      set qi : P := ↑((s.erase i.succ).orthogonalProjectionSpan pi) with hqi
      -- Projection of p0 and pi onto `S / {0, i}`
      set r0 : P := ↑(((s.erase i.succ).erase 0).orthogonalProjectionSpan p0) with hr0
      set ri : P := ↑(((s.erase i.succ).erase 0).orthogonalProjectionSpan pi) with hri
      erw [← hq0, ← hqi, ← hr0, ← hri]
      simp_rw [← coe_nndist, ← NNReal.coe_mul, NNReal.coe_inj]
      rw [← sq_eq_sq (zero_le _) (zero_le _)]
      simp_rw [sq, ← NNReal.coe_inj, NNReal.coe_mul, coe_nndist]
      conv_lhs => rw [mul_mul_mul_comm]
      conv_rhs => rw [mul_mul_mul_comm]
      conv_lhs =>
        enter [1]
        rw [(s.erase i.succ).dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq _
          sorry]


end Simplex

end Affine
