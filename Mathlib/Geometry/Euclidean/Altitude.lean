/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Geometry.Euclidean.Projection
import Mathlib.Analysis.InnerProductSpace.Affine

/-!
# Altitudes of a simplex

This file defines the altitudes of a simplex and their feet.

## Main definitions

* `altitude` is the line that passes through a vertex of a simplex and
  is orthogonal to the opposite face.

* `altitudeFoot` is the orthogonal projection of a vertex of a simplex onto the opposite face.

* `height` is the distance between a vertex of a simplex and its `altitudeFoot`.

## References

* <https://en.wikipedia.org/wiki/Altitude_(triangle)>

-/

noncomputable section

namespace Affine

namespace Simplex

open Finset AffineSubspace EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- An altitude of a simplex is the line that passes through a vertex
and is orthogonal to the opposite face. -/
def altitude {n : ℕ} (s : Simplex ℝ P (n + 1)) (i : Fin (n + 2)) : AffineSubspace ℝ P :=
  mk' (s.points i) (affineSpan ℝ (s.points '' ↑(univ.erase i))).directionᗮ ⊓
    affineSpan ℝ (Set.range s.points)

/-- The definition of an altitude. -/
theorem altitude_def {n : ℕ} (s : Simplex ℝ P (n + 1)) (i : Fin (n + 2)) :
    s.altitude i =
      mk' (s.points i) (affineSpan ℝ (s.points '' ↑(univ.erase i))).directionᗮ ⊓
        affineSpan ℝ (Set.range s.points) :=
  rfl

/-- A vertex lies in the corresponding altitude. -/
theorem mem_altitude {n : ℕ} (s : Simplex ℝ P (n + 1)) (i : Fin (n + 2)) :
    s.points i ∈ s.altitude i :=
  (mem_inf_iff _ _ _).2 ⟨self_mem_mk' _ _, mem_affineSpan ℝ (Set.mem_range_self _)⟩

/-- The direction of an altitude. -/
theorem direction_altitude {n : ℕ} (s : Simplex ℝ P (n + 1)) (i : Fin (n + 2)) :
    (s.altitude i).direction =
      (vectorSpan ℝ (s.points '' ↑(Finset.univ.erase i)))ᗮ ⊓ vectorSpan ℝ (Set.range s.points) := by
  rw [altitude_def,
    direction_inf_of_mem (self_mem_mk' (s.points i) _) (mem_affineSpan ℝ (Set.mem_range_self _)),
    direction_mk', direction_affineSpan, direction_affineSpan]

/-- The vector span of the opposite face lies in the direction
orthogonal to an altitude. -/
theorem vectorSpan_isOrtho_altitude_direction {n : ℕ} (s : Simplex ℝ P (n + 1)) (i : Fin (n + 2)) :
    vectorSpan ℝ (s.points '' ↑(Finset.univ.erase i)) ⟂ (s.altitude i).direction := by
  rw [direction_altitude]
  exact (Submodule.isOrtho_orthogonal_right _).mono_right inf_le_left

open Module

/-- An altitude is finite-dimensional. -/
instance finiteDimensional_direction_altitude {n : ℕ} (s : Simplex ℝ P (n + 1)) (i : Fin (n + 2)) :
    FiniteDimensional ℝ (s.altitude i).direction := by
  rw [direction_altitude]
  infer_instance

/-- An altitude is one-dimensional (i.e., a line). -/
@[simp]
theorem finrank_direction_altitude {n : ℕ} (s : Simplex ℝ P (n + 1)) (i : Fin (n + 2)) :
    finrank ℝ (s.altitude i).direction = 1 := by
  rw [direction_altitude]
  have h := Submodule.finrank_add_inf_finrank_orthogonal
    (vectorSpan_mono ℝ (Set.image_subset_range s.points ↑(univ.erase i)))
  have hc : #(univ.erase i) = n + 1 := by rw [card_erase_of_mem (mem_univ _)]; simp
  refine add_left_cancel (_root_.trans h ?_)
  classical
  rw [s.independent.finrank_vectorSpan (Fintype.card_fin _), ← Finset.coe_image,
    s.independent.finrank_vectorSpan_image_finset hc]

/-- A line through a vertex is the altitude through that vertex if and
only if it is orthogonal to the opposite face. -/
theorem affineSpan_pair_eq_altitude_iff {n : ℕ} (s : Simplex ℝ P (n + 1)) (i : Fin (n + 2))
    (p : P) :
    line[ℝ, p, s.points i] = s.altitude i ↔
      p ≠ s.points i ∧
        p ∈ affineSpan ℝ (Set.range s.points) ∧
          p -ᵥ s.points i ∈ (affineSpan ℝ (s.points '' ↑(Finset.univ.erase i))).directionᗮ := by
  rw [eq_iff_direction_eq_of_mem (mem_affineSpan ℝ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      (s.mem_altitude _),
    ← vsub_right_mem_direction_iff_mem (mem_affineSpan ℝ (Set.mem_range_self i)) p,
    direction_affineSpan, direction_affineSpan, direction_affineSpan]
  constructor
  · intro h
    constructor
    · intro heq
      rw [heq, Set.pair_eq_singleton, vectorSpan_singleton] at h
      have hd : finrank ℝ (s.altitude i).direction = 0 := by rw [← h, finrank_bot]
      simp at hd
    · rw [← Submodule.mem_inf, _root_.inf_comm, ← direction_altitude, ← h]
      exact
        vsub_mem_vectorSpan ℝ (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  · rintro ⟨hne, h⟩
    rw [← Submodule.mem_inf, _root_.inf_comm, ← direction_altitude] at h
    rw [vectorSpan_eq_span_vsub_set_left_ne ℝ (Set.mem_insert _ _),
      Set.insert_diff_of_mem _ (Set.mem_singleton _),
      Set.diff_singleton_eq_self fun h => hne (Set.mem_singleton_iff.1 h), Set.image_singleton]
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le]
      simpa using h
    · rw [finrank_direction_altitude, finrank_span_set_eq_card]
      · simp
      · exact LinearIndepOn.id_singleton _ <| by simpa using hne

/-- The foot of an altitude is the orthogonal projection of a vertex of a simplex onto the
opposite face. -/
def altitudeFoot {n : ℕ} [NeZero n] (s : Simplex ℝ P n) (i : Fin (n + 1)) : P :=
  (s.faceOpposite i).orthogonalProjectionSpan (s.points i)

@[simp] lemma ne_altitudeFoot {n : ℕ} [NeZero n] (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    s.points i ≠ s.altitudeFoot i := by
  intro h
  rw [eq_comm, altitudeFoot, orthogonalProjectionSpan, orthogonalProjection_eq_self_iff,
    mem_affineSpan_range_faceOpposite_points_iff] at h
  simp at h

lemma altitudeFoot_mem_affineSpan_faceOpposite {n : ℕ} [NeZero n] (s : Simplex ℝ P n)
    (i : Fin (n + 1)) : s.altitudeFoot i ∈ affineSpan ℝ (Set.range (s.faceOpposite i).points) :=
  orthogonalProjection_mem _

lemma altitudeFoot_mem_affineSpan {n : ℕ} [NeZero n] (s : Simplex ℝ P n)
    (i : Fin (n + 1)) : s.altitudeFoot i ∈ affineSpan ℝ (Set.range s.points) := by
  refine SetLike.le_def.1 (affineSpan_mono _ ?_) (s.altitudeFoot_mem_affineSpan_faceOpposite _)
  simp

lemma affineSpan_pair_altitudeFoot_eq_altitude {n : ℕ} (s : Simplex ℝ P (n + 1)) (i : Fin (n + 2)) :
    line[ℝ, s.altitudeFoot i, s.points i] = s.altitude i := by
  rw [affineSpan_pair_eq_altitude_iff]
  refine ⟨(s.ne_altitudeFoot i).symm, s.altitudeFoot_mem_affineSpan _, ?_⟩
  rw [altitudeFoot, orthogonalProjectionSpan]
  convert orthogonalProjection_vsub_mem_direction_orthogonal
    (affineSpan ℝ (Set.range (s.faceOpposite i).points)) _
  rw [range_faceOpposite_points]
  convert rfl using 2
  ext j
  simp

lemma altitudeFoot_mem_altitude {n : ℕ} (s : Simplex ℝ P (n + 1)) (i : Fin (n + 2)) :
    s.altitudeFoot i ∈ s.altitude i := by
  rw [← affineSpan_pair_altitudeFoot_eq_altitude]
  exact left_mem_affineSpan_pair _ _ _

/-- The height of a vertex of a simplex is the distance between it and the foot of the altitude
from that vertex. -/
def height {n : ℕ} [NeZero n] (s : Simplex ℝ P n) (i : Fin (n + 1)) : ℝ :=
  dist (s.points i) (s.altitudeFoot i)

lemma height_pos {n : ℕ} [NeZero n] (s : Simplex ℝ P n) (i : Fin (n + 1)) : 0 < s.height i := by
  simp [height]
open scoped RealInnerProductSpace

/-- The inner product of an edge from `j` to `i` and the vector from the foot of `i` to `i`
is the square of the height. -/
lemma inner_vsub_vsub_altitudeFoot_eq_height_sq
    {n : ℕ} [NeZero n] (s : Simplex ℝ P n) {i j : Fin (n + 1)} (h : i ≠ j)  :
    ⟪s.points i -ᵥ s.points j, s.points i -ᵥ s.altitudeFoot i⟫ = s.height i ^ 2 := by
  rw [height, inner_vsub_vsub_left_eq_dist_sq_right_iff, altitudeFoot]
  refine Submodule.inner_right_of_mem_orthogonal
        (K := vectorSpan ℝ (Set.range (s.faceOpposite i).points))
        (vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan
          (SetLike.coe_mem _)
          (mem_affineSpan ℝ ?_)) ?_
  · simp only [range_faceOpposite_points, ne_eq, Set.mem_image, Set.mem_setOf_eq]
    refine ⟨j, h.symm, rfl⟩
  · rw [← direction_affineSpan]
    exact vsub_orthogonalProjection_mem_direction_orthogonal _ _

end Simplex

end Affine
