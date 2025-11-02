/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Geometry.Euclidean.Projection
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
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
def altitude {n : ℕ} (s : Simplex ℝ P n) (i : Fin (n + 1)) : AffineSubspace ℝ P :=
  mk' (s.points i) (affineSpan ℝ (s.points '' {i}ᶜ)).directionᗮ ⊓
    affineSpan ℝ (Set.range s.points)

/-- The definition of an altitude. -/
theorem altitude_def {n : ℕ} (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    s.altitude i =
      mk' (s.points i) (affineSpan ℝ (s.points '' {i}ᶜ)).directionᗮ ⊓
        affineSpan ℝ (Set.range s.points) :=
  rfl

/-- A vertex lies in the corresponding altitude. -/
theorem mem_altitude {n : ℕ} (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    s.points i ∈ s.altitude i :=
  (mem_inf_iff _ _ _).2 ⟨self_mem_mk' _ _, mem_affineSpan ℝ (Set.mem_range_self _)⟩

/-- The direction of an altitude. -/
theorem direction_altitude {n : ℕ} (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    (s.altitude i).direction =
      (vectorSpan ℝ (s.points '' {i}ᶜ))ᗮ ⊓ vectorSpan ℝ (Set.range s.points) := by
  rw [altitude_def,
    direction_inf_of_mem (self_mem_mk' (s.points i) _) (mem_affineSpan ℝ (Set.mem_range_self _)),
    direction_mk', direction_affineSpan, direction_affineSpan]

/-- The vector span of the opposite face lies in the direction
orthogonal to an altitude. -/
theorem vectorSpan_isOrtho_altitude_direction {n : ℕ} (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    vectorSpan ℝ (s.points '' {i}ᶜ) ⟂ (s.altitude i).direction := by
  rw [direction_altitude]
  exact (Submodule.isOrtho_orthogonal_right _).mono_right inf_le_left

open Module

/-- An altitude is finite-dimensional. -/
instance finiteDimensional_direction_altitude {n : ℕ} (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    FiniteDimensional ℝ (s.altitude i).direction := by
  rw [direction_altitude]
  infer_instance

/-- An altitude is one-dimensional (i.e., a line). -/
@[simp]
theorem finrank_direction_altitude {n : ℕ} [NeZero n] (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    finrank ℝ (s.altitude i).direction = 1 := by
  rw [direction_altitude]
  have h := Submodule.finrank_add_inf_finrank_orthogonal
    (vectorSpan_mono ℝ (Set.image_subset_range s.points {i}ᶜ))
  have hn : (n - 1) + 1 = n := by
    have := NeZero.ne n
    cases n <;> omega
  have hc : #({i}ᶜ) = (n - 1) + 1 := by
    rw [card_compl, card_singleton, Fintype.card_fin, hn, add_tsub_cancel_right]
  refine add_left_cancel (_root_.trans h ?_)
  classical
  rw [s.independent.finrank_vectorSpan (Fintype.card_fin _), ← Finset.coe_singleton,
    ← Finset.coe_compl, ← Finset.coe_image,
    s.independent.finrank_vectorSpan_image_finset hc, hn]

/-- A line through a vertex is the altitude through that vertex if and
only if it is orthogonal to the opposite face. -/
theorem affineSpan_pair_eq_altitude_iff {n : ℕ} [NeZero n] (s : Simplex ℝ P n) (i : Fin (n + 1))
    (p : P) :
    line[ℝ, p, s.points i] = s.altitude i ↔
      p ≠ s.points i ∧
        p ∈ affineSpan ℝ (Set.range s.points) ∧
          p -ᵥ s.points i ∈ (affineSpan ℝ (s.points '' {i}ᶜ)).directionᗮ := by
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
  rw [eq_comm, altitudeFoot, orthogonalProjectionSpan, orthogonalProjection_eq_self_iff] at h
  simp at h

@[simp] lemma altitudeFoot_mem_affineSpan_image_compl {n : ℕ} [NeZero n] (s : Simplex ℝ P n)
    (i : Fin (n + 1)) : s.altitudeFoot i ∈ affineSpan ℝ (s.points '' {i}ᶜ) := by
  rw [← range_faceOpposite_points]
  exact orthogonalProjection_mem _

lemma altitudeFoot_mem_affineSpan_faceOpposite {n : ℕ} [NeZero n] (s : Simplex ℝ P n)
    (i : Fin (n + 1)) : s.altitudeFoot i ∈ affineSpan ℝ (Set.range (s.faceOpposite i).points) :=
  orthogonalProjection_mem _

lemma altitudeFoot_mem_affineSpan {n : ℕ} [NeZero n] (s : Simplex ℝ P n)
    (i : Fin (n + 1)) : s.altitudeFoot i ∈ affineSpan ℝ (Set.range s.points) := by
  refine SetLike.le_def.1 (affineSpan_mono _ ?_) (s.altitudeFoot_mem_affineSpan_faceOpposite _)
  simp

lemma affineSpan_pair_altitudeFoot_eq_altitude
    {n : ℕ} [NeZero n] (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    line[ℝ, s.altitudeFoot i, s.points i] = s.altitude i := by
  rw [affineSpan_pair_eq_altitude_iff]
  refine ⟨(s.ne_altitudeFoot i).symm, s.altitudeFoot_mem_affineSpan _, ?_⟩
  rw [altitudeFoot, orthogonalProjectionSpan]
  simp_rw [range_faceOpposite_points]
  exact orthogonalProjection_vsub_mem_direction_orthogonal _ _

lemma altitudeFoot_mem_altitude {n : ℕ} [NeZero n] (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    s.altitudeFoot i ∈ s.altitude i := by
  rw [← affineSpan_pair_altitudeFoot_eq_altitude]
  exact left_mem_affineSpan_pair _ _ _

/-- The height of a vertex of a simplex is the distance between it and the foot of the altitude
from that vertex. -/
def height {n : ℕ} [NeZero n] (s : Simplex ℝ P n) (i : Fin (n + 1)) : ℝ :=
  dist (s.points i) (s.altitudeFoot i)

@[simp]
lemma height_pos {n : ℕ} [NeZero n] (s : Simplex ℝ P n) (i : Fin (n + 1)) : 0 < s.height i := by
  simp [height]

open Qq Mathlib.Meta.Positivity in
/-- Extension for the `positivity` tactic: the height of a simplex is always positive. -/
@[positivity height _ _]
def evalHeight : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@height $V $P $i1 $i2 $i3 $i4 $n $hn $s $i) =>
    assertInstancesCommute
    return .positive q(height_pos $s $i)
  | _, _, _ => throwError "not Simplex.height"

example {n : ℕ} [NeZero n] (s : Simplex ℝ P n) (i : Fin (n + 1)) : 0 < s.height i := by
  positivity

open scoped RealInnerProductSpace

variable {n : ℕ} (s : Simplex ℝ P n)

/-- The inner product of an edge from `j` to `i` and the vector from the foot of `i` to `i`
is the square of the height. -/
lemma inner_vsub_vsub_altitudeFoot_eq_height_sq [NeZero n] {i j : Fin (n + 1)} (h : i ≠ j) :
    ⟪s.points i -ᵥ s.points j, s.points i -ᵥ s.altitudeFoot i⟫ = s.height i ^ 2 := by
  suffices ⟪s.points j -ᵥ s.altitudeFoot i, s.points i -ᵥ s.altitudeFoot i⟫ = 0 by
    rwa [height, inner_vsub_vsub_left_eq_dist_sq_right_iff, inner_vsub_left_eq_zero_symm]
  refine Submodule.inner_right_of_mem_orthogonal
      (K := vectorSpan ℝ (s.points '' {i}ᶜ))
      (vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan
        (s.mem_affineSpan_image_iff.2 h.symm)
        (altitudeFoot_mem_affineSpan_image_compl _ _))
      ?_
  rw [← direction_affineSpan, ← range_faceOpposite_points]
  exact vsub_orthogonalProjection_mem_direction_orthogonal _ _

variable [Nat.AtLeastTwo n]

/--
The inner product of two distinct altitudes has absolute value strictly less than the product of
their lengths.

Equivalently, neither vector is a multiple of the other; the angle between them is not 0 or π. -/
lemma abs_inner_vsub_altitudeFoot_lt_mul {i j : Fin (n + 1)} (hij : i ≠ j) :
    |⟪s.points i -ᵥ s.altitudeFoot i, s.points j -ᵥ s.altitudeFoot j⟫|
      < s.height i * s.height j := by
  apply lt_of_le_of_ne
  · convert abs_real_inner_le_norm _ _ using 1
    simp only [dist_eq_norm_vsub, height]
  · simp_rw [height, dist_eq_norm_vsub]
    rw [← Real.norm_eq_abs, ne_eq, norm_inner_eq_norm_iff (by simp) (by simp)]
    rintro ⟨r, hr, h⟩
    suffices s.points j -ᵥ s.altitudeFoot j = 0 by
      simp at this
    rw [← Submodule.mem_bot ℝ,
      ← Submodule.inf_orthogonal_eq_bot (vectorSpan ℝ (Set.range s.points))]
    refine ⟨vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan
      (mem_affineSpan _ (Set.mem_range_self _)) ?_, ?_⟩
    · refine SetLike.le_def.1 (affineSpan_mono _ ?_) (Subtype.property _)
      simp
    · rw [SetLike.mem_coe]
      have hk : ∃ k, k ≠ i ∧ k ≠ j := Fin.exists_ne_and_ne_of_two_lt i j
        (by linarith only [Nat.AtLeastTwo.one_lt (n := n)])
      have hs : vectorSpan ℝ (Set.range s.points) =
          vectorSpan ℝ (Set.range (s.faceOpposite i).points) ⊔
            vectorSpan ℝ (Set.range (s.faceOpposite j).points) := by
        rcases hk with ⟨k, hki, hkj⟩
        have hki' : s.points k ∈ Set.range (s.faceOpposite i).points := by
          rw [range_faceOpposite_points]
          exact Set.mem_image_of_mem _ hki
        have hkj' : s.points k ∈ Set.range (s.faceOpposite j).points := by
          rw [range_faceOpposite_points]
          exact Set.mem_image_of_mem _ hkj
        have hs :
            Set.range s.points =
              Set.range (s.faceOpposite i).points ∪ Set.range (s.faceOpposite j).points := by
          simp only [range_faceOpposite_points, ← Set.image_union]
          simp_rw [← Set.image_univ, ← Set.compl_inter]
          rw [Set.inter_singleton_eq_empty.mpr ?_, Set.compl_empty]
          simpa using hij.symm
        convert AffineSubspace.vectorSpan_union_of_mem_of_mem ℝ hki' hkj'
      rw [hs, ← Submodule.inf_orthogonal, Submodule.mem_inf]
      refine ⟨?_, ?_⟩
      · rw [h, ← direction_affineSpan]
        exact Submodule.smul_mem _ _ (vsub_orthogonalProjection_mem_direction_orthogonal _ _)
      · rw [← direction_affineSpan]
        exact vsub_orthogonalProjection_mem_direction_orthogonal _ _

/--
The inner product of two altitudes has value strictly greater than the negated product of
their lengths.
-/
lemma neg_mul_lt_inner_vsub_altitudeFoot (i j : Fin (n + 1)) :
    -(s.height i * s.height j)
      < ⟪s.points i -ᵥ s.altitudeFoot i, s.points j -ᵥ s.altitudeFoot j⟫ := by
  obtain rfl | hij := eq_or_ne i j
  · rw [real_inner_self_eq_norm_sq]
    refine lt_of_lt_of_le (b := 0) ?_ ?_
    · rw [neg_lt_zero]
      positivity
    · positivity
  rw [neg_lt]
  refine lt_of_abs_lt ?_
  rw [abs_neg]
  exact abs_inner_vsub_altitudeFoot_lt_mul s hij

lemma abs_inner_vsub_altitudeFoot_div_lt_one {i j : Fin (n + 1)} (hij : i ≠ j) :
    |⟪s.points i -ᵥ s.altitudeFoot i, s.points j -ᵥ s.altitudeFoot j⟫
            / (s.height i * s.height j)| < 1 := by
  rw [abs_div, div_lt_one (by simp [height])]
  nth_rw 2 [abs_eq_self.2]
  · exact abs_inner_vsub_altitudeFoot_lt_mul _ hij
  · simp only [height]
    positivity

lemma neg_one_lt_inner_vsub_altitudeFoot_div (s : Simplex ℝ P n) (i j : Fin (n + 1)) :
    -1 < ⟪s.points i -ᵥ s.altitudeFoot i, s.points j -ᵥ s.altitudeFoot j⟫
            / (s.height i * s.height j) := by
  rw [neg_lt, neg_div', div_lt_one (by simp [height]), neg_lt]
  exact neg_mul_lt_inner_vsub_altitudeFoot _ _ _

end Simplex

end Affine
