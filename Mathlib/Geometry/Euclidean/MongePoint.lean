/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers

! This file was ported from Lean 3 source module geometry.euclidean.monge_point
! leanprover-community/mathlib commit 1a4df69ca1a9a0e5e26bfe12e2b92814216016d0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Geometry.Euclidean.Circumcenter

/-!
# Monge point and orthocenter

This file defines the orthocenter of a triangle, via its n-dimensional
generalization, the Monge point of a simplex.

## Main definitions

* `monge_point` is the Monge point of a simplex, defined in terms of
  its position on the Euler line and then shown to be the point of
  concurrence of the Monge planes.

* `monge_plane` is a Monge plane of an (n+2)-simplex, which is the
  (n+1)-dimensional affine subspace of the subspace spanned by the
  simplex that passes through the centroid of an n-dimensional face
  and is orthogonal to the opposite edge (in 2 dimensions, this is the
  same as an altitude).

* `altitude` is the line that passes through a vertex of a simplex and
  is orthogonal to the opposite face.

* `orthocenter` is defined, for the case of a triangle, to be the same
  as its Monge point, then shown to be the point of concurrence of the
  altitudes.

* `orthocentric_system` is a predicate on sets of points that says
  whether they are four points, one of which is the orthocenter of the
  other three (in which case various other properties hold, including
  that each is the orthocenter of the other three).

## References

* <https://en.wikipedia.org/wiki/Altitude_(triangle)>
* <https://en.wikipedia.org/wiki/Monge_point>
* <https://en.wikipedia.org/wiki/Orthocentric_system>
* Małgorzata Buba-Brzozowa, [The Monge Point and the 3(n+1) Point
  Sphere of an
  n-Simplex](https://pdfs.semanticscholar.org/6f8b/0f623459c76dac2e49255737f8f0f4725d16.pdf)

-/


noncomputable section

open scoped BigOperators

open scoped Classical

open scoped RealInnerProductSpace

namespace Affine

namespace Simplex

open Finset AffineSubspace EuclideanGeometry PointsWithCircumcenterIndex

variable {V : Type _} {P : Type _} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- The Monge point of a simplex (in 2 or more dimensions) is a
generalization of the orthocenter of a triangle.  It is defined to be
the intersection of the Monge planes, where a Monge plane is the
(n-1)-dimensional affine subspace of the subspace spanned by the
simplex that passes through the centroid of an (n-2)-dimensional face
and is orthogonal to the opposite edge (in 2 dimensions, this is the
same as an altitude).  The circumcenter O, centroid G and Monge point
M are collinear in that order on the Euler line, with OG : GM = (n-1)
: 2.  Here, we use that ratio to define the Monge point (so resulting
in a point that equals the centroid in 0 or 1 dimensions), and then
show in subsequent lemmas that the point so defined lies in the Monge
planes and is their unique point of intersection. -/
def mongePoint {n : ℕ} (s : Simplex ℝ P n) : P :=
  (((n + 1 : ℕ) : ℝ) / ((n - 1 : ℕ) : ℝ)) •
      ((univ : Finset (Fin (n + 1))).centroid ℝ s.points -ᵥ s.circumcenter) +ᵥ
    s.circumcenter
#align affine.simplex.monge_point Affine.Simplex.mongePoint

/-- The position of the Monge point in relation to the circumcenter
and centroid. -/
theorem mongePoint_eq_smul_vsub_vadd_circumcenter {n : ℕ} (s : Simplex ℝ P n) :
    s.mongePoint =
      (((n + 1 : ℕ) : ℝ) / ((n - 1 : ℕ) : ℝ)) •
          ((univ : Finset (Fin (n + 1))).centroid ℝ s.points -ᵥ s.circumcenter) +ᵥ
        s.circumcenter :=
  rfl
#align affine.simplex.monge_point_eq_smul_vsub_vadd_circumcenter Affine.Simplex.mongePoint_eq_smul_vsub_vadd_circumcenter

/-- The Monge point lies in the affine span. -/
theorem mongePoint_mem_affineSpan {n : ℕ} (s : Simplex ℝ P n) :
    s.mongePoint ∈ affineSpan ℝ (Set.range s.points) :=
  smul_vsub_vadd_mem _ _ (centroid_mem_affineSpan_of_card_eq_add_one ℝ _ (card_fin (n + 1)))
    s.circumcenter_mem_affineSpan s.circumcenter_mem_affineSpan
#align affine.simplex.monge_point_mem_affine_span Affine.Simplex.mongePoint_mem_affineSpan

/-- Two simplices with the same points have the same Monge point. -/
theorem mongePoint_eq_of_range_eq {n : ℕ} {s₁ s₂ : Simplex ℝ P n}
    (h : Set.range s₁.points = Set.range s₂.points) : s₁.mongePoint = s₂.mongePoint := by
  simp_rw [monge_point_eq_smul_vsub_vadd_circumcenter, centroid_eq_of_range_eq h,
    circumcenter_eq_of_range_eq h]
#align affine.simplex.monge_point_eq_of_range_eq Affine.Simplex.mongePoint_eq_of_range_eq

/-- The weights for the Monge point of an (n+2)-simplex, in terms of
`points_with_circumcenter`. -/
def mongePointWeightsWithCircumcenter (n : ℕ) : PointsWithCircumcenterIndex (n + 2) → ℝ
  | point_index i => ((n + 1 : ℕ) : ℝ)⁻¹
  | circumcenter_index => -2 / ((n + 1 : ℕ) : ℝ)
#align affine.simplex.monge_point_weights_with_circumcenter Affine.Simplex.mongePointWeightsWithCircumcenter

/-- `monge_point_weights_with_circumcenter` sums to 1. -/
@[simp]
theorem sum_mongePointWeightsWithCircumcenter (n : ℕ) :
    ∑ i, mongePointWeightsWithCircumcenter n i = 1 :=
  by
  simp_rw [sum_points_with_circumcenter, monge_point_weights_with_circumcenter, sum_const, card_fin,
    nsmul_eq_mul]
  have hn1 : (n + 1 : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero _
  field_simp [hn1]
  ring
#align affine.simplex.sum_monge_point_weights_with_circumcenter Affine.Simplex.sum_mongePointWeightsWithCircumcenter

/-- The Monge point of an (n+2)-simplex, in terms of
`points_with_circumcenter`. -/
theorem mongePoint_eq_affineCombination_of_pointsWithCircumcenter {n : ℕ}
    (s : Simplex ℝ P (n + 2)) :
    s.mongePoint =
      (univ : Finset (PointsWithCircumcenterIndex (n + 2))).affineCombination ℝ
        s.pointsWithCircumcenter (mongePointWeightsWithCircumcenter n) :=
  by
  rw [monge_point_eq_smul_vsub_vadd_circumcenter,
    centroid_eq_affine_combination_of_points_with_circumcenter,
    circumcenter_eq_affine_combination_of_points_with_circumcenter, affine_combination_vsub, ←
    LinearMap.map_smul, weighted_vsub_vadd_affine_combination]
  congr with i
  rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
  have hn1 : (n + 1 : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero _
  cases i <;>
      simp_rw [centroid_weights_with_circumcenter, circumcenter_weights_with_circumcenter,
        monge_point_weights_with_circumcenter] <;>
    rw [add_tsub_assoc_of_le (by decide : 1 ≤ 2), (by decide : 2 - 1 = 1)]
  · rw [if_pos (mem_univ _), sub_zero, add_zero, card_fin]
    have hn3 : (n + 2 + 1 : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero _
    field_simp [hn1, hn3, mul_comm]
  · field_simp [hn1]
    ring
#align affine.simplex.monge_point_eq_affine_combination_of_points_with_circumcenter Affine.Simplex.mongePoint_eq_affineCombination_of_pointsWithCircumcenter

/-- The weights for the Monge point of an (n+2)-simplex, minus the
centroid of an n-dimensional face, in terms of
`points_with_circumcenter`.  This definition is only valid when `i₁ ≠ i₂`. -/
def mongePointVsubFaceCentroidWeightsWithCircumcenter {n : ℕ} (i₁ i₂ : Fin (n + 3)) :
    PointsWithCircumcenterIndex (n + 2) → ℝ
  | point_index i => if i = i₁ ∨ i = i₂ then ((n + 1 : ℕ) : ℝ)⁻¹ else 0
  | circumcenter_index => -2 / ((n + 1 : ℕ) : ℝ)
#align affine.simplex.monge_point_vsub_face_centroid_weights_with_circumcenter Affine.Simplex.mongePointVsubFaceCentroidWeightsWithCircumcenter

/-- `monge_point_vsub_face_centroid_weights_with_circumcenter` is the
result of subtracting `centroid_weights_with_circumcenter` from
`monge_point_weights_with_circumcenter`. -/
theorem mongePointVsubFaceCentroidWeightsWithCircumcenter_eq_sub {n : ℕ} {i₁ i₂ : Fin (n + 3)}
    (h : i₁ ≠ i₂) :
    mongePointVsubFaceCentroidWeightsWithCircumcenter i₁ i₂ =
      mongePointWeightsWithCircumcenter n - centroidWeightsWithCircumcenter ({i₁, i₂}ᶜ) :=
  by
  ext i
  cases i
  · rw [Pi.sub_apply, monge_point_weights_with_circumcenter, centroid_weights_with_circumcenter,
      monge_point_vsub_face_centroid_weights_with_circumcenter]
    have hu : card ({i₁, i₂}ᶜ : Finset (Fin (n + 3))) = n + 1 := by
      simp [card_compl, Fintype.card_fin, h]
    rw [hu]
    by_cases hi : i = i₁ ∨ i = i₂ <;> simp [compl_eq_univ_sdiff, hi]
  ·
    simp [monge_point_weights_with_circumcenter, centroid_weights_with_circumcenter,
      monge_point_vsub_face_centroid_weights_with_circumcenter]
#align affine.simplex.monge_point_vsub_face_centroid_weights_with_circumcenter_eq_sub Affine.Simplex.mongePointVsubFaceCentroidWeightsWithCircumcenter_eq_sub

/-- `monge_point_vsub_face_centroid_weights_with_circumcenter` sums to 0. -/
@[simp]
theorem sum_mongePointVsubFaceCentroidWeightsWithCircumcenter {n : ℕ} {i₁ i₂ : Fin (n + 3)}
    (h : i₁ ≠ i₂) : ∑ i, mongePointVsubFaceCentroidWeightsWithCircumcenter i₁ i₂ i = 0 :=
  by
  rw [monge_point_vsub_face_centroid_weights_with_circumcenter_eq_sub h]
  simp_rw [Pi.sub_apply, sum_sub_distrib, sum_monge_point_weights_with_circumcenter]
  rw [sum_centroid_weights_with_circumcenter, sub_self]
  simp [← card_pos, card_compl, h]
#align affine.simplex.sum_monge_point_vsub_face_centroid_weights_with_circumcenter Affine.Simplex.sum_mongePointVsubFaceCentroidWeightsWithCircumcenter

/-- The Monge point of an (n+2)-simplex, minus the centroid of an
n-dimensional face, in terms of `points_with_circumcenter`. -/
theorem mongePoint_vsub_face_centroid_eq_weightedVSub_of_pointsWithCircumcenter {n : ℕ}
    (s : Simplex ℝ P (n + 2)) {i₁ i₂ : Fin (n + 3)} (h : i₁ ≠ i₂) :
    s.mongePoint -ᵥ ({i₁, i₂}ᶜ : Finset (Fin (n + 3))).centroid ℝ s.points =
      (univ : Finset (PointsWithCircumcenterIndex (n + 2))).weightedVSub s.pointsWithCircumcenter
        (mongePointVsubFaceCentroidWeightsWithCircumcenter i₁ i₂) :=
  by
  simp_rw [monge_point_eq_affine_combination_of_points_with_circumcenter,
    centroid_eq_affine_combination_of_points_with_circumcenter, affine_combination_vsub,
    monge_point_vsub_face_centroid_weights_with_circumcenter_eq_sub h]
#align affine.simplex.monge_point_vsub_face_centroid_eq_weighted_vsub_of_points_with_circumcenter Affine.Simplex.mongePoint_vsub_face_centroid_eq_weightedVSub_of_pointsWithCircumcenter

/-- The Monge point of an (n+2)-simplex, minus the centroid of an
n-dimensional face, is orthogonal to the difference of the two
vertices not in that face. -/
theorem inner_mongePoint_vsub_face_centroid_vsub {n : ℕ} (s : Simplex ℝ P (n + 2))
    {i₁ i₂ : Fin (n + 3)} :
    ⟪s.mongePoint -ᵥ ({i₁, i₂}ᶜ : Finset (Fin (n + 3))).centroid ℝ s.points,
        s.points i₁ -ᵥ s.points i₂⟫ =
      0 :=
  by
  by_cases h : i₁ = i₂
  · simp [h]
  simp_rw [monge_point_vsub_face_centroid_eq_weighted_vsub_of_points_with_circumcenter s h,
    point_eq_affine_combination_of_points_with_circumcenter, affine_combination_vsub]
  have hs : ∑ i, (point_weights_with_circumcenter i₁ - point_weights_with_circumcenter i₂) i = 0 :=
    by simp
  rw [inner_weighted_vsub _ (sum_monge_point_vsub_face_centroid_weights_with_circumcenter h) _ hs,
    sum_points_with_circumcenter, points_with_circumcenter_eq_circumcenter]
  simp only [monge_point_vsub_face_centroid_weights_with_circumcenter,
    points_with_circumcenter_point]
  let fs : Finset (Fin (n + 3)) := {i₁, i₂}
  have hfs : ∀ i : Fin (n + 3), i ∉ fs → i ≠ i₁ ∧ i ≠ i₂ :=
    by
    intro i hi
    constructor <;> · intro hj; simpa [← hj] using hi
  rw [← sum_subset fs.subset_univ _]
  · simp_rw [sum_points_with_circumcenter, points_with_circumcenter_eq_circumcenter,
      points_with_circumcenter_point, Pi.sub_apply, point_weights_with_circumcenter]
    rw [← sum_subset fs.subset_univ _]
    · simp_rw [sum_insert (not_mem_singleton.2 h), sum_singleton]
      repeat' rw [← sum_subset fs.subset_univ _]
      · simp_rw [sum_insert (not_mem_singleton.2 h), sum_singleton]
        simp [h, Ne.symm h, dist_comm (s.points i₁)]
      all_goals intro i hu hi; simp [hfs i hi]
    · intro i hu hi
      simp [hfs i hi, point_weights_with_circumcenter]
  · intro i hu hi
    simp [hfs i hi]
#align affine.simplex.inner_monge_point_vsub_face_centroid_vsub Affine.Simplex.inner_mongePoint_vsub_face_centroid_vsub

/-- A Monge plane of an (n+2)-simplex is the (n+1)-dimensional affine
subspace of the subspace spanned by the simplex that passes through
the centroid of an n-dimensional face and is orthogonal to the
opposite edge (in 2 dimensions, this is the same as an altitude).
This definition is only intended to be used when `i₁ ≠ i₂`. -/
def mongePlane {n : ℕ} (s : Simplex ℝ P (n + 2)) (i₁ i₂ : Fin (n + 3)) : AffineSubspace ℝ P :=
  mk' (({i₁, i₂}ᶜ : Finset (Fin (n + 3))).centroid ℝ s.points) (ℝ ∙ s.points i₁ -ᵥ s.points i₂)ᗮ ⊓
    affineSpan ℝ (Set.range s.points)
#align affine.simplex.monge_plane Affine.Simplex.mongePlane

/-- The definition of a Monge plane. -/
theorem mongePlane_def {n : ℕ} (s : Simplex ℝ P (n + 2)) (i₁ i₂ : Fin (n + 3)) :
    s.mongePlane i₁ i₂ =
      mk' (({i₁, i₂}ᶜ : Finset (Fin (n + 3))).centroid ℝ s.points)
          (ℝ ∙ s.points i₁ -ᵥ s.points i₂)ᗮ ⊓
        affineSpan ℝ (Set.range s.points) :=
  rfl
#align affine.simplex.monge_plane_def Affine.Simplex.mongePlane_def

/-- The Monge plane associated with vertices `i₁` and `i₂` equals that
associated with `i₂` and `i₁`. -/
theorem mongePlane_comm {n : ℕ} (s : Simplex ℝ P (n + 2)) (i₁ i₂ : Fin (n + 3)) :
    s.mongePlane i₁ i₂ = s.mongePlane i₂ i₁ :=
  by
  simp_rw [monge_plane_def]
  congr 3
  · congr 1
    exact pair_comm _ _
  · ext
    simp_rw [Submodule.mem_span_singleton]
    constructor
    all_goals rintro ⟨r, rfl⟩; use -r; rw [neg_smul, ← smul_neg, neg_vsub_eq_vsub_rev]
#align affine.simplex.monge_plane_comm Affine.Simplex.mongePlane_comm

/-- The Monge point lies in the Monge planes. -/
theorem mongePoint_mem_mongePlane {n : ℕ} (s : Simplex ℝ P (n + 2)) {i₁ i₂ : Fin (n + 3)} :
    s.mongePoint ∈ s.mongePlane i₁ i₂ :=
  by
  rw [monge_plane_def, mem_inf_iff, ← vsub_right_mem_direction_iff_mem (self_mem_mk' _ _),
    direction_mk', Submodule.mem_orthogonal']
  refine' ⟨_, s.monge_point_mem_affine_span⟩
  intro v hv
  rcases submodule.mem_span_singleton.mp hv with ⟨r, rfl⟩
  rw [inner_smul_right, s.inner_monge_point_vsub_face_centroid_vsub, MulZeroClass.mul_zero]
#align affine.simplex.monge_point_mem_monge_plane Affine.Simplex.mongePoint_mem_mongePlane

/-- The direction of a Monge plane. -/
theorem direction_mongePlane {n : ℕ} (s : Simplex ℝ P (n + 2)) {i₁ i₂ : Fin (n + 3)} :
    (s.mongePlane i₁ i₂).direction =
      (ℝ ∙ s.points i₁ -ᵥ s.points i₂)ᗮ ⊓ vectorSpan ℝ (Set.range s.points) :=
  by
  rw [monge_plane_def, direction_inf_of_mem_inf s.monge_point_mem_monge_plane, direction_mk',
    direction_affineSpan]
#align affine.simplex.direction_monge_plane Affine.Simplex.direction_mongePlane

/-- The Monge point is the only point in all the Monge planes from any
one vertex. -/
theorem eq_mongePoint_of_forall_mem_mongePlane {n : ℕ} {s : Simplex ℝ P (n + 2)} {i₁ : Fin (n + 3)}
    {p : P} (h : ∀ i₂, i₁ ≠ i₂ → p ∈ s.mongePlane i₁ i₂) : p = s.mongePoint :=
  by
  rw [← @vsub_eq_zero_iff_eq V]
  have h' :
    ∀ i₂,
      i₁ ≠ i₂ →
        p -ᵥ s.monge_point ∈
          (ℝ ∙ s.points i₁ -ᵥ s.points i₂)ᗮ ⊓ vectorSpan ℝ (Set.range s.points) :=
    by
    intro i₂ hne
    rw [← s.direction_monge_plane, vsub_right_mem_direction_iff_mem s.monge_point_mem_monge_plane]
    exact h i₂ hne
  have hi : p -ᵥ s.monge_point ∈ ⨅ i₂ : { i // i₁ ≠ i }, (ℝ ∙ s.points i₁ -ᵥ s.points i₂)ᗮ :=
    by
    rw [Submodule.mem_iInf]
    exact fun i => (Submodule.mem_inf.1 (h' i i.property)).1
  rw [Submodule.iInf_orthogonal, ← Submodule.span_iUnion] at hi 
  have hu :
    (⋃ i : { i // i₁ ≠ i }, ({s.points i₁ -ᵥ s.points i} : Set V)) =
      (· -ᵥ ·) (s.points i₁) '' (s.points '' (Set.univ \ {i₁})) :=
    by
    rw [Set.image_image]
    ext x
    simp_rw [Set.mem_iUnion, Set.mem_image, Set.mem_singleton_iff, Set.mem_diff_singleton]
    constructor
    · rintro ⟨i, rfl⟩
      use i, ⟨Set.mem_univ _, i.property.symm⟩
    · rintro ⟨i, ⟨hiu, hi⟩, rfl⟩
      use ⟨i, hi.symm⟩, rfl
  rw [hu, ← vectorSpan_image_eq_span_vsub_set_left_ne ℝ _ (Set.mem_univ _), Set.image_univ] at hi 
  have hv : p -ᵥ s.monge_point ∈ vectorSpan ℝ (Set.range s.points) :=
    by
    let s₁ : Finset (Fin (n + 3)) := univ.erase i₁
    obtain ⟨i₂, h₂⟩ := card_pos.1 (show 0 < card s₁ by simp [card_erase_of_mem])
    have h₁₂ : i₁ ≠ i₂ := (ne_of_mem_erase h₂).symm
    exact (Submodule.mem_inf.1 (h' i₂ h₁₂)).2
  exact Submodule.disjoint_def.1 (vectorSpan ℝ (Set.range s.points)).orthogonal_disjoint _ hv hi
#align affine.simplex.eq_monge_point_of_forall_mem_monge_plane Affine.Simplex.eq_mongePoint_of_forall_mem_mongePlane

/-- An altitude of a simplex is the line that passes through a vertex
and is orthogonal to the opposite face. -/
def altitude {n : ℕ} (s : Simplex ℝ P (n + 1)) (i : Fin (n + 2)) : AffineSubspace ℝ P :=
  mk' (s.points i) (affineSpan ℝ (s.points '' ↑(univ.eraseₓ i))).directionᗮ ⊓
    affineSpan ℝ (Set.range s.points)
#align affine.simplex.altitude Affine.Simplex.altitude

/-- The definition of an altitude. -/
theorem altitude_def {n : ℕ} (s : Simplex ℝ P (n + 1)) (i : Fin (n + 2)) :
    s.altitude i =
      mk' (s.points i) (affineSpan ℝ (s.points '' ↑(univ.eraseₓ i))).directionᗮ ⊓
        affineSpan ℝ (Set.range s.points) :=
  rfl
#align affine.simplex.altitude_def Affine.Simplex.altitude_def

/-- A vertex lies in the corresponding altitude. -/
theorem mem_altitude {n : ℕ} (s : Simplex ℝ P (n + 1)) (i : Fin (n + 2)) :
    s.points i ∈ s.altitude i :=
  (mem_inf_iff _ _ _).2 ⟨self_mem_mk' _ _, mem_affineSpan ℝ (Set.mem_range_self _)⟩
#align affine.simplex.mem_altitude Affine.Simplex.mem_altitude

/-- The direction of an altitude. -/
theorem direction_altitude {n : ℕ} (s : Simplex ℝ P (n + 1)) (i : Fin (n + 2)) :
    (s.altitude i).direction =
      (vectorSpan ℝ (s.points '' ↑(Finset.univ.eraseₓ i)))ᗮ ⊓ vectorSpan ℝ (Set.range s.points) :=
  by
  rw [altitude_def,
    direction_inf_of_mem (self_mem_mk' (s.points i) _) (mem_affineSpan ℝ (Set.mem_range_self _)),
    direction_mk', direction_affineSpan, direction_affineSpan]
#align affine.simplex.direction_altitude Affine.Simplex.direction_altitude

/-- The vector span of the opposite face lies in the direction
orthogonal to an altitude. -/
theorem vectorSpan_isOrtho_altitude_direction {n : ℕ} (s : Simplex ℝ P (n + 1)) (i : Fin (n + 2)) :
    vectorSpan ℝ (s.points '' ↑(Finset.univ.eraseₓ i)) ⟂ (s.altitude i).direction :=
  by
  rw [direction_altitude]
  exact (Submodule.isOrtho_orthogonal_right _).mono_right inf_le_left
#align affine.simplex.vector_span_is_ortho_altitude_direction Affine.Simplex.vectorSpan_isOrtho_altitude_direction

open FiniteDimensional

/-- An altitude is finite-dimensional. -/
instance finiteDimensional_direction_altitude {n : ℕ} (s : Simplex ℝ P (n + 1)) (i : Fin (n + 2)) :
    FiniteDimensional ℝ (s.altitude i).direction :=
  by
  rw [direction_altitude]
  infer_instance
#align affine.simplex.finite_dimensional_direction_altitude Affine.Simplex.finiteDimensional_direction_altitude

/-- An altitude is one-dimensional (i.e., a line). -/
@[simp]
theorem finrank_direction_altitude {n : ℕ} (s : Simplex ℝ P (n + 1)) (i : Fin (n + 2)) :
    finrank ℝ (s.altitude i).direction = 1 :=
  by
  rw [direction_altitude]
  have h :=
    Submodule.finrank_add_inf_finrank_orthogonal
      (vectorSpan_mono ℝ (Set.image_subset_range s.points ↑(univ.erase i)))
  have hc : card (univ.erase i) = n + 1 := by rw [card_erase_of_mem (mem_univ _)]; simp
  refine' add_left_cancel (trans h _)
  rw [s.independent.finrank_vector_span (Fintype.card_fin _), ← Finset.coe_image,
    s.independent.finrank_vector_span_image_finset hc]
#align affine.simplex.finrank_direction_altitude Affine.Simplex.finrank_direction_altitude

/-- A line through a vertex is the altitude through that vertex if and
only if it is orthogonal to the opposite face. -/
theorem affineSpan_pair_eq_altitude_iff {n : ℕ} (s : Simplex ℝ P (n + 1)) (i : Fin (n + 2))
    (p : P) :
    line[ℝ, p, s.points i] = s.altitude i ↔
      p ≠ s.points i ∧
        p ∈ affineSpan ℝ (Set.range s.points) ∧
          p -ᵥ s.points i ∈ (affineSpan ℝ (s.points '' ↑(Finset.univ.eraseₓ i))).directionᗮ :=
  by
  rw [eq_iff_direction_eq_of_mem (mem_affineSpan ℝ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      (s.mem_altitude _),
    ← vsub_right_mem_direction_iff_mem (mem_affineSpan ℝ (Set.mem_range_self i)) p,
    direction_affineSpan, direction_affineSpan, direction_affineSpan]
  constructor
  · intro h
    constructor
    · intro heq
      rw [HEq, Set.pair_eq_singleton, vectorSpan_singleton] at h 
      have hd : finrank ℝ (s.altitude i).direction = 0 := by rw [← h, finrank_bot]
      simpa using hd
    · rw [← Submodule.mem_inf, _root_.inf_comm, ← direction_altitude, ← h]
      exact
        vsub_mem_vectorSpan ℝ (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  · rintro ⟨hne, h⟩
    rw [← Submodule.mem_inf, _root_.inf_comm, ← direction_altitude] at h 
    rw [vectorSpan_eq_span_vsub_set_left_ne ℝ (Set.mem_insert _ _),
      Set.insert_diff_of_mem _ (Set.mem_singleton _),
      Set.diff_singleton_eq_self fun h => hne (Set.mem_singleton_iff.1 h), Set.image_singleton]
    refine' eq_of_le_of_finrank_eq _ _
    · rw [Submodule.span_le]
      simpa using h
    · rw [finrank_direction_altitude, finrank_span_set_eq_card]
      · simp
      · refine' linearIndependent_singleton _
        simpa using hne
#align affine.simplex.affine_span_pair_eq_altitude_iff Affine.Simplex.affineSpan_pair_eq_altitude_iff

end Simplex

namespace Triangle

open EuclideanGeometry Finset Simplex AffineSubspace FiniteDimensional

variable {V : Type _} {P : Type _} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- The orthocenter of a triangle is the intersection of its
altitudes.  It is defined here as the 2-dimensional case of the
Monge point. -/
def orthocenter (t : Triangle ℝ P) : P :=
  t.mongePoint
#align affine.triangle.orthocenter Affine.Triangle.orthocenter

/-- The orthocenter equals the Monge point. -/
theorem orthocenter_eq_mongePoint (t : Triangle ℝ P) : t.orthocenter = t.mongePoint :=
  rfl
#align affine.triangle.orthocenter_eq_monge_point Affine.Triangle.orthocenter_eq_mongePoint

/-- The position of the orthocenter in relation to the circumcenter
and centroid. -/
theorem orthocenter_eq_smul_vsub_vadd_circumcenter (t : Triangle ℝ P) :
    t.orthocenter =
      (3 : ℝ) • ((univ : Finset (Fin 3)).centroid ℝ t.points -ᵥ t.circumcenter : V) +ᵥ
        t.circumcenter :=
  by
  rw [orthocenter_eq_monge_point, monge_point_eq_smul_vsub_vadd_circumcenter]
  norm_num
#align affine.triangle.orthocenter_eq_smul_vsub_vadd_circumcenter Affine.Triangle.orthocenter_eq_smul_vsub_vadd_circumcenter

/-- The orthocenter lies in the affine span. -/
theorem orthocenter_mem_affineSpan (t : Triangle ℝ P) :
    t.orthocenter ∈ affineSpan ℝ (Set.range t.points) :=
  t.mongePoint_mem_affineSpan
#align affine.triangle.orthocenter_mem_affine_span Affine.Triangle.orthocenter_mem_affineSpan

/-- Two triangles with the same points have the same orthocenter. -/
theorem orthocenter_eq_of_range_eq {t₁ t₂ : Triangle ℝ P}
    (h : Set.range t₁.points = Set.range t₂.points) : t₁.orthocenter = t₂.orthocenter :=
  mongePoint_eq_of_range_eq h
#align affine.triangle.orthocenter_eq_of_range_eq Affine.Triangle.orthocenter_eq_of_range_eq

/-- In the case of a triangle, altitudes are the same thing as Monge
planes. -/
theorem altitude_eq_mongePlane (t : Triangle ℝ P) {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃)
    (h₂₃ : i₂ ≠ i₃) : t.altitude i₁ = t.mongePlane i₂ i₃ :=
  by
  have hs : ({i₂, i₃}ᶜ : Finset (Fin 3)) = {i₁} := by decide!
  have he : univ.erase i₁ = {i₂, i₃} := by decide!
  rw [monge_plane_def, altitude_def, direction_affineSpan, hs, he, centroid_singleton, coe_insert,
    coe_singleton, vectorSpan_image_eq_span_vsub_set_left_ne ℝ _ (Set.mem_insert i₂ _)]
  simp [h₂₃, Submodule.span_insert_eq_span]
#align affine.triangle.altitude_eq_monge_plane Affine.Triangle.altitude_eq_mongePlane

/-- The orthocenter lies in the altitudes. -/
theorem orthocenter_mem_altitude (t : Triangle ℝ P) {i₁ : Fin 3} : t.orthocenter ∈ t.altitude i₁ :=
  by
  obtain ⟨i₂, i₃, h₁₂, h₂₃, h₁₃⟩ : ∃ i₂ i₃, i₁ ≠ i₂ ∧ i₂ ≠ i₃ ∧ i₁ ≠ i₃ := by decide!
  rw [orthocenter_eq_monge_point, t.altitude_eq_monge_plane h₁₂ h₁₃ h₂₃]
  exact t.monge_point_mem_monge_plane
#align affine.triangle.orthocenter_mem_altitude Affine.Triangle.orthocenter_mem_altitude

/-- The orthocenter is the only point lying in any two of the
altitudes. -/
theorem eq_orthocenter_of_forall_mem_altitude {t : Triangle ℝ P} {i₁ i₂ : Fin 3} {p : P}
    (h₁₂ : i₁ ≠ i₂) (h₁ : p ∈ t.altitude i₁) (h₂ : p ∈ t.altitude i₂) : p = t.orthocenter :=
  by
  obtain ⟨i₃, h₂₃, h₁₃⟩ : ∃ i₃, i₂ ≠ i₃ ∧ i₁ ≠ i₃ := by clear h₁ h₂; decide!
  rw [t.altitude_eq_monge_plane h₁₃ h₁₂ h₂₃.symm] at h₁ 
  rw [t.altitude_eq_monge_plane h₂₃ h₁₂.symm h₁₃.symm] at h₂ 
  rw [orthocenter_eq_monge_point]
  have ha : ∀ i, i₃ ≠ i → p ∈ t.monge_plane i₃ i :=
    by
    intro i hi
    have hi₁₂ : i₁ = i ∨ i₂ = i := by clear h₁ h₂; decide!
    cases hi₁₂
    · exact hi₁₂ ▸ h₂
    · exact hi₁₂ ▸ h₁
  exact eq_monge_point_of_forall_mem_monge_plane ha
#align affine.triangle.eq_orthocenter_of_forall_mem_altitude Affine.Triangle.eq_orthocenter_of_forall_mem_altitude

/-- The distance from the orthocenter to the reflection of the
circumcenter in a side equals the circumradius. -/
theorem dist_orthocenter_reflection_circumcenter (t : Triangle ℝ P) {i₁ i₂ : Fin 3} (h : i₁ ≠ i₂) :
    dist t.orthocenter (reflection (affineSpan ℝ (t.points '' {i₁, i₂})) t.circumcenter) =
      t.circumradius :=
  by
  rw [← mul_self_inj_of_nonneg dist_nonneg t.circumradius_nonneg,
    t.reflection_circumcenter_eq_affine_combination_of_points_with_circumcenter h,
    t.orthocenter_eq_monge_point, monge_point_eq_affine_combination_of_points_with_circumcenter,
    dist_affine_combination t.points_with_circumcenter (sum_monge_point_weights_with_circumcenter _)
      (sum_reflection_circumcenter_weights_with_circumcenter h)]
  simp_rw [sum_points_with_circumcenter, Pi.sub_apply, monge_point_weights_with_circumcenter,
    reflection_circumcenter_weights_with_circumcenter]
  have hu : ({i₁, i₂} : Finset (Fin 3)) ⊆ univ := subset_univ _
  obtain ⟨i₃, hi₃, hi₃₁, hi₃₂⟩ :
    ∃ i₃, univ \ ({i₁, i₂} : Finset (Fin 3)) = {i₃} ∧ i₃ ≠ i₁ ∧ i₃ ≠ i₂ := by decide!
  simp_rw [← sum_sdiff hu, hi₃]
  simp [hi₃₁, hi₃₂]
  norm_num
#align affine.triangle.dist_orthocenter_reflection_circumcenter Affine.Triangle.dist_orthocenter_reflection_circumcenter

/-- The distance from the orthocenter to the reflection of the
circumcenter in a side equals the circumradius, variant using a
`finset`. -/
theorem dist_orthocenter_reflection_circumcenter_finset (t : Triangle ℝ P) {i₁ i₂ : Fin 3}
    (h : i₁ ≠ i₂) :
    dist t.orthocenter
        (reflection (affineSpan ℝ (t.points '' ↑({i₁, i₂} : Finset (Fin 3)))) t.circumcenter) =
      t.circumradius :=
  by convert dist_orthocenter_reflection_circumcenter _ h; simp
#align affine.triangle.dist_orthocenter_reflection_circumcenter_finset Affine.Triangle.dist_orthocenter_reflection_circumcenter_finset

/-- The affine span of the orthocenter and a vertex is contained in
the altitude. -/
theorem affineSpan_orthocenter_point_le_altitude (t : Triangle ℝ P) (i : Fin 3) :
    line[ℝ, t.orthocenter, t.points i] ≤ t.altitude i :=
  by
  refine' span_points_subset_coe_of_subset_coe _
  rw [Set.insert_subset_iff, Set.singleton_subset_iff]
  exact ⟨t.orthocenter_mem_altitude, t.mem_altitude i⟩
#align affine.triangle.affine_span_orthocenter_point_le_altitude Affine.Triangle.affineSpan_orthocenter_point_le_altitude

/-- Suppose we are given a triangle `t₁`, and replace one of its
vertices by its orthocenter, yielding triangle `t₂` (with vertices not
necessarily listed in the same order).  Then an altitude of `t₂` from
a vertex that was not replaced is the corresponding side of `t₁`. -/
theorem altitude_replace_orthocenter_eq_affineSpan {t₁ t₂ : Triangle ℝ P}
    {i₁ i₂ i₃ j₁ j₂ j₃ : Fin 3} (hi₁₂ : i₁ ≠ i₂) (hi₁₃ : i₁ ≠ i₃) (hi₂₃ : i₂ ≠ i₃) (hj₁₂ : j₁ ≠ j₂)
    (hj₁₃ : j₁ ≠ j₃) (hj₂₃ : j₂ ≠ j₃) (h₁ : t₂.points j₁ = t₁.orthocenter)
    (h₂ : t₂.points j₂ = t₁.points i₂) (h₃ : t₂.points j₃ = t₁.points i₃) :
    t₂.altitude j₂ = line[ℝ, t₁.points i₁, t₁.points i₂] :=
  by
  symm
  rw [← h₂, t₂.affine_span_pair_eq_altitude_iff]
  rw [h₂]
  use t₁.independent.injective.ne hi₁₂
  have he : affineSpan ℝ (Set.range t₂.points) = affineSpan ℝ (Set.range t₁.points) :=
    by
    refine'
      ext_of_direction_eq _
        ⟨t₁.points i₃, mem_affineSpan ℝ ⟨j₃, h₃⟩, mem_affineSpan ℝ (Set.mem_range_self _)⟩
    refine' eq_of_le_of_finrank_eq (direction_le (span_points_subset_coe_of_subset_coe _)) _
    · have hu : (Finset.univ : Finset (Fin 3)) = {j₁, j₂, j₃} := by clear h₁ h₂ h₃; decide!
      rw [← Set.image_univ, ← Finset.coe_univ, hu, Finset.coe_insert, Finset.coe_insert,
        Finset.coe_singleton, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton, h₁, h₂,
        h₃, Set.insert_subset_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact
        ⟨t₁.orthocenter_mem_affine_span, mem_affineSpan ℝ (Set.mem_range_self _),
          mem_affineSpan ℝ (Set.mem_range_self _)⟩
    ·
      rw [direction_affineSpan, direction_affineSpan,
        t₁.independent.finrank_vector_span (Fintype.card_fin _),
        t₂.independent.finrank_vector_span (Fintype.card_fin _)]
  rw [he]
  use mem_affineSpan ℝ (Set.mem_range_self _)
  have hu : finset.univ.erase j₂ = {j₁, j₃} := by clear h₁ h₂ h₃; decide!
  rw [hu, Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq, Set.image_singleton, h₁, h₃]
  have hle : (t₁.altitude i₃).directionᗮ ≤ line[ℝ, t₁.orthocenter, t₁.points i₃].directionᗮ :=
    Submodule.orthogonal_le (direction_le (affine_span_orthocenter_point_le_altitude _ _))
  refine' hle ((t₁.vector_span_is_ortho_altitude_direction i₃) _)
  have hui : finset.univ.erase i₃ = {i₁, i₂} := by clear hle h₂ h₃; decide!
  rw [hui, Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq, Set.image_singleton]
  refine' vsub_mem_vectorSpan ℝ (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_singleton _))
#align affine.triangle.altitude_replace_orthocenter_eq_affine_span Affine.Triangle.altitude_replace_orthocenter_eq_affineSpan

/-- Suppose we are given a triangle `t₁`, and replace one of its
vertices by its orthocenter, yielding triangle `t₂` (with vertices not
necessarily listed in the same order).  Then the orthocenter of `t₂`
is the vertex of `t₁` that was replaced. -/
theorem orthocenter_replace_orthocenter_eq_point {t₁ t₂ : Triangle ℝ P} {i₁ i₂ i₃ j₁ j₂ j₃ : Fin 3}
    (hi₁₂ : i₁ ≠ i₂) (hi₁₃ : i₁ ≠ i₃) (hi₂₃ : i₂ ≠ i₃) (hj₁₂ : j₁ ≠ j₂) (hj₁₃ : j₁ ≠ j₃)
    (hj₂₃ : j₂ ≠ j₃) (h₁ : t₂.points j₁ = t₁.orthocenter) (h₂ : t₂.points j₂ = t₁.points i₂)
    (h₃ : t₂.points j₃ = t₁.points i₃) : t₂.orthocenter = t₁.points i₁ :=
  by
  refine' (triangle.eq_orthocenter_of_forall_mem_altitude hj₂₃ _ _).symm
  · rw [altitude_replace_orthocenter_eq_affine_span hi₁₂ hi₁₃ hi₂₃ hj₁₂ hj₁₃ hj₂₃ h₁ h₂ h₃]
    exact mem_affineSpan ℝ (Set.mem_insert _ _)
  · rw [altitude_replace_orthocenter_eq_affine_span hi₁₃ hi₁₂ hi₂₃.symm hj₁₃ hj₁₂ hj₂₃.symm h₁ h₃
        h₂]
    exact mem_affineSpan ℝ (Set.mem_insert _ _)
#align affine.triangle.orthocenter_replace_orthocenter_eq_point Affine.Triangle.orthocenter_replace_orthocenter_eq_point

end Triangle

end Affine

namespace EuclideanGeometry

open Affine AffineSubspace FiniteDimensional

variable {V : Type _} {P : Type _} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- Four points form an orthocentric system if they consist of the
vertices of a triangle and its orthocenter. -/
def OrthocentricSystem (s : Set P) : Prop :=
  ∃ t : Triangle ℝ P,
    t.orthocenter ∉ Set.range t.points ∧ s = insert t.orthocenter (Set.range t.points)
#align euclidean_geometry.orthocentric_system EuclideanGeometry.OrthocentricSystem

/-- This is an auxiliary lemma giving information about the relation
of two triangles in an orthocentric system; it abstracts some
reasoning, with no geometric content, that is common to some other
lemmas.  Suppose the orthocentric system is generated by triangle `t`,
and we are given three points `p` in the orthocentric system.  Then
either we can find indices `i₁`, `i₂` and `i₃` for `p` such that `p
i₁` is the orthocenter of `t` and `p i₂` and `p i₃` are points `j₂`
and `j₃` of `t`, or `p` has the same points as `t`. -/
theorem exists_of_range_subset_orthocentric_system {t : Triangle ℝ P}
    (ho : t.orthocenter ∉ Set.range t.points) {p : Fin 3 → P}
    (hps : Set.range p ⊆ insert t.orthocenter (Set.range t.points)) (hpi : Function.Injective p) :
    (∃ i₁ i₂ i₃ j₂ j₃ : Fin 3,
        i₁ ≠ i₂ ∧
          i₁ ≠ i₃ ∧
            i₂ ≠ i₃ ∧
              (∀ i : Fin 3, i = i₁ ∨ i = i₂ ∨ i = i₃) ∧
                p i₁ = t.orthocenter ∧ j₂ ≠ j₃ ∧ t.points j₂ = p i₂ ∧ t.points j₃ = p i₃) ∨
      Set.range p = Set.range t.points :=
  by
  by_cases h : t.orthocenter ∈ Set.range p
  · left
    rcases h with ⟨i₁, h₁⟩
    obtain ⟨i₂, i₃, h₁₂, h₁₃, h₂₃, h₁₂₃⟩ :
      ∃ i₂ i₃ : Fin 3, i₁ ≠ i₂ ∧ i₁ ≠ i₃ ∧ i₂ ≠ i₃ ∧ ∀ i : Fin 3, i = i₁ ∨ i = i₂ ∨ i = i₃ := by
      clear h₁; decide!
    have h : ∀ i, i₁ ≠ i → ∃ j : Fin 3, t.points j = p i :=
      by
      intro i hi
      replace hps :=
        Set.mem_of_mem_insert_of_ne (Set.mem_of_mem_of_subset (Set.mem_range_self i) hps)
          (h₁ ▸ hpi.ne hi.symm)
      exact hps
    rcases h i₂ h₁₂ with ⟨j₂, h₂⟩
    rcases h i₃ h₁₃ with ⟨j₃, h₃⟩
    have hj₂₃ : j₂ ≠ j₃ := by
      intro he
      rw [he, h₃] at h₂ 
      exact h₂₃.symm (hpi h₂)
    exact ⟨i₁, i₂, i₃, j₂, j₃, h₁₂, h₁₃, h₂₃, h₁₂₃, h₁, hj₂₃, h₂, h₃⟩
  · right
    have hs := Set.subset_diff_singleton hps h
    rw [Set.insert_diff_self_of_not_mem ho] at hs 
    refine' Set.eq_of_subset_of_card_le hs _
    rw [Set.card_range_of_injective hpi, Set.card_range_of_injective t.independent.injective]
#align euclidean_geometry.exists_of_range_subset_orthocentric_system EuclideanGeometry.exists_of_range_subset_orthocentric_system

/-- For any three points in an orthocentric system generated by
triangle `t`, there is a point in the subspace spanned by the triangle
from which the distance of all those three points equals the circumradius. -/
theorem exists_dist_eq_circumradius_of_subset_insert_orthocenter {t : Triangle ℝ P}
    (ho : t.orthocenter ∉ Set.range t.points) {p : Fin 3 → P}
    (hps : Set.range p ⊆ insert t.orthocenter (Set.range t.points)) (hpi : Function.Injective p) :
    ∃ c ∈ affineSpan ℝ (Set.range t.points), ∀ p₁ ∈ Set.range p, dist p₁ c = t.circumradius :=
  by
  rcases exists_of_range_subset_orthocentric_system ho hps hpi with
    (⟨i₁, i₂, i₃, j₂, j₃, h₁₂, h₁₃, h₂₃, h₁₂₃, h₁, hj₂₃, h₂, h₃⟩ | hs)
  · use reflection (affineSpan ℝ (t.points '' {j₂, j₃})) t.circumcenter,
      reflection_mem_of_le_of_mem (affineSpan_mono ℝ (Set.image_subset_range _ _))
        t.circumcenter_mem_affine_span
    intro p₁ hp₁
    rcases hp₁ with ⟨i, rfl⟩
    replace h₁₂₃ := h₁₂₃ i
    repeat' cases h₁₂₃
    · rw [h₁]
      exact triangle.dist_orthocenter_reflection_circumcenter t hj₂₃
    · rw [← h₂,
        dist_reflection_eq_of_mem _
          (mem_affineSpan ℝ (Set.mem_image_of_mem _ (Set.mem_insert _ _)))]
      exact t.dist_circumcenter_eq_circumradius _
    · rw [← h₃,
        dist_reflection_eq_of_mem _
          (mem_affineSpan ℝ
            (Set.mem_image_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))]
      exact t.dist_circumcenter_eq_circumradius _
  · use t.circumcenter, t.circumcenter_mem_affine_span
    intro p₁ hp₁
    rw [hs] at hp₁ 
    rcases hp₁ with ⟨i, rfl⟩
    exact t.dist_circumcenter_eq_circumradius _
#align euclidean_geometry.exists_dist_eq_circumradius_of_subset_insert_orthocenter EuclideanGeometry.exists_dist_eq_circumradius_of_subset_insert_orthocenter

/-- Any three points in an orthocentric system are affinely independent. -/
theorem OrthocentricSystem.affineIndependent {s : Set P} (ho : OrthocentricSystem s) {p : Fin 3 → P}
    (hps : Set.range p ⊆ s) (hpi : Function.Injective p) : AffineIndependent ℝ p :=
  by
  rcases ho with ⟨t, hto, hst⟩
  rw [hst] at hps 
  rcases exists_dist_eq_circumradius_of_subset_insert_orthocenter hto hps hpi with ⟨c, hcs, hc⟩
  exact cospherical.affine_independent ⟨c, t.circumradius, hc⟩ Set.Subset.rfl hpi
#align euclidean_geometry.orthocentric_system.affine_independent EuclideanGeometry.OrthocentricSystem.affineIndependent

/-- Any three points in an orthocentric system span the same subspace
as the whole orthocentric system. -/
theorem affineSpan_of_orthocentricSystem {s : Set P} (ho : OrthocentricSystem s) {p : Fin 3 → P}
    (hps : Set.range p ⊆ s) (hpi : Function.Injective p) :
    affineSpan ℝ (Set.range p) = affineSpan ℝ s :=
  by
  have ha := ho.affine_independent hps hpi
  rcases ho with ⟨t, hto, hts⟩
  have hs : affineSpan ℝ s = affineSpan ℝ (Set.range t.points) := by
    rw [hts, affineSpan_insert_eq_affineSpan ℝ t.orthocenter_mem_affine_span]
  refine'
    ext_of_direction_eq _
      ⟨p 0, mem_affineSpan ℝ (Set.mem_range_self _), mem_affineSpan ℝ (hps (Set.mem_range_self _))⟩
  have hfd : FiniteDimensional ℝ (affineSpan ℝ s).direction := by rw [hs]; infer_instance
  haveI := hfd
  refine' eq_of_le_of_finrank_eq (direction_le (affineSpan_mono ℝ hps)) _
  rw [hs, direction_affineSpan, direction_affineSpan, ha.finrank_vector_span (Fintype.card_fin _),
    t.independent.finrank_vector_span (Fintype.card_fin _)]
#align euclidean_geometry.affine_span_of_orthocentric_system EuclideanGeometry.affineSpan_of_orthocentricSystem

/-- All triangles in an orthocentric system have the same circumradius. -/
theorem OrthocentricSystem.exists_circumradius_eq {s : Set P} (ho : OrthocentricSystem s) :
    ∃ r : ℝ, ∀ t : Triangle ℝ P, Set.range t.points ⊆ s → t.circumradius = r :=
  by
  rcases ho with ⟨t, hto, hts⟩
  use t.circumradius
  intro t₂ ht₂
  have ht₂s := ht₂
  rw [hts] at ht₂ 
  rcases exists_dist_eq_circumradius_of_subset_insert_orthocenter hto ht₂
      t₂.independent.injective with
    ⟨c, hc, h⟩
  rw [Set.forall_range_iff] at h 
  have hs : Set.range t.points ⊆ s := by
    rw [hts]
    exact Set.subset_insert _ _
  rw [affine_span_of_orthocentric_system ⟨t, hto, hts⟩ hs t.independent.injective, ←
    affine_span_of_orthocentric_system ⟨t, hto, hts⟩ ht₂s t₂.independent.injective] at hc 
  exact (t₂.eq_circumradius_of_dist_eq hc h).symm
#align euclidean_geometry.orthocentric_system.exists_circumradius_eq EuclideanGeometry.OrthocentricSystem.exists_circumradius_eq

/-- Given any triangle in an orthocentric system, the fourth point is
its orthocenter. -/
theorem OrthocentricSystem.eq_insert_orthocenter {s : Set P} (ho : OrthocentricSystem s)
    {t : Triangle ℝ P} (ht : Set.range t.points ⊆ s) :
    s = insert t.orthocenter (Set.range t.points) :=
  by
  rcases ho with ⟨t₀, ht₀o, ht₀s⟩
  rw [ht₀s] at ht 
  rcases exists_of_range_subset_orthocentric_system ht₀o ht t.independent.injective with
    (⟨i₁, i₂, i₃, j₂, j₃, h₁₂, h₁₃, h₂₃, h₁₂₃, h₁, hj₂₃, h₂, h₃⟩ | hs)
  · obtain ⟨j₁, hj₁₂, hj₁₃, hj₁₂₃⟩ :
      ∃ j₁ : Fin 3, j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ ∀ j : Fin 3, j = j₁ ∨ j = j₂ ∨ j = j₃ := by clear h₂ h₃;
      decide!
    suffices h : t₀.points j₁ = t.orthocenter
    · have hui : (Set.univ : Set (Fin 3)) = {i₁, i₂, i₃} := by ext x; simpa using h₁₂₃ x
      have huj : (Set.univ : Set (Fin 3)) = {j₁, j₂, j₃} := by ext x; simpa using hj₁₂₃ x
      rw [← h, ht₀s, ← Set.image_univ, huj, ← Set.image_univ, hui]
      simp_rw [Set.image_insert_eq, Set.image_singleton, h₁, ← h₂, ← h₃]
      rw [Set.insert_comm]
    exact
      (triangle.orthocenter_replace_orthocenter_eq_point hj₁₂ hj₁₃ hj₂₃ h₁₂ h₁₃ h₂₃ h₁ h₂.symm
          h₃.symm).symm
  · rw [hs]
    convert ht₀s using 2
    exact triangle.orthocenter_eq_of_range_eq hs
#align euclidean_geometry.orthocentric_system.eq_insert_orthocenter EuclideanGeometry.OrthocentricSystem.eq_insert_orthocenter

end EuclideanGeometry

