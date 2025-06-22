/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.Geometry.Euclidean.SignedDist
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.Tactic.Positivity.Finset

/-!
# Incenters and excenters of simplices.

This file defines the insphere and exspheres of a simplex (tangent to the faces of the simplex),
and the center and radius of such spheres.

## Main definitions

* `Affine.Simplex.ExcenterExists` says whether an excenter exists with a given set of indices
  (that determine, up to negating all the signs, which vertices of the simplex lie on the same
  side of the opposite face as the excenter and which lie on the opposite side of that face).
* `Affine.Simplex.excenterWeights` are the weights of the excenter with the given set of
  indices, if it exists, as an affine combination of the vertices.
* `Affine.Simplex.exsphere` is the exsphere with the given set of indices, if it exists, with
  shorthands:
  * `Affine.Simplex.excenter` for the center of this sphere
  * `Affine.Simplex.exradius` for the radius of this sphere
* `Affine.Simplex.insphere` is the insphere, with shorthands:
  * `Affine.Simplex.incenter` for the center of this sphere
  * `Affine.Simplex.inradius` for the radius of this sphere

## References

* https://en.wikipedia.org/wiki/Incircle_and_excircles
* https://en.wikipedia.org/wiki/Incenter

-/


open EuclideanGeometry
open scoped Finset RealInnerProductSpace

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P]

noncomputable section

namespace Affine

namespace Simplex

variable {n : ℕ} [NeZero n] (s : Simplex ℝ P n)

/-- The unnormalized weights of the vertices in an affine combination that gives an excenter with
signs determined by the given set of indices (for the empty set, this is the incenter; for a
singleton set, this is the excenter opposite a vertex).  An excenter with those signs exists if
and only if the sum of these weights is nonzero (so the normalized weights sum to 1). -/
def excenterWeightsUnnorm (signs : Finset (Fin (n + 1))) (i : Fin (n + 1)) : ℝ :=
  (if i ∈ signs then -1 else 1) * (s.height i)⁻¹

@[simp] lemma excenterWeightsUnnorm_empty_apply (i : Fin (n + 1)) :
    s.excenterWeightsUnnorm ∅ i = (s.height i)⁻¹ :=
  one_mul _

/-- Whether an excenter exists with a given choice of signs. -/
def ExcenterExists (signs : Finset (Fin (n + 1))) : Prop :=
  ∑ i, s.excenterWeightsUnnorm signs i ≠ 0

/-- The normalized weights of the vertices in an affine combination that gives an excenter with
signs determined by the given set of indices.  An excenter with those signs exists if and only if
the sum of these weights is 1. -/
def excenterWeights (signs : Finset (Fin (n + 1))) : Fin (n + 1) → ℝ :=
  (∑ i, s.excenterWeightsUnnorm signs i)⁻¹ • s.excenterWeightsUnnorm signs

@[simp] lemma excenterWeightsUnnorm_compl (signs : Finset (Fin (n + 1))) :
    s.excenterWeightsUnnorm signsᶜ = -s.excenterWeightsUnnorm signs := by
  ext i
  by_cases h : i ∈ signs <;> simp [excenterWeightsUnnorm, h]

@[simp] lemma excenterWeights_compl (signs : Finset (Fin (n + 1))) :
    s.excenterWeights signsᶜ = s.excenterWeights signs := by
  simp [excenterWeights, inv_neg]

@[simp] lemma excenterExists_compl {signs : Finset (Fin (n + 1))} :
    s.ExcenterExists signsᶜ ↔ s.ExcenterExists signs := by
  simp [ExcenterExists]

lemma sum_excenterWeights (signs : Finset (Fin (n + 1))) [Decidable (s.ExcenterExists signs)] :
    ∑ i, s.excenterWeights signs i = if s.ExcenterExists signs then 1 else 0 := by
  simp_rw [ExcenterExists, excenterWeights]
  split_ifs with h
  · simp [← Finset.mul_sum, h]
  · simp only [ne_eq, not_not] at h
    simp [h]

@[simp] lemma sum_excenterWeights_eq_one_iff {signs : Finset (Fin (n + 1))} :
    ∑ i, s.excenterWeights signs i = 1 ↔ s.ExcenterExists signs := by
  classical
  simp [sum_excenterWeights]

alias ⟨_, ExcenterExists.sum_excenterWeights_eq_one⟩ := sum_excenterWeights_eq_one_iff

lemma sum_excenterWeightsUnnorm_empty_pos : 0 < ∑ i, s.excenterWeightsUnnorm ∅ i := by
  simp_rw [excenterWeightsUnnorm_empty_apply]
  positivity

/-- The existence of the incenter, expressed in terms of `ExcenterExists`. -/
@[simp] lemma excenterExists_empty : s.ExcenterExists ∅ :=
  s.sum_excenterWeightsUnnorm_empty_pos.ne'

lemma sum_inv_height_sq_smul_vsub_eq_zero :
    ∑ i, (s.height i)⁻¹ ^ 2 • (s.points i -ᵥ s.altitudeFoot i) = 0 := by
  suffices ∀ i, i ≠ 0 →
      ∑ j, ⟪s.points i -ᵥ s.points 0, (s.height j)⁻¹ ^ 2 • (s.points j -ᵥ s.altitudeFoot j)⟫ = 0 by
    rw [← Submodule.mem_bot ℝ,
      ← Submodule.inf_orthogonal_eq_bot (vectorSpan ℝ (Set.range s.points))]
    refine ⟨Submodule.sum_smul_mem _ _ fun i hi ↦
              vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan
                (mem_affineSpan _ (Set.mem_range_self _))
                (altitudeFoot_mem_affineSpan  _ _),
            ?_⟩
    rw [vectorSpan_range_eq_span_range_vsub_right_ne _ _ 0, Submodule.span_range_eq_iSup,
      ← Submodule.iInf_orthogonal, Submodule.iInf_coe, Set.mem_iInter]
    intro i
    rcases i with ⟨i, hi⟩
    simpa only [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sum]
      using this i hi
  intro i hi
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0),
    ← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩), ← add_assoc]
  convert add_zero _
  · convert Finset.sum_const_zero with j hj
    rw [real_inner_smul_right]
    convert mul_zero _
    rw [← Submodule.mem_orthogonal_singleton_iff_inner_right]
    refine SetLike.le_def.1 (Submodule.orthogonal_le ?_)
      (vsub_orthogonalProjection_mem_direction_orthogonal _ _)
    rw [Submodule.span_singleton_le_iff_mem, direction_affineSpan]
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hj
    refine vsub_mem_vectorSpan _ ?_ ?_ <;>
      simp only [range_faceOpposite_points, Set.mem_image, Set.mem_setOf_eq]
    · exact ⟨i, hj.1.symm, rfl⟩
    · exact ⟨0, hj.2.symm, rfl⟩
  · rw [inner_smul_right, inner_smul_right, inner_vsub_vsub_altitudeFoot_eq_height_sq _ hi,
      ← neg_vsub_eq_vsub_rev, inner_neg_left, inner_vsub_vsub_altitudeFoot_eq_height_sq _ hi.symm,
      mul_neg, inv_pow]
    simp [height]

/-- The inverse of the distance from one vertex to the opposite face, expressed as a sum of
multiples of that quantity for the other vertices. The multipliers, expressed here in terms of
inner products, are equal to the cosines of angles between faces (informally, the inverse
distances are proportional to the volumes of the faces and this is equivalent to expressing
the volume of a face as the sum of the signed volumes of projections of the other faces onto that
face). -/
lemma inv_height_eq_sum_mul_inv_dist (i : Fin (n + 1)) :
    (s.height i)⁻¹ =
      ∑ j ∈ {k | k ≠ i},
        -(⟪s.points i -ᵥ s.altitudeFoot i, s.points j -ᵥ s.altitudeFoot j⟫ /
          (s.height i * s.height j)) *
        (s.height j)⁻¹ := by
  rw [← sub_eq_zero]
  simp_rw [neg_mul]
  rw [Finset.sum_neg_distrib, sub_neg_eq_add, Finset.filter_ne',
    Finset.sum_erase_eq_sub (Finset.mem_univ _), real_inner_self_eq_norm_mul_norm,
    ← dist_eq_norm_vsub]
  simp only [height, ne_eq, mul_eq_zero, dist_eq_zero, ne_altitudeFoot, or_self,
    not_false_eq_true, div_self, one_mul, add_sub_cancel]
  have h := s.sum_inv_height_sq_smul_vsub_eq_zero
  apply_fun fun v ↦ (s.height i)⁻¹ * ⟪s.points i -ᵥ s.altitudeFoot i, v⟫ at h
  rw [inner_sum, Finset.mul_sum] at h
  simp only [inner_zero_right, mul_zero, inner_smul_right, height] at h
  convert h using 2 with j
  ring

/-- The inverse of the distance from one vertex to the opposite face is less than the sum of that
quantity for the other vertices. This implies the existence of the excenter opposite that vertex;
it also implies that the image of the incenter under a homothety with scale factor 2 about a
vertex lies outside the simplex. -/
lemma inv_height_lt_sum_inv_height (hn : 1 < n) (i : Fin (n + 1)) :
    (s.height i)⁻¹ < ∑ j ∈ {k | k ≠ i}, (s.height j)⁻¹ := by
  rw [inv_height_eq_sum_mul_inv_dist]
  refine Finset.sum_lt_sum_of_nonempty ?_ ?_
  · rw [Finset.filter_ne', ← Finset.card_ne_zero]
    simp only [Finset.mem_univ, Finset.card_erase_of_mem, Finset.card_univ, Fintype.card_fin,
      add_tsub_cancel_right]
    exact NeZero.ne _
  · rintro j hj
    refine mul_lt_of_lt_one_left ?_ ?_
    · simp [height_pos]
    · rw [neg_lt]
      exact neg_one_lt_inner_vsub_altitudeFoot_div _ _ _ hn

lemma sum_excenterWeightsUnnorm_singleton_pos (hn : 1 < n) (i : Fin (n + 1)) :
    0 < ∑ j, s.excenterWeightsUnnorm {i} j := by
  rw [← Finset.sum_add_sum_compl {i}, Finset.sum_singleton]
  nth_rw 1 [excenterWeightsUnnorm]
  simp only [Finset.mem_singleton, ↓reduceIte, neg_mul, one_mul, lt_neg_add_iff_add_lt, add_zero]
  convert s.inv_height_lt_sum_inv_height hn i using 2 with j h
  · ext j
    simp
  · simp only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and] at h
    simp [excenterWeightsUnnorm, h]

/-- The existence of the excenter opposite a vertex (in two or more dimensions), expressed in
terms of `ExcenterExists`. -/
lemma excenterExists_singleton (hn : 1 < n) (i : Fin (n + 1)) : s.ExcenterExists {i} :=
  (s.sum_excenterWeightsUnnorm_singleton_pos hn i).ne'

/-- The exsphere with signs determined by the given set of indices (for the empty set, this is
the insphere; for a singleton set, this is the exsphere opposite a vertex).  This is only
meaningful if `s.ExcenterExists`; otherwise, it is a sphere of radius zero at some arbitrary
point. -/
def exsphere (signs : Finset (Fin (n + 1))) : Sphere P where
  center := Finset.univ.affineCombination ℝ s.points (s.excenterWeights signs)
  radius := |(∑ i, s.excenterWeightsUnnorm signs i)⁻¹|

/-- The insphere of a simplex. -/
def insphere : Sphere P :=
  s.exsphere ∅

/-- The excenter with signs determined by the given set of indices (for the empty set, this is
the incenter; for a singleton set, this is the excenter opposite a vertex).  This is only
meaningful if `s.ExcenterExists signs`; otherwise, it is some arbitrary point. -/
def excenter (signs : Finset (Fin (n + 1))) : P :=
  (s.exsphere signs).center

/-- The incenter of a simplex. -/
def incenter : P :=
  (s.exsphere ∅).center

/-- The distance between an excenter and a face of the simplex (zero if no such excenter
exists). -/
def exradius (signs : Finset (Fin (n + 1))) : ℝ :=
  (s.exsphere signs).radius

/-- The distance between the incenter and a face of the simplex. -/
def inradius : ℝ :=
  (s.exsphere ∅).radius

@[simp] lemma exsphere_center (signs : Finset (Fin (n + 1))) :
    (s.exsphere signs).center = s.excenter signs :=
  rfl

@[simp] lemma exsphere_radius (signs : Finset (Fin (n + 1))) :
    (s.exsphere signs).radius = s.exradius signs :=
  rfl

@[simp] lemma insphere_center : s.insphere.center = s.incenter :=
  rfl

@[simp] lemma insphere_radius : s.insphere.radius = s.inradius :=
  rfl

@[simp] lemma exsphere_empty : s.exsphere ∅ = s.insphere :=
  rfl

@[simp] lemma excenter_empty : s.excenter ∅ = s.incenter :=
  rfl

@[simp] lemma exradius_empty : s.exradius ∅ = s.inradius :=
  rfl

@[simp] lemma exsphere_univ : s.exsphere Finset.univ = s.insphere := by
  rw [exsphere, ← Finset.compl_empty, excenterWeightsUnnorm_compl, excenterWeights_compl]
  simp only [Finset.mem_univ, Pi.neg_apply, Finset.sum_neg_distrib, inv_neg, abs_neg]
  rfl

@[simp] lemma excenter_univ : s.excenter Finset.univ = s.incenter := by
  rw [excenter, exsphere_univ, insphere_center]

@[simp] lemma exradius_univ : s.exradius Finset.univ = s.inradius := by
  rw [exradius, exsphere_univ, insphere_radius]

lemma excenter_eq_affineCombination (signs : Finset (Fin (n + 1))) :
    s.excenter signs = Finset.univ.affineCombination ℝ s.points (s.excenterWeights signs) :=
  rfl

lemma exradius_eq_abs_inv_sum (signs : Finset (Fin (n + 1))) :
    s.exradius signs = |(∑ i, s.excenterWeightsUnnorm signs i)⁻¹| :=
  rfl

lemma incenter_eq_affineCombination :
    s.incenter = Finset.univ.affineCombination ℝ s.points (s.excenterWeights ∅) :=
  rfl

lemma inradius_eq_abs_inv_sum : s.inradius = |(∑ i, s.excenterWeightsUnnorm ∅ i)⁻¹| :=
  rfl

lemma exradius_nonneg (signs : Finset (Fin (n + 1))) : 0 ≤ s.exradius signs :=
  abs_nonneg _

variable {s} in
lemma ExcenterExists.exradius_pos {signs : Finset (Fin (n + 1))} (h : s.ExcenterExists signs) :
    0 < s.exradius signs :=
  abs_pos.2 (inv_ne_zero h)

lemma inradius_pos : 0 < s.inradius :=
  s.excenterExists_empty.exradius_pos

lemma exradius_singleton_pos (hn : 1 < n) (i : Fin (n + 1)) : 0 < s.exradius {i} :=
  (s.excenterExists_singleton hn i).exradius_pos

variable {s} in
lemma ExcenterExists.excenter_mem_affineSpan_range {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) : s.excenter signs ∈ affineSpan ℝ (Set.range s.points) :=
  affineCombination_mem_affineSpan h.sum_excenterWeights_eq_one _

lemma incenter_mem_affineSpan_range : s.incenter ∈ affineSpan ℝ (Set.range s.points) :=
  s.excenterExists_empty.excenter_mem_affineSpan_range

lemma excenter_singleton_mem_affineSpan_range (hn : 1 < n) (i : Fin (n + 1)) :
    s.excenter {i} ∈ affineSpan ℝ (Set.range s.points) :=
  (s.excenterExists_singleton hn i).excenter_mem_affineSpan_range

variable {s} in
lemma ExcenterExists.signedInfDist_excenter_eq_mul_sum_inv {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) (i : Fin (n + 1)) :
    s.signedInfDist i (s.excenter signs) =
      (if i ∈ signs then -1 else 1) * (∑ j, s.excenterWeightsUnnorm signs j)⁻¹ := by
  simp_rw [excenter_eq_affineCombination,
    signedInfDist_affineCombination _ _ h.sum_excenterWeights_eq_one, excenterWeights,
    Pi.smul_apply, ← dist_eq_norm_vsub, excenterWeightsUnnorm]
  rw [← altitudeFoot, ← height]
  simp [mul_assoc, (s.height_pos i).ne']

variable {s} in
/-- The signed distance between the excenter and its projection in the plane of each face is the
exradius. -/
lemma ExcenterExists.signedInfDist_excenter {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) (i : Fin (n + 1)) :
    s.signedInfDist i (s.excenter signs) = (if i ∈ signs then -1 else 1) *
      SignType.sign (∑ j, s.excenterWeightsUnnorm signs j) * (s.exradius signs) := by
  rw [h.signedInfDist_excenter_eq_mul_sum_inv, mul_assoc, exradius_eq_abs_inv_sum]
  congr
  rw [← mul_eq_one_iff_inv_eq₀ h, ← mul_assoc, self_mul_sign, ← abs_mul, mul_inv_cancel₀ h, abs_one]

/-- The signed distance between the incenter and its projection in the plane of each face is the
inradius.

In other words, the incenter is _internally_ tangent to the faces. -/
lemma signedInfDist_incenter (i : Fin (n + 1)) : s.signedInfDist i s.incenter = s.inradius := by
  rw [incenter, exsphere_center, s.excenterExists_empty.signedInfDist_excenter]
  simp (discharger := positivity)

variable {s} in
/-- The distance between the excenter and its projection in the plane of each face is the exradius.

In other words, the exsphere is tangent to the faces. -/
lemma ExcenterExists.dist_excenter {signs : Finset (Fin (n + 1))} (h : s.ExcenterExists signs)
    (i : Fin (n + 1)) :
    dist (s.excenter signs) ((s.faceOpposite i).orthogonalProjectionSpan (s.excenter signs)) =
      s.exradius signs := by
  rw [← abs_signedInfDist_eq_dist_of_mem_affineSpan_range i h.excenter_mem_affineSpan_range,
    h.signedInfDist_excenter, abs_mul, abs_mul, abs_of_nonneg (s.exradius_nonneg signs)]
  simp only [abs_ite, abs_neg, abs_one, ite_self, one_mul]
  rcases lt_trichotomy 0 (∑ i, s.excenterWeightsUnnorm signs i) with h' | h' | h'
  · simp [h']
  · simp [h h'.symm]
  · simp [h']

/-- The distance between the incenter and its projection in the plane of each face is the inradius.

In other words, the incenter is tangent to the faces. -/
lemma dist_incenter (i : Fin (n + 1)) :
    dist s.incenter ((s.faceOpposite i).orthogonalProjectionSpan s.incenter) = s.inradius :=
  s.excenterExists_empty.dist_excenter _

lemma exists_forall_signedInfDist_eq_iff_excenterExists_and_eq_excenter {p : P}
    (hp : p ∈ affineSpan ℝ (Set.range s.points)) {signs : Finset (Fin (n + 1))} :
    (∃ r : ℝ, ∀ i, s.signedInfDist i p = (if i ∈ signs then -1 else 1) * r) ↔
      s.ExcenterExists signs ∧ p = s.excenter signs := by
  refine ⟨?_, ?_⟩
  · rintro ⟨r, h⟩
    obtain ⟨w, h1, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp
    have h' : ∀ i, w i * ‖s.points i -ᵥ s.altitudeFoot i‖ = (if i ∈ signs then -1 else 1) * r := by
      intro i
      rw [altitudeFoot, ← s.signedInfDist_affineCombination i h1]
      exact h i
    simp_rw [← dist_eq_norm_vsub] at h'
    have h'' : ∀ i, w i = r * s.excenterWeightsUnnorm signs i := by
      simp_rw [excenterWeightsUnnorm]
      intro i
      replace h' := h' i
      rw [← height, ← eq_div_iff (s.height_pos i).ne'] at h'
      rw [h', mul_comm, div_eq_mul_inv, mul_assoc, height, altitudeFoot, orthogonalProjectionSpan]
    have hw : w = s.excenterWeights signs := by
      simp_rw [h'', ← Finset.mul_sum] at h1
      ext j
      rw [h'', eq_inv_of_mul_eq_one_left h1]
      rfl
    subst hw
    exact ⟨s.sum_excenterWeights_eq_one_iff.1 h1, rfl⟩
  · rintro ⟨h, rfl⟩
    refine ⟨SignType.sign (∑ j, s.excenterWeightsUnnorm signs j) * (s.exradius signs), fun i ↦ ?_⟩
    rw [h.signedInfDist_excenter]
    simp

lemma exists_forall_signedInfDist_eq_iff_eq_incenter {p : P}
    (hp : p ∈ affineSpan ℝ (Set.range s.points)) :
    (∃ r : ℝ, ∀ i, s.signedInfDist i p = r) ↔ p = s.incenter := by
  convert s.exists_forall_signedInfDist_eq_iff_excenterExists_and_eq_excenter hp (signs := ∅)
  · simp
  · simp [excenterExists_empty]

lemma exists_forall_dist_eq_iff_exists_excenterExists_and_eq_excenter {p : P}
    (hp : p ∈ affineSpan ℝ (Set.range s.points)) :
    (∃ r : ℝ, ∀ i, dist p ((s.faceOpposite i).orthogonalProjectionSpan p) = r) ↔
      ∃ signs, s.ExcenterExists signs ∧ p = s.excenter signs := by
  simp_rw [← abs_signedInfDist_eq_dist_of_mem_affineSpan_range _ hp]
  refine ⟨?_, ?_⟩
  · rintro ⟨r, h⟩
    have h' : ∀ i, s.signedInfDist i p = r ∨ s.signedInfDist i p = -r :=
      fun i ↦ eq_or_eq_neg_of_abs_eq (h i)
    refine ⟨{i ∈ (Finset.univ : Finset (Fin (n + 1))) | s.signedInfDist i p = -r}, ?_⟩
    apply (s.exists_forall_signedInfDist_eq_iff_excenterExists_and_eq_excenter hp).1
    refine ⟨r, ?_⟩
    simp only [Set.mem_setOf_eq, ite_mul, neg_mul, one_mul]
    intro i
    split_ifs with hi
    · simpa using hi
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simpa [hi] using h' i
  · rintro ⟨signs, h⟩
    replace h := (s.exists_forall_signedInfDist_eq_iff_excenterExists_and_eq_excenter hp).2 h
    rcases h with ⟨r, h⟩
    refine ⟨|r|, ?_⟩
    simp [h, abs_ite]

end Simplex

end Affine
