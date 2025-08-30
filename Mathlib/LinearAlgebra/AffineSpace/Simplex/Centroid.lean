/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Chu Zheng
-/
import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
import Mathlib.LinearAlgebra.AffineSpace.Centroid
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic.FieldSimp

/-!
# Centroid of a simplex in affine space

This file proves some basic properties of the centroid of a simplex in affine space.
The definition of the centroid is based on `Finset.univ.centroid` applied to the set of vertices.
For convenience, we use `Simplex.centroid` as an abbreviation.

This file also defines `faceOppositeCentroid`, which is the centroid of the facet of the simplex
obtained by removing one vertex.

We prove several relations among the `centroid`, the `faceOppositeCentroid`, and the vertices of
the simplex. In particular, we prove a version of Commandino's theorem in arbitrary dimensions:
the centroid lies on each median, dividing it in a ratio of `n : 1`, where `n` is the dimension
of the simplex.

## Main definitions

* `centroid` is the centroid of a simplex, defined via `Finset.univ.centroid` on its vertices.

* `faceOppositeCentroid` is the centroid of the facet obtained by removing one vertex from the
simplex.

* `median` is the line connecting a vertex to the corresponding faceOppositeCentroid.

## References

* https://en.wikipedia.org/wiki/Median_(geometry)
* https://en.wikipedia.org/wiki/Commandino%27s_theorem

-/

noncomputable section

open Finset AffineSubspace

namespace Affine

namespace Simplex

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AffineSpace V P]

variable {n : ℕ}

/-- The centroid of a simplex is the `Finset.centroid` of the set of all its vertices. -/
abbrev centroid (t : Affine.Simplex k P n) : P := Finset.univ.centroid k t.points

@[simp]
theorem finset_centroid_eq (s : Simplex k P n) :
    Finset.univ.centroid k s.points = s.centroid := rfl

/-- The centroid lines in the affine span of the simplex's vertices. -/
theorem centroid_mem_affineSpan [CharZero k] {n : ℕ} (s : Simplex k P n) :
    s.centroid ∈ affineSpan k (Set.range s.points) :=
  centroid_mem_affineSpan_of_card_eq_add_one k _ (card_fin (n + 1))

/-- The centroid is equal to the affine combination of the points with `centroidWeights`. -/
@[simp]
theorem centroid_eq_affine_combination (s : Simplex k P n) :
    s.centroid = affineCombination k univ s.points (centroidWeights k univ) := by rfl

/-- The centroid does not lie in the affine span of the simplex's points with one vertex removed. -/
theorem centroid_not_mem_affineSpan_compl [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) :
    s.centroid ∉ affineSpan k (s.points '' {i}ᶜ) := by
  intro h
  rw [s.centroid_eq_affine_combination] at h
  set w := (centroidWeights k (univ : Finset (Fin (n + 1)))) with wdef
  have hw : ∑ i, w i = 1 := by
    rw [sum_centroidWeights_eq_one_of_card_ne_zero]
    simp
  have hi : i ∉ ({i}ᶜ : Set (Fin (n+1))) := by simp
  have h1 := AffineIndependent.eq_zero_of_affineCombination_mem_affineSpan s.independent hw h
    (by simp) hi
  have h2 : w i = (1 : k) / (n+1) := by
    field_simp [wdef, centroidWeights_apply, card_univ, Fintype.card_fin, Nat.cast_add,
      Nat.cast_one]
  field_simp [h2] at h1
  norm_cast at h1

/-- The vector from any point to the centroid is the average of vectors to the simplex vertices. -/
theorem centroid_vsub_eq {n : ℕ} [CharZero k] (s : Simplex k P n) (p : P) :
    s.centroid -ᵥ p = ((1 : k) / (n + 1)) • ∑ x, (s.points x -ᵥ p) := by
  rw [centroid, Finset.centroid_def]
  have hsum : ∑ i : Fin (n+1), centroidWeights k univ i = 1 := by
    rw [sum_centroidWeights_eq_one_of_cast_card_ne_zero _ (by simp; norm_cast)]
  rw [affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _ hsum p]
  simp only [weightedVSubOfPoint_apply, centroidWeights_apply, card_univ, Fintype.card_fin,
    Nat.cast_add, Nat.cast_one, vadd_vsub, one_div,← smul_sum]

/-- The vector from a vertex to the centroid equals the average of vertex-to-vertex vectors. -/
theorem centroid_vsub_point_eq_smul_sum_vsub {n : ℕ} [CharZero k] (s : Simplex k P n)
    (i : Fin (n + 1)) :
    s.centroid -ᵥ s.points i = ((1 : k) / (n + 1)) • ∑ x, (s.points x -ᵥ s.points i) :=
  centroid_vsub_eq s (s.points i)

theorem centroid_eq_smul_sum_vsub_vadd [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) :
    s.centroid = ((1 : k) / (n + 1)) • ∑ x, (s.points x -ᵥ s.points i) +ᵥ s.points i := by
  rw [← centroid_vsub_point_eq_smul_sum_vsub s i, vsub_vadd]

theorem smul_centroid_vsub_point_eq_sum_vsub [CharZero k] (s : Simplex k P n)
    (i : Fin (n + 1)) :
    ((n : k) + 1) • (s.centroid -ᵥ s.points i) = ∑ x, (s.points x -ᵥ s.points i) := by
  rw [centroid_eq_smul_sum_vsub_vadd s i, vadd_vsub, smul_smul]
  field_simp
  rw [div_self (by norm_cast), one_smul]

/-- The sum of vectors from the centroid to each vertex is zero. -/
theorem centroid_weighted_vsub_eq_zero [CharZero k] (s : Simplex k P n) :
    ∑ i, (s.points i -ᵥ s.centroid) = 0 := by
  have h := centroid_vsub_eq s s.centroid
  simp only [vsub_self, one_div] at h
  symm at h
  rw [smul_eq_zero_iff_right (inv_ne_zero (by norm_cast))] at h
  exact h

/-- A point is centroid if and only if the sum of vectors from the point to all vertices is zero. -/
theorem eq_centroid_iff_sum_vsub_eq_zero [CharZero k] {s : Simplex k P n} {p : P} :
    p = s.centroid ↔ ∑ i, (s.points i -ᵥ p) = 0 := by
  constructor
  · intro h
    rw [h, centroid_weighted_vsub_eq_zero]
  · intro h
    rw [← vsub_eq_zero_iff_eq]
    have : ∑ i, (s.points i -ᵥ p) = ∑ i, ((s.points i -ᵥ s.centroid) - (p -ᵥ s.centroid)) := by
      apply sum_congr rfl
      intro x hx
      rw [vsub_sub_vsub_cancel_right _ _ s.centroid]
    rw [this, sum_sub_distrib, centroid_weighted_vsub_eq_zero] at h
    simp only [sum_const, card_univ, Fintype.card_fin, zero_sub, neg_eq_zero] at h
    have h' : ((n : k) + 1) • (p -ᵥ s.centroid) = 0 := by norm_cast
    rw [smul_eq_zero_iff_right (by norm_cast)] at h'
    exact h'

/-- The centroid of a face of a simplex as the centroid of a subset of
the points. -/
@[simp]
theorem face_centroid_eq_centroid {n : ℕ} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : ℕ}
    (h : #fs = m + 1) : Finset.univ.centroid k (s.face h).points = fs.centroid k s.points := by
  convert (Finset.univ.centroid_map k (fs.orderEmbOfFin h).toEmbedding s.points).symm
  rw [← Finset.coe_inj, Finset.coe_map, Finset.coe_univ, Set.image_univ]
  simp

/-- Over a characteristic-zero division ring, the centroids given by
two subsets of the points of a simplex are equal if and only if those
faces are given by the same subset of points. -/
@[simp]
theorem centroid_eq_iff [CharZero k] {n : ℕ} (s : Simplex k P n) {fs₁ fs₂ : Finset (Fin (n + 1))}
    {m₁ m₂ : ℕ} (h₁ : #fs₁ = m₁ + 1) (h₂ : #fs₂ = m₂ + 1) :
    fs₁.centroid k s.points = fs₂.centroid k s.points ↔ fs₁ = fs₂ := by
  refine ⟨fun h => ?_, @congrArg _ _ fs₁ fs₂ (fun z => Finset.centroid k z s.points)⟩
  rw [Finset.centroid_eq_affineCombination_fintype,
    Finset.centroid_eq_affineCombination_fintype] at h
  have ha :=
    (affineIndependent_iff_indicator_eq_of_affineCombination_eq k s.points).1 s.independent _ _ _ _
      (fs₁.sum_centroidWeightsIndicator_eq_one_of_card_eq_add_one k h₁)
      (fs₂.sum_centroidWeightsIndicator_eq_one_of_card_eq_add_one k h₂) h
  simp_rw [Finset.coe_univ, Set.indicator_univ, funext_iff,
    Finset.centroidWeightsIndicator_def, Finset.centroidWeights, h₁, h₂] at ha
  ext i
  specialize ha i
  have key : ∀ n : ℕ, (n : k) + 1 ≠ 0 := fun n h => by norm_cast at h
  -- we should be able to golf this to
  -- `refine ⟨fun hi ↦ decidable.by_contradiction (fun hni ↦ ?_), ...⟩`,
  -- but for some unknown reason it doesn't work.
  constructor <;> intro hi <;> by_contra hni
  · simp [hni, hi, key] at ha
  · simpa [hni, hi, key] using ha.symm

/-- Over a characteristic-zero division ring, the centroids of two
faces of a simplex are equal if and only if those faces are given by
the same subset of points. -/
theorem face_centroid_eq_iff [CharZero k] {n : ℕ} (s : Simplex k P n)
    {fs₁ fs₂ : Finset (Fin (n + 1))} {m₁ m₂ : ℕ} (h₁ : #fs₁ = m₁ + 1) (h₂ : #fs₂ = m₂ + 1) :
    (s.face h₁).centroid = (s.face h₂).centroid ↔
      fs₁ = fs₂ := by
  rw [face_centroid_eq_centroid, face_centroid_eq_centroid]
  exact s.centroid_eq_iff h₁ h₂

/-- Two simplices with the same points have the same centroid. -/
theorem centroid_eq_of_range_eq {n : ℕ} {s₁ s₂ : Simplex k P n}
    (h : Set.range s₁.points = Set.range s₂.points) :
    s₁.centroid = s₂.centroid := by
  rw [← Set.image_univ, ← Set.image_univ, ← Finset.coe_univ] at h
  exact
    Finset.univ.centroid_eq_of_inj_on_of_image_eq k _
      (fun _ _ _ _ he => AffineIndependent.injective s₁.independent he)
      (fun _ _ _ _ he => AffineIndependent.injective s₂.independent he) h


/-- Replacing a vertex of a simplex by its centroid preserves affine independence. -/
theorem affineIndependent_points_update_centroid [CharZero k] (s : Simplex k P n)
    (i : Fin (n + 1)) :
    AffineIndependent k (Function.update s.points i s.centroid) := by
  have h : s.centroid ∉ affineSpan k (s.points '' {i}ᶜ) := centroid_not_mem_affineSpan_compl s i
  exact AffineIndependent.affineIndependent_update_of_notMem_affineSpan s.independent h

variable [NeZero n]

/-- The faceOppositeCentroid is the centroid of the face opposite to the vertex indexed by `i`. -/
def faceOppositeCentroid (s : Affine.Simplex k P n) (i : Fin (n + 1)) : P :=
    (s.faceOpposite i).centroid

/-- The `faceOppositeCentroid` lies in the affine span of all simplex vertices. -/
theorem faceOppositeCentroid_mem_affineSpan [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) :
    s.faceOppositeCentroid i ∈ affineSpan k (Set.range s.points) := by
  unfold faceOppositeCentroid
  have h : Set.range (s.faceOpposite i).points ⊆ Set.range s.points := by
    intro j hj
    rcases hj with ⟨k, _, rfl⟩
    apply Set.mem_range_self
  apply affineSpan_mono _ h
  exact centroid_mem_affineSpan (s.faceOpposite i)

/-- The `faceOppositeCentroid` is the affine combination of the complement vertices with equal
 weights `1/n`. -/
theorem faceOppositeCentroid_eq_affineCombination (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    s.faceOppositeCentroid i = ((affineCombination k {i}ᶜ s.points) fun _ ↦ (↑n)⁻¹) := by
  unfold faceOppositeCentroid
  have : s.faceOpposite i = s.face (fs := {i}ᶜ) (by simp [card_compl, NeZero.one_le]) := by rfl
  rw [this, face_centroid_eq_centroid, centroid_def, centroidWeights_eq_const, card_compl]
  simp only [Fintype.card_fin, card_singleton, add_tsub_cancel_right]
  rfl

/-- The vector from a vertex to the corresponding `faceOppositeCentroid` equals the average of the
 displacements to the other vertices. -/
theorem faceOppositeCentroid_vsub_point_eq_smul_sum_vsub [CharZero k] (s : Affine.Simplex k P n)
    (i : Fin (n + 1)) :
    s.faceOppositeCentroid i -ᵥ (s.points i) = (n : k)⁻¹ • ∑ x, (s.points x -ᵥ s.points i) := by
  rw [faceOppositeCentroid_eq_affineCombination]
  rw [affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _
    ?_ (s.points i)]
  · simp only [weightedVSubOfPoint_apply, vadd_vsub]
    have h (i : Fin (n+1)) : ∑ i_1 ∈ {i}ᶜ, (n : k)⁻¹ • (s.points i_1 -ᵥ s.points i) =
      ∑ i_1 : (Fin (n + 1)) , ((n : k)⁻¹ • (s.points i_1 -ᵥ s.points i)) := by
      rw [← Finset.sum_compl_add_sum {i}]
      simp
    rw [h i]
    field_simp
    rw [smul_sum]
  simp [sum_const, card_compl]
  field_simp
  rw [div_self]
  exact NeZero.ne (n : k)

/-- The `faceOppositeCentroid` equals the average displacement from a vertex plus that vertex. -/
theorem faceOppositeCentroid_eq_sum_vsub_vadd [CharZero k] (s : Affine.Simplex k P n)
    (i : Fin (n + 1)) :
    s.faceOppositeCentroid i = (n : k)⁻¹ • ∑ x, (s.points x -ᵥ s.points i) +ᵥ (s.points i) := by
  rw [← faceOppositeCentroid_vsub_point_eq_smul_sum_vsub s i, vsub_vadd]

/-- The vector from a vertex to its `faceOppositeCentroid` equals the average of reversed
displacements. -/
theorem point_vsub_faceOppositeCentroid_eq_smul_sum_vsub [CharZero k] (s : Affine.Simplex k P n)
    (i : Fin (n + 1)) :
    s.points i -ᵥ s.faceOppositeCentroid i = (n : k)⁻¹ • ∑ x, (s.points i -ᵥ s.points x) := by
  rw [← neg_vsub_eq_vsub_rev, faceOppositeCentroid_vsub_point_eq_smul_sum_vsub, ← neg_smul,
    Lean.Grind.Ring.neg_eq_mul_neg_one, ← smul_smul, smul_sum]
  simp only [neg_smul, one_smul, neg_vsub_eq_vsub_rev]

theorem smul_faceOppositeCentroid_vsub_point_eq_sum_vsub [CharZero k] (s : Affine.Simplex k P n)
    (i : Fin (n + 1)) :
    (n : k) • (s.faceOppositeCentroid i -ᵥ s.points i) =  ∑ x, (s.points x -ᵥ s.points i) := by
  field_simp [faceOppositeCentroid_eq_sum_vsub_vadd, smul_smul, div_self (NeZero.ne (n : k)),
    one_smul]

theorem smul_centroid_vsub_point_eq_smul_faceOppositeCentroid_vsub_point [CharZero k]
    (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    ((n + 1) : k) • (s.centroid -ᵥ s.points i) =
    (n : k) • (s.faceOppositeCentroid i -ᵥ s.points i) := by
  rw [smul_faceOppositeCentroid_vsub_point_eq_sum_vsub s i,
    smul_centroid_vsub_point_eq_sum_vsub s i]

/-- The vector between two `faceOppositeCentroid` equals `n⁻¹` times the vector between the
corresponding vertices. -/
theorem faceOppositeCentroid_vsub_faceOppositeCentroid [CharZero k] (s : Affine.Simplex k P n)
    (i j : Fin (n + 1)) :
    s.faceOppositeCentroid i -ᵥ s.faceOppositeCentroid j =
    (n : k)⁻¹ • (s.points j -ᵥ s.points i) := by
  rw [faceOppositeCentroid_eq_sum_vsub_vadd s i, faceOppositeCentroid_eq_sum_vsub_vadd s j,
    vadd_vsub_vadd_comm _ _ (s.points i) (s.points j)]
  have h1 (i : Fin (n+1)) : ∑ x, (s.points x -ᵥ s.points i) = ∑ x,  (s.points x -ᵥ s.points 0
      - (s.points i-ᵥ s.points 0)) := by
    apply sum_congr rfl
    simp
  simp_rw [h1 i, h1 j, sum_sub_distrib]
  field_simp
  rw [smul_sub, smul_sub, one_div, sub_sub_sub_cancel_left, ← smul_sub, ← smul_sub,
    vsub_sub_vsub_cancel_right]
  have : (s.points i -ᵥ s.points j) = -(s.points j -ᵥ s.points i) := by simp
  rw [this, ← sub_eq_add_neg, add_smul, sub_eq_iff_eq_add , one_smul, smul_add, add_comm]
  field_simp
  have : ((1 : k) / ↑n) • n • (s.points j -ᵥ s.points i) = (n : k)⁻¹ •
      (n : k) • (s.points j -ᵥ s.points i) := by
    norm_cast0
    congr 1
    rw [one_div]
  rw [this, smul_smul, inv_eq_one_div, one_div_mul_cancel (NeZero.ne (n : k)), one_smul]

/-- The vector from a vertex to its `faceOppositeCentroid` is `(n+1)` times the vector from the
 `centroid` to that `faceOppositeCentroid`. -/
theorem faceOppositeCentroid_vsub_point_eq_smul_vsub [CharZero k] (s : Simplex k P n)
    (i : Fin (n + 1)) :
    s.faceOppositeCentroid i -ᵥ s.points i =
    ((n + 1) : k) • (s.faceOppositeCentroid i -ᵥ s.centroid) := by
  rw [← vsub_sub_vsub_cancel_right _ (s.centroid) (s.points i),
    faceOppositeCentroid_vsub_point_eq_smul_sum_vsub, centroid_vsub_point_eq_smul_sum_vsub,
    ← sub_smul, smul_smul]
  congr
  field_simp [mul_sub]
  rw [add_div, one_div, div_self (NeZero.ne (n : k)), div_self (by norm_cast)]
  norm_num

theorem point_vsub_faceOppositeCentroid_eq_smul_vsub [CharZero k] (s : Simplex k P n)
    (i : Fin (n + 1)) :
    s.points i -ᵥ s.faceOppositeCentroid i =
    ((n + 1) : k) • (s.centroid -ᵥ s.faceOppositeCentroid i) := by
  rw [← neg_vsub_eq_vsub_rev, faceOppositeCentroid_vsub_point_eq_smul_vsub, ← neg_smul,
    ← neg_smul_neg, neg_vsub_eq_vsub_rev, neg_neg]

/-- *Commandino's theorem* : For n-simplex, the vector from a vertex to the `centroid`
equals `n` times the vector from the `centroid` to the corresponding `faceOppositeCentroid`. -/
theorem point_vsub_centroid_eq_smul_vsub [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) :
    s.points i -ᵥ s.centroid = (n : k) • (s.centroid -ᵥ s.faceOppositeCentroid i) := by
  symm
  rw [← vsub_sub_vsub_cancel_right _ _ (s.points i),
    faceOppositeCentroid_vsub_point_eq_smul_sum_vsub,
    centroid_vsub_point_eq_smul_sum_vsub, ← neg_vsub_eq_vsub_rev,
    centroid_vsub_point_eq_smul_sum_vsub, ← sub_smul, smul_smul, ← neg_smul]
  congr
  simp_rw [mul_sub, sub_eq_iff_eq_add, neg_add_eq_sub]
  symm
  field_simp [sub_eq_iff_eq_add, NeZero.ne (n : k)]
  rw [div_self (by norm_cast)]

/-- Reverse version of `point_vsub_centroid_eq_smul_vsub`. -/
theorem centroid_vsub_point_eq_smul_vsub [CharZero k]
    (s : Simplex k P n) (i : Fin (n + 1)) :
    s.centroid -ᵥ s.points i = (n : k) • (s.faceOppositeCentroid i -ᵥ s.centroid) := by
  rw [← neg_vsub_eq_vsub_rev, point_vsub_centroid_eq_smul_vsub, ← neg_smul_neg,
    neg_vsub_eq_vsub_rev, ← neg_smul, neg_neg]

/-- The vector from `centroid` to a vertex corresponding `faceOppositeCentroid` is `(1 / n)` of the
vector from the vertex to the centroid. -/
theorem faceOppositeCentroid_vsub_centroid_eq_smul_vsub [CharZero k]
    (s : Simplex k P n) (i : Fin (n + 1)) :
    s.faceOppositeCentroid i -ᵥ s.centroid = (1 / n : k) • (s.centroid -ᵥ s.points i) := by
  rw [centroid_vsub_point_eq_smul_vsub, smul_smul]
  field_simp [div_eq_inv_mul, NeZero.ne (n : k)]

/-- Reverse version of `faceOppositeCentroid_vsub_centroid_eq_smul_vsub` -/
theorem centroid_vsub_faceOppositeCentroid_eq_smul_vsub [CharZero k]
    (s : Simplex k P n) (i : Fin (n + 1)) :
    s.centroid -ᵥ s.faceOppositeCentroid i = (1 / n : k) • (s.points i -ᵥ s.centroid) := by
  rw [point_vsub_centroid_eq_smul_vsub, smul_smul]
  field_simp [div_eq_inv_mul, NeZero.ne (n : k)]

/-- The centroid of an n-simplex can be obtained from a vertex by adding
`n` times the vector from the centroid to the `faceOppositeCentroid`. -/
theorem centroid_eq_smul_vsub_vadd_point [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) :
    s.centroid = (n : k) • (s.faceOppositeCentroid i -ᵥ s.centroid) +ᵥ s.points i := by
  rw [← centroid_vsub_point_eq_smul_vsub, vsub_vadd]

/-- The point `faceOppositeCentroid` of an n-simplex can be obtained from
the centroid by adding `(1 / n)` times the vector from the vertex to the centroid. -/
theorem faceOppositeCentroid_eq_smul_vsub_vadd_point [CharZero k] (s : Simplex k P n)
    (i : Fin (n + 1)) :
    s.faceOppositeCentroid i = (1 / n : k) • (s.centroid -ᵥ s.points i) +ᵥ s.centroid := by
  rw [centroid_vsub_point_eq_smul_vsub, eq_vadd_iff_vsub_eq, smul_smul]
  field_simp [div_eq_inv_mul, NeZero.ne (n : k)]

/-- The centroid, a vertex, and the corresponding `faceOppositeCentroid` of a simplex are collinear.
-/
theorem collinear_point_centroid_faceOppositeCentroid [CharZero k] (s : Simplex k P n)
    (i : Fin (n + 1)) :
    Collinear k {s.points i, s.centroid, s.faceOppositeCentroid i} := by
  apply collinear_insert_of_mem_affineSpan_pair
  have h : s.points i = (-n : k) • (s.faceOppositeCentroid i -ᵥ s.centroid) +ᵥ s.centroid :=by
    rw [← neg_vsub_eq_vsub_rev, neg_smul_neg, ← point_vsub_centroid_eq_smul_vsub, vsub_vadd]
  rw [h]
  exact smul_vsub_vadd_mem_affineSpan_pair _ _ _

section median

/-- The median of a simplex is the line through a vertex and its corresponding
 `faceOppositeCentroid`.
-/
def median (s : Simplex k P n) (i : Fin (n + 1)) : AffineSubspace k P :=
  line[k, s.points i, s.faceOppositeCentroid i]

/-- The `faceOppositeCentroid` lines on the median through the corresponding vertex. -/
theorem faceOppositeCentroid_mem_median (s : Simplex k P n) (i : Fin (n + 1)) :
    s.faceOppositeCentroid i ∈ s.median i := by
  simp [median, right_mem_affineSpan_pair]

/-- A vertex lies on its median. -/
theorem point_mem_median (s : Simplex k P n) (i : Fin (n + 1)) :
    s.points i ∈ s.median i := by
  simp [median, left_mem_affineSpan_pair]

/-- The centroid lies on the median from any vertex. -/
theorem centroid_mem_median [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) :
  s.centroid ∈ s.median i := by
  rw [median]
  have h : s.centroid = ((n : k) * (1 / (n + 1))) • (s.faceOppositeCentroid i -ᵥ s.points i)
    +ᵥ s.points i := by
    rw [eq_vadd_iff_vsub_eq, centroid_vsub_point_eq_smul_vsub,
      faceOppositeCentroid_vsub_point_eq_smul_vsub, smul_smul, one_div, mul_assoc,
      inv_mul_cancel₀ (by norm_cast), mul_one]
  rw [h]
  exact smul_vsub_vadd_mem_affineSpan_pair _ _ _

/-- The median through a vertex is the same affine span of that vertex and the centroid. -/
theorem median_eq_affineSpan_point_centroid [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) :
    s.median i = affineSpan k {s.points i, s.centroid} := by
  have h1 : s.median i ≤ affineSpan k {s.points i, s.centroid} := by
    unfold median
    apply affineSpan_pair_le_of_right_mem
    rw [faceOppositeCentroid_eq_smul_vsub_vadd_point]
    have h : (1 / n : k) • (s.centroid -ᵥ s.points i) = (-1 / n : k) • (s.points i -ᵥ s.centroid)
        := by
      rw [← neg_vsub_eq_vsub_rev]
      have : -(s.points i -ᵥ s.centroid) = (-1 : k) • (s.points i -ᵥ s.centroid) := by simp
      rw [this, smul_smul]
      congr 1
      field_simp [div_eq_inv_mul, NeZero.ne (n : k)]
    rw [h]
    exact smul_vsub_rev_vadd_mem_affineSpan_pair _ _ _
  have h2 : affineSpan k {s.points i, s.centroid} ≤ s.median i := by
    rw [median]
    apply affineSpan_pair_le_of_right_mem
    exact centroid_mem_median s i
  exact le_antisymm h1 h2

/-- The medians of a simplex are concurrent at its centroid. -/
theorem eq_centroid_of_forall_mem_median [CharZero k] (s : Simplex k P n) {hn : 1 < n} {p : P}
    (h : ∀ i, p ∈ s.median i) :
    p = s.centroid := by
  rw [← vsub_eq_zero_iff_eq]
  set i₀ : Fin (n+1) := 0
  have hp : p = (p -ᵥ s.centroid) +ᵥ s.centroid := by rw [vsub_vadd]
  let s' : Finset (Fin (n + 1)) := {i₀}ᶜ
  let u : s' → V := fun i => s.points i -ᵥ s.centroid
  have h_span : ∀ i : s', p -ᵥ s.centroid ∈ (Submodule.span k ({u i} : Set V)) := by
    intro i
    have hi := h i
    grind only [median_eq_affineSpan_point_centroid, vadd_right_mem_affineSpan_pair,
      Submodule.smul_mem, Submodule.mem_span_singleton_self]
  have hi : LinearIndependent k u := by
    set p : Fin (n + 1) → P := fun x => if x = i₀ then s.centroid else s.points x
    have hindep : AffineIndependent k p := by
      have := affineIndependent_points_update_centroid s i₀
      unfold Function.update at this; simp at this; exact this
    have h1 := (affineIndependent_iff_linearIndependent_vsub k p i₀).mp hindep
    simp_rw [ne_eq, p] at h1
    set f : {x // x ∈ ({i₀}ᶜ : Finset (Fin (n+1)))} → {x // x ≠ i₀} :=
      have h (x : {x // x ∈ ({i₀}ᶜ : Finset (Fin (n+1)))}) : x.val ≠ i₀ := by
        grind [mem_compl, Finset.notMem_singleton]
      fun x => ⟨x.val, h x⟩
    have f_inj : Function.Injective f := by intro x y hxy; grind
    have h2 := h1.comp f f_inj
    convert h2 using 1
    grind only [if_neg, mem_compl, Finset.notMem_singleton]
  have he : ∃ i j : s', i ≠ j := by
    simp only [ne_eq, Subtype.exists, Subtype.mk.injEq, exists_prop]
    have hcard : s'.card = n := by
      rw [Finset.card_compl, Fintype.card_fin, card_singleton, add_tsub_cancel_right]
    have hcard' : 1 < #s' := by grind
    rw [Finset.one_lt_card_iff] at hcard'
    grind
  choose i j hij using he
  have h_ij : Disjoint ({i} : Set {x // x ∈ s'}) {j} := by simp [hij]
  have h_disjoint : Disjoint (Submodule.span k {u i}) (Submodule.span k {u j}) := by
    simp_rw [← Set.image_singleton, hi.disjoint_span_image h_ij]
  exact Submodule.disjoint_def.1 h_disjoint _ (h_span i) (h_span j)

end median

end Simplex

end Affine
