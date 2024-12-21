/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Manuel Candales
-/
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Geometry.Euclidean.PerpBisector
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Euclidean spaces

This file makes some definitions and proves very basic geometrical
results about real inner product spaces and Euclidean affine spaces.
Results about real inner product spaces that involve the norm and
inner product but not angles generally go in
`Analysis.NormedSpace.InnerProduct`. Results with longer
proofs or more geometrical content generally go in separate files.

## Main definitions

* `EuclideanGeometry.orthogonalProjection` is the orthogonal
  projection of a point onto an affine subspace.

* `EuclideanGeometry.reflection` is the reflection of a point in an
  affine subspace.

## Implementation notes

To declare `P` as the type of points in a Euclidean affine space with
`V` as the type of vectors, use
`[NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]`.
This works better with `outParam` to make
`V` implicit in most cases than having a separate type alias for
Euclidean affine spaces.

Rather than requiring Euclidean affine spaces to be finite-dimensional
(as in the definition on Wikipedia), this is specified only for those
theorems that need it.

## References

* https://en.wikipedia.org/wiki/Euclidean_space

-/

noncomputable section

open RealInnerProductSpace

namespace EuclideanGeometry

/-!
### Geometrical results on Euclidean affine spaces

This section develops some geometrical definitions and results on
Euclidean affine spaces.
-/


variable {V : Type*} {P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P]

/-- The midpoint of the segment AB is the same distance from A as it is from B. -/
theorem dist_left_midpoint_eq_dist_right_midpoint (p1 p2 : P) :
    dist p1 (midpoint ℝ p1 p2) = dist p2 (midpoint ℝ p1 p2) := by
  rw [dist_left_midpoint (𝕜 := ℝ) p1 p2, dist_right_midpoint (𝕜 := ℝ) p1 p2]

/-- The inner product of two vectors given with `weightedVSub`, in
terms of the pairwise distances. -/
theorem inner_weightedVSub {ι₁ : Type*} {s₁ : Finset ι₁} {w₁ : ι₁ → ℝ} (p₁ : ι₁ → P)
    (h₁ : ∑ i ∈ s₁, w₁ i = 0) {ι₂ : Type*} {s₂ : Finset ι₂} {w₂ : ι₂ → ℝ} (p₂ : ι₂ → P)
    (h₂ : ∑ i ∈ s₂, w₂ i = 0) :
    ⟪s₁.weightedVSub p₁ w₁, s₂.weightedVSub p₂ w₂⟫ =
      (-∑ i₁ ∈ s₁, ∑ i₂ ∈ s₂, w₁ i₁ * w₂ i₂ * (dist (p₁ i₁) (p₂ i₂) * dist (p₁ i₁) (p₂ i₂))) /
        2 := by
  rw [Finset.weightedVSub_apply, Finset.weightedVSub_apply,
    inner_sum_smul_sum_smul_of_sum_eq_zero _ h₁ _ h₂]
  simp_rw [vsub_sub_vsub_cancel_right]
  rcongr (i₁ i₂) <;> rw [dist_eq_norm_vsub V (p₁ i₁) (p₂ i₂)]

/-- The distance between two points given with `affineCombination`,
in terms of the pairwise distances between the points in that
combination. -/
theorem dist_affineCombination {ι : Type*} {s : Finset ι} {w₁ w₂ : ι → ℝ} (p : ι → P)
    (h₁ : ∑ i ∈ s, w₁ i = 1) (h₂ : ∑ i ∈ s, w₂ i = 1) : by
      have a₁ := s.affineCombination ℝ p w₁
      have a₂ := s.affineCombination ℝ p w₂
      exact dist a₁ a₂ * dist a₁ a₂ = (-∑ i₁ ∈ s, ∑ i₂ ∈ s,
        (w₁ - w₂) i₁ * (w₁ - w₂) i₂ * (dist (p i₁) (p i₂) * dist (p i₁) (p i₂))) / 2 := by
  dsimp only
  rw [dist_eq_norm_vsub V (s.affineCombination ℝ p w₁) (s.affineCombination ℝ p w₂), ←
    @inner_self_eq_norm_mul_norm ℝ, Finset.affineCombination_vsub]
  have h : (∑ i ∈ s, (w₁ - w₂) i) = 0 := by
    simp_rw [Pi.sub_apply, Finset.sum_sub_distrib, h₁, h₂, sub_self]
  exact inner_weightedVSub p h p h

-- Porting note: `inner_vsub_vsub_of_dist_eq_of_dist_eq` moved to `PerpendicularBisector`

/-- The squared distance between points on a line (expressed as a
multiple of a fixed vector added to a point) and another point,
expressed as a quadratic. -/
theorem dist_smul_vadd_sq (r : ℝ) (v : V) (p₁ p₂ : P) :
    dist (r • v +ᵥ p₁) p₂ * dist (r • v +ᵥ p₁) p₂ =
      ⟪v, v⟫ * r * r + 2 * ⟪v, p₁ -ᵥ p₂⟫ * r + ⟪p₁ -ᵥ p₂, p₁ -ᵥ p₂⟫ := by
  rw [dist_eq_norm_vsub V _ p₂, ← real_inner_self_eq_norm_mul_norm, vadd_vsub_assoc,
    real_inner_add_add_self, real_inner_smul_left, real_inner_smul_left, real_inner_smul_right]
  ring

/-- The condition for two points on a line to be equidistant from
another point. -/
theorem dist_smul_vadd_eq_dist {v : V} (p₁ p₂ : P) (hv : v ≠ 0) (r : ℝ) :
    dist (r • v +ᵥ p₁) p₂ = dist p₁ p₂ ↔ r = 0 ∨ r = -2 * ⟪v, p₁ -ᵥ p₂⟫ / ⟪v, v⟫ := by
  conv_lhs =>
    rw [← mul_self_inj_of_nonneg dist_nonneg dist_nonneg, dist_smul_vadd_sq, mul_assoc,
      ← sub_eq_zero, add_sub_assoc, dist_eq_norm_vsub V p₁ p₂, ← real_inner_self_eq_norm_mul_norm,
      sub_self]
  have hvi : ⟪v, v⟫ ≠ 0 := by simpa using hv
  have hd : discrim ⟪v, v⟫ (2 * ⟪v, p₁ -ᵥ p₂⟫) 0 = 2 * ⟪v, p₁ -ᵥ p₂⟫ * (2 * ⟪v, p₁ -ᵥ p₂⟫) := by
    rw [discrim]
    ring
  rw [quadratic_eq_zero_iff hvi hd, neg_add_cancel, zero_div, neg_mul_eq_neg_mul, ←
    mul_sub_right_distrib, sub_eq_add_neg, ← mul_two, mul_assoc, mul_div_assoc, mul_div_mul_left,
    mul_div_assoc]
  norm_num

open AffineSubspace Module

/-- Distances `r₁` `r₂` of `p` from two different points `c₁` `c₂` determine at
most two points `p₁` `p₂` in a two-dimensional subspace containing those points
(two circles intersect in at most two points). -/
theorem eq_of_dist_eq_of_dist_eq_of_mem_of_finrank_eq_two {s : AffineSubspace ℝ P}
    [FiniteDimensional ℝ s.direction] (hd : finrank ℝ s.direction = 2) {c₁ c₂ p₁ p₂ p : P}
    (hc₁s : c₁ ∈ s) (hc₂s : c₂ ∈ s) (hp₁s : p₁ ∈ s) (hp₂s : p₂ ∈ s) (hps : p ∈ s) {r₁ r₂ : ℝ}
    (hc : c₁ ≠ c₂) (hp : p₁ ≠ p₂) (hp₁c₁ : dist p₁ c₁ = r₁) (hp₂c₁ : dist p₂ c₁ = r₁)
    (hpc₁ : dist p c₁ = r₁) (hp₁c₂ : dist p₁ c₂ = r₂) (hp₂c₂ : dist p₂ c₂ = r₂)
    (hpc₂ : dist p c₂ = r₂) : p = p₁ ∨ p = p₂ := by
  have ho : ⟪c₂ -ᵥ c₁, p₂ -ᵥ p₁⟫ = 0 :=
    inner_vsub_vsub_of_dist_eq_of_dist_eq (hp₁c₁.trans hp₂c₁.symm) (hp₁c₂.trans hp₂c₂.symm)
  have hop : ⟪c₂ -ᵥ c₁, p -ᵥ p₁⟫ = 0 :=
    inner_vsub_vsub_of_dist_eq_of_dist_eq (hp₁c₁.trans hpc₁.symm) (hp₁c₂.trans hpc₂.symm)
  let b : Fin 2 → V := ![c₂ -ᵥ c₁, p₂ -ᵥ p₁]
  have hb : LinearIndependent ℝ b := by
    refine linearIndependent_of_ne_zero_of_inner_eq_zero ?_ ?_
    · intro i
      fin_cases i <;> simp [b, hc.symm, hp.symm]
    · intro i j hij
      fin_cases i <;> fin_cases j <;> try exact False.elim (hij rfl)
      · exact ho
      · rw [real_inner_comm]
        exact ho
  have hbs : Submodule.span ℝ (Set.range b) = s.direction := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le, Set.range_subset_iff]
      intro i
      fin_cases i
      · exact vsub_mem_direction hc₂s hc₁s
      · exact vsub_mem_direction hp₂s hp₁s
    · rw [finrank_span_eq_card hb, Fintype.card_fin, hd]
  have hv : ∀ v ∈ s.direction, ∃ t₁ t₂ : ℝ, v = t₁ • (c₂ -ᵥ c₁) + t₂ • (p₂ -ᵥ p₁) := by
    intro v hv
    have hr : Set.range b = {c₂ -ᵥ c₁, p₂ -ᵥ p₁} := by
      have hu : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
      classical
      rw [← Fintype.coe_image_univ, hu]
      simp [b]
    rw [← hbs, hr, Submodule.mem_span_insert] at hv
    rcases hv with ⟨t₁, v', hv', hv⟩
    rw [Submodule.mem_span_singleton] at hv'
    rcases hv' with ⟨t₂, rfl⟩
    exact ⟨t₁, t₂, hv⟩
  rcases hv (p -ᵥ p₁) (vsub_mem_direction hps hp₁s) with ⟨t₁, t₂, hpt⟩
  simp only [hpt, inner_add_right, inner_smul_right, ho, mul_zero, add_zero,
    mul_eq_zero, inner_self_eq_zero, vsub_eq_zero_iff_eq, hc.symm, or_false] at hop
  rw [hop, zero_smul, zero_add, ← eq_vadd_iff_vsub_eq] at hpt
  subst hpt
  have hp' : (p₂ -ᵥ p₁ : V) ≠ 0 := by simp [hp.symm]
  have hp₂ : dist ((1 : ℝ) • (p₂ -ᵥ p₁) +ᵥ p₁) c₁ = r₁ := by simp [hp₂c₁]
  rw [← hp₁c₁, dist_smul_vadd_eq_dist _ _ hp'] at hpc₁ hp₂
  simp only [one_ne_zero, false_or] at hp₂
  rw [hp₂.symm] at hpc₁
  cases' hpc₁ with hpc₁ hpc₁ <;> simp [hpc₁]

/-- Distances `r₁` `r₂` of `p` from two different points `c₁` `c₂` determine at
most two points `p₁` `p₂` in two-dimensional space (two circles intersect in at
most two points). -/
theorem eq_of_dist_eq_of_dist_eq_of_finrank_eq_two [FiniteDimensional ℝ V] (hd : finrank ℝ V = 2)
    {c₁ c₂ p₁ p₂ p : P} {r₁ r₂ : ℝ} (hc : c₁ ≠ c₂) (hp : p₁ ≠ p₂) (hp₁c₁ : dist p₁ c₁ = r₁)
    (hp₂c₁ : dist p₂ c₁ = r₁) (hpc₁ : dist p c₁ = r₁) (hp₁c₂ : dist p₁ c₂ = r₂)
    (hp₂c₂ : dist p₂ c₂ = r₂) (hpc₂ : dist p c₂ = r₂) : p = p₁ ∨ p = p₂ :=
  haveI hd' : finrank ℝ (⊤ : AffineSubspace ℝ P).direction = 2 := by
    rw [direction_top, finrank_top]
    exact hd
  eq_of_dist_eq_of_dist_eq_of_mem_of_finrank_eq_two hd' (mem_top ℝ V _) (mem_top ℝ V _)
    (mem_top ℝ V _) (mem_top ℝ V _) (mem_top ℝ V _) hc hp hp₁c₁ hp₂c₁ hpc₁ hp₁c₂ hp₂c₂ hpc₂

/-- The orthogonal projection of a point onto a nonempty affine
subspace, whose direction is complete, as an unbundled function. This
definition is only intended for use in setting up the bundled version
`orthogonalProjection` and should not be used once that is
defined. -/
def orthogonalProjectionFn (s : AffineSubspace ℝ P) [Nonempty s]
    [HasOrthogonalProjection s.direction] (p : P) : P :=
  Classical.choose <|
    inter_eq_singleton_of_nonempty_of_isCompl (nonempty_subtype.mp ‹_›)
      (mk'_nonempty p s.directionᗮ)
      (by
        rw [direction_mk' p s.directionᗮ]
        exact Submodule.isCompl_orthogonal_of_completeSpace)

/-- The intersection of the subspace and the orthogonal subspace
through the given point is the `orthogonalProjectionFn` of that
point onto the subspace. This lemma is only intended for use in
setting up the bundled version and should not be used once that is
defined. -/
theorem inter_eq_singleton_orthogonalProjectionFn {s : AffineSubspace ℝ P} [Nonempty s]
    [HasOrthogonalProjection s.direction] (p : P) :
    (s : Set P) ∩ mk' p s.directionᗮ = {orthogonalProjectionFn s p} :=
  Classical.choose_spec <|
    inter_eq_singleton_of_nonempty_of_isCompl (nonempty_subtype.mp ‹_›)
      (mk'_nonempty p s.directionᗮ)
      (by
        rw [direction_mk' p s.directionᗮ]
        exact Submodule.isCompl_orthogonal_of_completeSpace)

/-- The `orthogonalProjectionFn` lies in the given subspace. This
lemma is only intended for use in setting up the bundled version and
should not be used once that is defined. -/
theorem orthogonalProjectionFn_mem {s : AffineSubspace ℝ P} [Nonempty s]
    [HasOrthogonalProjection s.direction] (p : P) : orthogonalProjectionFn s p ∈ s := by
  rw [← mem_coe, ← Set.singleton_subset_iff, ← inter_eq_singleton_orthogonalProjectionFn]
  exact Set.inter_subset_left

/-- The `orthogonalProjectionFn` lies in the orthogonal
subspace. This lemma is only intended for use in setting up the
bundled version and should not be used once that is defined. -/
theorem orthogonalProjectionFn_mem_orthogonal {s : AffineSubspace ℝ P} [Nonempty s]
    [HasOrthogonalProjection s.direction] (p : P) :
    orthogonalProjectionFn s p ∈ mk' p s.directionᗮ := by
  rw [← mem_coe, ← Set.singleton_subset_iff, ← inter_eq_singleton_orthogonalProjectionFn]
  exact Set.inter_subset_right

/-- Subtracting `p` from its `orthogonalProjectionFn` produces a
result in the orthogonal direction. This lemma is only intended for
use in setting up the bundled version and should not be used once that
is defined. -/
theorem orthogonalProjectionFn_vsub_mem_direction_orthogonal {s : AffineSubspace ℝ P} [Nonempty s]
    [HasOrthogonalProjection s.direction] (p : P) :
    orthogonalProjectionFn s p -ᵥ p ∈ s.directionᗮ :=
  direction_mk' p s.directionᗮ ▸
    vsub_mem_direction (orthogonalProjectionFn_mem_orthogonal p) (self_mem_mk' _ _)

attribute [local instance] AffineSubspace.toAddTorsor

/-- The orthogonal projection of a point onto a nonempty affine
subspace, whose direction is complete. The corresponding linear map
(mapping a vector to the difference between the projections of two
points whose difference is that vector) is the `orthogonalProjection`
for real inner product spaces, onto the direction of the affine
subspace being projected onto. -/
nonrec def orthogonalProjection (s : AffineSubspace ℝ P) [Nonempty s]
    [HasOrthogonalProjection s.direction] : P →ᵃ[ℝ] s where
  toFun p := ⟨orthogonalProjectionFn s p, orthogonalProjectionFn_mem p⟩
  linear := orthogonalProjection s.direction
  map_vadd' p v := by
    have hs : ((orthogonalProjection s.direction) v : V) +ᵥ orthogonalProjectionFn s p ∈ s :=
      vadd_mem_of_mem_direction (orthogonalProjection s.direction v).2
        (orthogonalProjectionFn_mem p)
    have ho :
      ((orthogonalProjection s.direction) v : V) +ᵥ orthogonalProjectionFn s p ∈
        mk' (v +ᵥ p) s.directionᗮ := by
      rw [← vsub_right_mem_direction_iff_mem (self_mem_mk' _ _) _, direction_mk',
        vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, add_comm, add_sub_assoc]
      refine Submodule.add_mem _ (orthogonalProjectionFn_vsub_mem_direction_orthogonal p) ?_
      rw [Submodule.mem_orthogonal']
      intro w hw
      rw [← neg_sub, inner_neg_left, orthogonalProjection_inner_eq_zero _ w hw, neg_zero]
    have hm :
      ((orthogonalProjection s.direction) v : V) +ᵥ orthogonalProjectionFn s p ∈
        ({orthogonalProjectionFn s (v +ᵥ p)} : Set P) := by
      rw [← inter_eq_singleton_orthogonalProjectionFn (v +ᵥ p)]
      exact Set.mem_inter hs ho
    rw [Set.mem_singleton_iff] at hm
    ext
    exact hm.symm

@[simp]
theorem orthogonalProjectionFn_eq {s : AffineSubspace ℝ P} [Nonempty s]
    [HasOrthogonalProjection s.direction] (p : P) :
    orthogonalProjectionFn s p = orthogonalProjection s p :=
  rfl

/-- The linear map corresponding to `orthogonalProjection`. -/
@[simp]
theorem orthogonalProjection_linear {s : AffineSubspace ℝ P} [Nonempty s]
    [HasOrthogonalProjection s.direction] :
    (orthogonalProjection s).linear = _root_.orthogonalProjection s.direction :=
  rfl

/-- The intersection of the subspace and the orthogonal subspace
through the given point is the `orthogonalProjection` of that point
onto the subspace. -/
theorem inter_eq_singleton_orthogonalProjection {s : AffineSubspace ℝ P} [Nonempty s]
    [HasOrthogonalProjection s.direction] (p : P) :
    (s : Set P) ∩ mk' p s.directionᗮ = {↑(orthogonalProjection s p)} := by
  rw [← orthogonalProjectionFn_eq]
  exact inter_eq_singleton_orthogonalProjectionFn p

/-- The `orthogonalProjection` lies in the given subspace. -/
theorem orthogonalProjection_mem {s : AffineSubspace ℝ P} [Nonempty s]
    [HasOrthogonalProjection s.direction] (p : P) : ↑(orthogonalProjection s p) ∈ s :=
  (orthogonalProjection s p).2

/-- The `orthogonalProjection` lies in the orthogonal subspace. -/
theorem orthogonalProjection_mem_orthogonal (s : AffineSubspace ℝ P) [Nonempty s]
    [HasOrthogonalProjection s.direction] (p : P) :
    ↑(orthogonalProjection s p) ∈ mk' p s.directionᗮ :=
  orthogonalProjectionFn_mem_orthogonal p

/-- Subtracting a point in the given subspace from the
`orthogonalProjection` produces a result in the direction of the
given subspace. -/
theorem orthogonalProjection_vsub_mem_direction {s : AffineSubspace ℝ P} [Nonempty s]
    [HasOrthogonalProjection s.direction] {p1 : P} (p2 : P) (hp1 : p1 ∈ s) :
    ↑(orthogonalProjection s p2 -ᵥ ⟨p1, hp1⟩ : s.direction) ∈ s.direction :=
  (orthogonalProjection s p2 -ᵥ ⟨p1, hp1⟩ : s.direction).2

/-- Subtracting the `orthogonalProjection` from a point in the given
subspace produces a result in the direction of the given subspace. -/
theorem vsub_orthogonalProjection_mem_direction {s : AffineSubspace ℝ P} [Nonempty s]
    [HasOrthogonalProjection s.direction] {p1 : P} (p2 : P) (hp1 : p1 ∈ s) :
    ↑((⟨p1, hp1⟩ : s) -ᵥ orthogonalProjection s p2 : s.direction) ∈ s.direction :=
  ((⟨p1, hp1⟩ : s) -ᵥ orthogonalProjection s p2 : s.direction).2

/-- A point equals its orthogonal projection if and only if it lies in
the subspace. -/
theorem orthogonalProjection_eq_self_iff {s : AffineSubspace ℝ P} [Nonempty s]
    [HasOrthogonalProjection s.direction] {p : P} : ↑(orthogonalProjection s p) = p ↔ p ∈ s := by
  constructor
  · exact fun h => h ▸ orthogonalProjection_mem p
  · intro h
    have hp : p ∈ (s : Set P) ∩ mk' p s.directionᗮ := ⟨h, self_mem_mk' p _⟩
    rw [inter_eq_singleton_orthogonalProjection p] at hp
    symm
    exact hp

@[simp]
theorem orthogonalProjection_mem_subspace_eq_self {s : AffineSubspace ℝ P} [Nonempty s]
    [HasOrthogonalProjection s.direction] (p : s) : orthogonalProjection s p = p := by
  ext
  rw [orthogonalProjection_eq_self_iff]
  exact p.2

instance : HasOrthogonalProjection (⊤ : AffineSubspace ℝ P).direction := by
  rw [direction_top]
  infer_instance

@[simp]
theorem orthogonalProjection_top :
    orthogonalProjection (⊤ : AffineSubspace ℝ P) = (topEquiv ℝ V P).symm := by
  ext p
  lift p to (⊤ : AffineSubspace ℝ P) using trivial
  simp

/-- Orthogonal projection is idempotent. -/
theorem orthogonalProjection_orthogonalProjection (s : AffineSubspace ℝ P) [Nonempty s]
    [HasOrthogonalProjection s.direction] (p : P) :
    orthogonalProjection s (orthogonalProjection s p) = orthogonalProjection s p := by
  ext
  rw [orthogonalProjection_eq_self_iff]
  exact orthogonalProjection_mem p

theorem eq_orthogonalProjection_of_eq_subspace {s s' : AffineSubspace ℝ P} [Nonempty s]
    [Nonempty s'] [HasOrthogonalProjection s.direction] [HasOrthogonalProjection s'.direction]
    (h : s = s') (p : P) : (orthogonalProjection s p : P) = (orthogonalProjection s' p : P) := by
  subst h
  rfl

/-- The distance to a point's orthogonal projection is 0 iff it lies in the subspace. -/
theorem dist_orthogonalProjection_eq_zero_iff {s : AffineSubspace ℝ P} [Nonempty s]
    [HasOrthogonalProjection s.direction] {p : P} :
    dist p (orthogonalProjection s p) = 0 ↔ p ∈ s := by
  rw [dist_comm, dist_eq_zero, orthogonalProjection_eq_self_iff]

/-- The distance between a point and its orthogonal projection is
nonzero if it does not lie in the subspace. -/
theorem dist_orthogonalProjection_ne_zero_of_not_mem {s : AffineSubspace ℝ P} [Nonempty s]
    [HasOrthogonalProjection s.direction] {p : P} (hp : p ∉ s) :
    dist p (orthogonalProjection s p) ≠ 0 :=
  mt dist_orthogonalProjection_eq_zero_iff.mp hp

/-- Subtracting `p` from its `orthogonalProjection` produces a result
in the orthogonal direction. -/
theorem orthogonalProjection_vsub_mem_direction_orthogonal (s : AffineSubspace ℝ P) [Nonempty s]
    [HasOrthogonalProjection s.direction] (p : P) :
    (orthogonalProjection s p : P) -ᵥ p ∈ s.directionᗮ :=
  orthogonalProjectionFn_vsub_mem_direction_orthogonal p

/-- Subtracting the `orthogonalProjection` from `p` produces a result
in the orthogonal direction. -/
theorem vsub_orthogonalProjection_mem_direction_orthogonal (s : AffineSubspace ℝ P) [Nonempty s]
    [HasOrthogonalProjection s.direction] (p : P) : p -ᵥ orthogonalProjection s p ∈ s.directionᗮ :=
  direction_mk' p s.directionᗮ ▸
    vsub_mem_direction (self_mem_mk' _ _) (orthogonalProjection_mem_orthogonal s p)

/-- Subtracting the `orthogonalProjection` from `p` produces a result in the kernel of the linear
part of the orthogonal projection. -/
theorem orthogonalProjection_vsub_orthogonalProjection (s : AffineSubspace ℝ P) [Nonempty s]
    [HasOrthogonalProjection s.direction] (p : P) :
    _root_.orthogonalProjection s.direction (p -ᵥ orthogonalProjection s p) = 0 := by
  apply orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero
  intro c hc
  rw [← neg_vsub_eq_vsub_rev, inner_neg_right,
    orthogonalProjection_vsub_mem_direction_orthogonal s p c hc, neg_zero]

/-- Adding a vector to a point in the given subspace, then taking the
orthogonal projection, produces the original point if the vector was
in the orthogonal direction. -/
theorem orthogonalProjection_vadd_eq_self {s : AffineSubspace ℝ P} [Nonempty s]
    [HasOrthogonalProjection s.direction] {p : P} (hp : p ∈ s) {v : V} (hv : v ∈ s.directionᗮ) :
    orthogonalProjection s (v +ᵥ p) = ⟨p, hp⟩ := by
  have h := vsub_orthogonalProjection_mem_direction_orthogonal s (v +ᵥ p)
  rw [vadd_vsub_assoc, Submodule.add_mem_iff_right _ hv] at h
  refine (eq_of_vsub_eq_zero ?_).symm
  ext
  refine Submodule.disjoint_def.1 s.direction.orthogonal_disjoint _ ?_ h
  exact (_ : s.direction).2

/-- Adding a vector to a point in the given subspace, then taking the
orthogonal projection, produces the original point if the vector is a
multiple of the result of subtracting a point's orthogonal projection
from that point. -/
theorem orthogonalProjection_vadd_smul_vsub_orthogonalProjection {s : AffineSubspace ℝ P}
    [Nonempty s] [HasOrthogonalProjection s.direction] {p1 : P} (p2 : P) (r : ℝ) (hp : p1 ∈ s) :
    orthogonalProjection s (r • (p2 -ᵥ orthogonalProjection s p2 : V) +ᵥ p1) = ⟨p1, hp⟩ :=
  orthogonalProjection_vadd_eq_self hp
    (Submodule.smul_mem _ _ (vsub_orthogonalProjection_mem_direction_orthogonal s _))

/-- The square of the distance from a point in `s` to `p2` equals the
sum of the squares of the distances of the two points to the
`orthogonalProjection`. -/
theorem dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq
    {s : AffineSubspace ℝ P} [Nonempty s] [HasOrthogonalProjection s.direction] {p1 : P} (p2 : P)
    (hp1 : p1 ∈ s) :
    dist p1 p2 * dist p1 p2 =
      dist p1 (orthogonalProjection s p2) * dist p1 (orthogonalProjection s p2) +
        dist p2 (orthogonalProjection s p2) * dist p2 (orthogonalProjection s p2) := by
  rw [dist_comm p2 _, dist_eq_norm_vsub V p1 _, dist_eq_norm_vsub V p1 _, dist_eq_norm_vsub V _ p2,
    ← vsub_add_vsub_cancel p1 (orthogonalProjection s p2) p2,
    norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero]
  exact Submodule.inner_right_of_mem_orthogonal (vsub_orthogonalProjection_mem_direction p2 hp1)
    (orthogonalProjection_vsub_mem_direction_orthogonal s p2)

/-- The square of the distance between two points constructed by
adding multiples of the same orthogonal vector to points in the same
subspace. -/
theorem dist_sq_smul_orthogonal_vadd_smul_orthogonal_vadd {s : AffineSubspace ℝ P} {p1 p2 : P}
    (hp1 : p1 ∈ s) (hp2 : p2 ∈ s) (r1 r2 : ℝ) {v : V} (hv : v ∈ s.directionᗮ) :
    dist (r1 • v +ᵥ p1) (r2 • v +ᵥ p2) * dist (r1 • v +ᵥ p1) (r2 • v +ᵥ p2) =
      dist p1 p2 * dist p1 p2 + (r1 - r2) * (r1 - r2) * (‖v‖ * ‖v‖) :=
  calc
    dist (r1 • v +ᵥ p1) (r2 • v +ᵥ p2) * dist (r1 • v +ᵥ p1) (r2 • v +ᵥ p2) =
        ‖p1 -ᵥ p2 + (r1 - r2) • v‖ * ‖p1 -ᵥ p2 + (r1 - r2) • v‖ := by
      rw [dist_eq_norm_vsub V (r1 • v +ᵥ p1), vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, sub_smul,
        add_comm, add_sub_assoc]
    _ = ‖p1 -ᵥ p2‖ * ‖p1 -ᵥ p2‖ + ‖(r1 - r2) • v‖ * ‖(r1 - r2) • v‖ :=
      (norm_add_sq_eq_norm_sq_add_norm_sq_real
        (Submodule.inner_right_of_mem_orthogonal (vsub_mem_direction hp1 hp2)
          (Submodule.smul_mem _ _ hv)))
    _ = ‖(p1 -ᵥ p2 : V)‖ * ‖(p1 -ᵥ p2 : V)‖ + |r1 - r2| * |r1 - r2| * ‖v‖ * ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      ring
    _ = dist p1 p2 * dist p1 p2 + (r1 - r2) * (r1 - r2) * (‖v‖ * ‖v‖) := by
      rw [dist_eq_norm_vsub V p1, abs_mul_abs_self, mul_assoc]

/-- Reflection in an affine subspace, which is expected to be nonempty
and complete. The word "reflection" is sometimes understood to mean
specifically reflection in a codimension-one subspace, and sometimes
more generally to cover operations such as reflection in a point. The
definition here, of reflection in an affine subspace, is a more
general sense of the word that includes both those common cases. -/
def reflection (s : AffineSubspace ℝ P) [Nonempty s] [HasOrthogonalProjection s.direction] :
    P ≃ᵃⁱ[ℝ] P :=
  AffineIsometryEquiv.mk'
    (fun p => (↑(orthogonalProjection s p) -ᵥ p) +ᵥ (orthogonalProjection s p : P))
    (_root_.reflection s.direction) (↑(Classical.arbitrary s))
    (by
      intro p
      let v := p -ᵥ ↑(Classical.arbitrary s)
      let a : V := _root_.orthogonalProjection s.direction v
      let b : P := ↑(Classical.arbitrary s)
      have key : ((a +ᵥ b) -ᵥ (v +ᵥ b)) +ᵥ (a +ᵥ b) = (a + a - v) +ᵥ (b -ᵥ b) +ᵥ b := by
        rw [← add_vadd, vsub_vadd_eq_vsub_sub, vsub_vadd, vadd_vsub]
        congr 1
        abel
      dsimp only
      rwa [reflection_apply, (vsub_vadd p b).symm, AffineMap.map_vadd, orthogonalProjection_linear,
        vadd_vsub, orthogonalProjection_mem_subspace_eq_self, two_smul])

/-- The result of reflecting. -/
theorem reflection_apply (s : AffineSubspace ℝ P) [Nonempty s] [HasOrthogonalProjection s.direction]
    (p : P) :
    reflection s p = (↑(orthogonalProjection s p) -ᵥ p) +ᵥ (orthogonalProjection s p : P) :=
  rfl

theorem eq_reflection_of_eq_subspace {s s' : AffineSubspace ℝ P} [Nonempty s] [Nonempty s']
    [HasOrthogonalProjection s.direction] [HasOrthogonalProjection s'.direction] (h : s = s')
    (p : P) : (reflection s p : P) = (reflection s' p : P) := by
  subst h
  rfl

/-- Reflecting twice in the same subspace. -/
@[simp]
theorem reflection_reflection (s : AffineSubspace ℝ P) [Nonempty s]
    [HasOrthogonalProjection s.direction] (p : P) : reflection s (reflection s p) = p := by
  have : ∀ a : s, ∀ b : V, (_root_.orthogonalProjection s.direction) b = 0 →
      reflection s (reflection s (b +ᵥ (a : P))) = b +ᵥ (a : P) := by
    intro _ _ h
    simp [reflection, h]
  rw [← vsub_vadd p (orthogonalProjection s p)]
  exact this (orthogonalProjection s p) _ (orthogonalProjection_vsub_orthogonalProjection s p)

/-- Reflection is its own inverse. -/
@[simp]
theorem reflection_symm (s : AffineSubspace ℝ P) [Nonempty s]
    [HasOrthogonalProjection s.direction] : (reflection s).symm = reflection s := by
  ext
  rw [← (reflection s).injective.eq_iff]
  simp

/-- Reflection is involutive. -/
theorem reflection_involutive (s : AffineSubspace ℝ P) [Nonempty s]
    [HasOrthogonalProjection s.direction] : Function.Involutive (reflection s) :=
  reflection_reflection s

/-- A point is its own reflection if and only if it is in the subspace. -/
theorem reflection_eq_self_iff {s : AffineSubspace ℝ P} [Nonempty s]
    [HasOrthogonalProjection s.direction] (p : P) : reflection s p = p ↔ p ∈ s := by
  rw [← orthogonalProjection_eq_self_iff, reflection_apply]
  constructor
  · intro h
    rw [← @vsub_eq_zero_iff_eq V, vadd_vsub_assoc, ← two_smul ℝ (↑(orthogonalProjection s p) -ᵥ p),
      smul_eq_zero] at h
    norm_num at h
    exact h
  · intro h
    simp [h]

/-- Reflecting a point in two subspaces produces the same result if
and only if the point has the same orthogonal projection in each of
those subspaces. -/
theorem reflection_eq_iff_orthogonalProjection_eq (s₁ s₂ : AffineSubspace ℝ P) [Nonempty s₁]
    [Nonempty s₂] [HasOrthogonalProjection s₁.direction] [HasOrthogonalProjection s₂.direction]
    (p : P) :
    reflection s₁ p = reflection s₂ p ↔
      (orthogonalProjection s₁ p : P) = orthogonalProjection s₂ p := by
  rw [reflection_apply, reflection_apply]
  constructor
  · intro h
    rw [← @vsub_eq_zero_iff_eq V, vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, add_comm, add_sub_assoc,
      vsub_sub_vsub_cancel_right, ←
      two_smul ℝ ((orthogonalProjection s₁ p : P) -ᵥ orthogonalProjection s₂ p), smul_eq_zero] at h
    norm_num at h
    exact h
  · intro h
    rw [h]

/-- The distance between `p₁` and the reflection of `p₂` equals that
between the reflection of `p₁` and `p₂`. -/
theorem dist_reflection (s : AffineSubspace ℝ P) [Nonempty s] [HasOrthogonalProjection s.direction]
    (p₁ p₂ : P) : dist p₁ (reflection s p₂) = dist (reflection s p₁) p₂ := by
  conv_lhs => rw [← reflection_reflection s p₁]
  exact (reflection s).dist_map _ _

/-- A point in the subspace is equidistant from another point and its
reflection. -/
theorem dist_reflection_eq_of_mem (s : AffineSubspace ℝ P) [Nonempty s]
    [HasOrthogonalProjection s.direction] {p₁ : P} (hp₁ : p₁ ∈ s) (p₂ : P) :
    dist p₁ (reflection s p₂) = dist p₁ p₂ := by
  rw [← reflection_eq_self_iff p₁] at hp₁
  convert (reflection s).dist_map p₁ p₂
  rw [hp₁]

/-- The reflection of a point in a subspace is contained in any larger
subspace containing both the point and the subspace reflected in. -/
theorem reflection_mem_of_le_of_mem {s₁ s₂ : AffineSubspace ℝ P} [Nonempty s₁]
    [HasOrthogonalProjection s₁.direction] (hle : s₁ ≤ s₂) {p : P} (hp : p ∈ s₂) :
    reflection s₁ p ∈ s₂ := by
  rw [reflection_apply]
  have ho : ↑(orthogonalProjection s₁ p) ∈ s₂ := hle (orthogonalProjection_mem p)
  exact vadd_mem_of_mem_direction (vsub_mem_direction ho hp) ho

/-- Reflecting an orthogonal vector plus a point in the subspace
produces the negation of that vector plus the point. -/
theorem reflection_orthogonal_vadd {s : AffineSubspace ℝ P} [Nonempty s]
    [HasOrthogonalProjection s.direction] {p : P} (hp : p ∈ s) {v : V} (hv : v ∈ s.directionᗮ) :
    reflection s (v +ᵥ p) = -v +ᵥ p := by
  rw [reflection_apply, orthogonalProjection_vadd_eq_self hp hv, vsub_vadd_eq_vsub_sub]
  simp

/-- Reflecting a vector plus a point in the subspace produces the
negation of that vector plus the point if the vector is a multiple of
the result of subtracting a point's orthogonal projection from that
point. -/
theorem reflection_vadd_smul_vsub_orthogonalProjection {s : AffineSubspace ℝ P} [Nonempty s]
    [HasOrthogonalProjection s.direction] {p₁ : P} (p₂ : P) (r : ℝ) (hp₁ : p₁ ∈ s) :
    reflection s (r • (p₂ -ᵥ orthogonalProjection s p₂) +ᵥ p₁) =
      -(r • (p₂ -ᵥ orthogonalProjection s p₂)) +ᵥ p₁ :=
  reflection_orthogonal_vadd hp₁
    (Submodule.smul_mem _ _ (vsub_orthogonalProjection_mem_direction_orthogonal s _))

end EuclideanGeometry
