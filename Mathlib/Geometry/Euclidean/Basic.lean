/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Manuel Candales
-/
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
  simp

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
  rcases hpc₁ with hpc₁ | hpc₁ <;> simp [hpc₁]

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

end EuclideanGeometry
