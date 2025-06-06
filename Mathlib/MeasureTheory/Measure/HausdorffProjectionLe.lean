/-
Copyright (c) 2025 Francesco Nishanil Chotuck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francesco Nishanil Chotuck
-/

import Mathlib.MeasureTheory.Measure.Haar.Disintegration
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Orthogonal Projections and Hausdorff Measure

This file proves that Hausdorff measure is non-increasing under orthogonal projection
onto a finite-dimensional Euclidean subspace.

## Main results

* `hausdorffMeasure_orthogonalProjection_le`: The `s`-dimensional Hausdorff
  measure of the projection of a set is at most the measure of the original set.

## References

This formalisation is based on Lemma 3.5 from:

- Julian Fox, *Besicovitch Sets, Kakeya Sets, and Their Properties*,
  University of Chicago REU, 2021.
  https://math.uchicago.edu/~may/REU2021/REUPapers/Fox.pdf
-/

open ENNReal MeasureTheory Submodule

/--
In a finite-dimensional Euclidean space, the norm of the orthogonal projection
of a vector `v` onto a subspace `V` is less than or equal to the norm of `v`.
-/
lemma norm_orthogonalProjection_le (n : ℕ)
  (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
  (v : EuclideanSpace ℝ (Fin n)) :
    ‖orthogonalProjection V v‖ ≤ ‖v‖ := by
  -- Use the definition of operator norm to bound the projection of v
  have h₁ : ‖orthogonalProjection V v‖ ≤ ‖orthogonalProjection V‖ * ‖v‖ := by
    apply ContinuousLinearMap.le_opNorm
  -- Use the known fact that the operator norm of an orthogonal projection is at most 1
  have h₂ : ‖orthogonalProjection V‖ ≤ 1 := by
    apply orthogonalProjection_norm_le
  -- Combine the inequalities to obtain the final bound
  have h₃ : ‖orthogonalProjection V‖ * ‖v‖ ≤ ‖v‖ := by
    calc
      ‖orthogonalProjection V‖ * ‖v‖ ≤ 1 * ‖v‖ := by
        gcongr
      _ = ‖v‖ := by
        simp only [one_mul]
  exact le_trans h₁ h₃

/--
The orthogonal projection onto a subspace `V` in a finite-dimensional Euclidean space
is a `1`-Lipschitz function.
-/
lemma lipschitzWith_orthogonalProjection (n : ℕ)
  (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    LipschitzWith 1 (orthogonalProjection V) := by
  -- Apply the constructor for a function being 1-Lipschitz
  apply LipschitzWith.mk_one
  intro x y
  -- Express distances using the norm
  rw [dist_eq_norm, dist_eq_norm]
  -- Use linearity of projection to factor out subtraction
  calc
    ‖orthogonalProjection V x - orthogonalProjection V y‖
      = ‖orthogonalProjection V (x - y)‖ := by
        simp only [AddSubgroupClass.coe_norm, AddSubgroupClass.coe_sub, map_sub]
    -- Apply previously proven bound on the projection of a vector
    _ ≤ ‖x - y‖ := by apply norm_orthogonalProjection_le

variable (n k : ℕ) (W : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (A : Set (EuclideanSpace ℝ (Fin n)))
  (h : Module.finrank ℝ W = k)

/--
Let `A` be a subset of `ℝⁿ` and `W` a `k`-dimensional subspace. Then the `s`-dimensional
Hausdorff measure of the orthogonal projection of `A` onto `W` is less than or equal to the
`s`-dimensional Hausdorff measure of `A`.
-/
lemma hausdorffMeasure_orthogonalProjection_le (s: NNReal) (hs : 0 ≤ s.toReal):
    μH[s.toReal] (orthogonalProjection W '' A) ≤ μH[s.toReal] A := by
  -- Orthogonal projection is 1-Lipschitz in Euclidean space.
  have h_Lipschitz : LipschitzWith 1 (orthogonalProjection W) := by
    apply lipschitzWith_orthogonalProjection
  -- Apply the general inequality for Hausdorff measure under Lipschitz maps.
  -- Since the Lipschitz constant is 1, the multiplicative factor is 1^s = 1.
  have h : μH[s.toReal] (orthogonalProjection W '' A)
      ≤ (1 : ENNReal) ^ (s.toReal) * μH[s.toReal] A := by
    apply LipschitzWith.hausdorffMeasure_image_le
    exact h_Lipschitz
    exact hs
  -- Simplify the bound using 1^s = 1 and 1 · μH = μH.
  simp only [one_rpow, one_mul] at h
  exact h
