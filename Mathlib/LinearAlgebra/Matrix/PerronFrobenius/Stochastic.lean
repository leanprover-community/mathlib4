/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michail Karatarakis
-/
module

public import Mathlib.LinearAlgebra.Matrix.PerronFrobenius.Dominance

/-!
# Column-stochastic matrices

Perron–Frobenius consequences for irreducible column-stochastic matrices.

## Main results

* `exists_positive_eigenvector_of_irreducible_stochastic`: an irreducible column-stochastic
  matrix has a unique stationary distribution in the standard simplex.

## References

* [E. Seneta, *Non-negative Matrices and Markov Chains*][seneta2006]

## Tags

stochastic matrix, stationary distribution, Perron–Frobenius theorem
-/

@[expose] public section

namespace Matrix

open CollatzWielandt

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- An irreducible column-stochastic matrix has a unique stationary vector in the simplex. -/
theorem exists_positive_eigenvector_of_irreducible_stochastic
    {A : Matrix n n ℝ} (hA_irred : A.IsIrreducible) (h_col_stoch : ∀ j, ∑ i, A i j = 1) :
    ∃! v : stdSimplex ℝ n, A *ᵥ v.val = v.val := by
  have hA_nonneg := hA_irred.1
  have h_eig_T : Aᵀ *ᵥ (fun _ ↦ 1) = (1 : ℝ) • (fun _ ↦ 1) := by
    ext i; simp [mulVec_apply, h_col_stoch]
  have r_A_eq_one : perronRoot_alt A = 1 := by
    rw [perronRoot_transpose_eq A hA_irred]
    exact (eigenvalue_is_perron_root_of_positive_eigenvector hA_irred.transpose
      (fun i j ↦ hA_nonneg j i) zero_lt_one (fun _ ↦ zero_lt_one) h_eig_T).symm
  obtain ⟨v, ⟨r, hr_pos, h_eig⟩, _⟩ := pft_irreducible hA_irred
  have v_pos_raw := eigenvector_is_positive_of_irreducible hA_irred h_eig v.property.1
    (ne_zero_of_mem_stdSimplex v.property)
  have h_eig_one : A *ᵥ v.val = v.val := by
    simpa [
      eigenvalue_is_perron_root_of_positive_eigenvector hA_irred hA_nonneg hr_pos v_pos_raw h_eig,
      r_A_eq_one] using h_eig
  refine ⟨v, h_eig_one, fun w hw_eig ↦ Subtype.ext ?_⟩
  have hv_eig' : A *ᵥ v.val = (1 : ℝ) • v.val := by simpa using h_eig_one
  have hw_eig' : A *ᵥ w.val = (1 : ℝ) • w.val := by simpa using hw_eig
  have v_pos := eigenvector_is_positive_of_irreducible hA_irred hv_eig' v.property.1
    (ne_zero_of_mem_stdSimplex v.property)
  have w_pos := eigenvector_is_positive_of_irreducible hA_irred hw_eig' w.property.1
    (ne_zero_of_mem_stdSimplex w.property)
  obtain ⟨c, _, hc_eq⟩ :=
    uniqueness_of_positive_eigenvector_gen hA_irred zero_lt_one v_pos w_pos hv_eig' hw_eig'
  have hc_one : c = 1 := by
    calc c = c * ∑ i, w.val i := by simp [w.property.2]
      _ = ∑ i, v.val i := by simp [hc_eq, smul_eq_mul, ← Finset.mul_sum]
      _ = 1 := v.property.2
  simp [hc_eq, hc_one]

end Matrix
