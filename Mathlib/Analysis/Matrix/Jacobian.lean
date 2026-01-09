/-
Copyright (c) 2026 Your Name. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Your Name
-/
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Matrix.Normed

/-!
# Jacobian matrix for matrix-valued functions of matrix variables (over `ℝ`)

For a function `F : Matrix m n ℝ → Matrix p q ℝ`, we define a Jacobian matrix
`jacobianMatrix F X : Matrix (p × q) (m × n) ℝ` at a point `X`.

The entry `jacobianMatrix F X (i, k) (j, l)` is the `(i, k)`-entry of the Fréchet derivative
`fderiv ℝ F X` applied to the standard basis matrix `Matrix.single j l 1`.

To avoid instance-mismatch issues, we fix the matrix norm/topology *locally* to the Frobenius one.
-/

noncomputable section

open scoped BigOperators
open scoped Matrix.Norms.Frobenius

/-
Enable Frobenius normed structures locally (do not create global instances).
This provides the `NormedSpace` / `TopologicalSpace` structure needed by `fderiv`.
-/
attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

namespace Matrix

/-!
## Jacobian matrix
-/

section Jacobian

variable {m n p q : Type*}
variable [DecidableEq m] [DecidableEq n]

/-- The Jacobian matrix of a matrix-valued function of a matrix variable.

`jacobianMatrix F X` is indexed by `(p × q)` (output coordinates) and `(m × n)` (input coordinates),
and is defined by
`J[(i, k), (j, l)] = (fderiv ℝ F X (Matrix.single j l 1)) i k`.
-/
def jacobianMatrix
    (F : Matrix m n ℝ → Matrix p q ℝ) (X : Matrix m n ℝ) :
    Matrix (p × q) (m × n) ℝ :=
  fun (i, k) (j, l) => (fderiv ℝ F X (Matrix.single j l (1 : ℝ))) i k

@[simp]
theorem jacobianMatrix_eq_fderiv_basis
    (F : Matrix m n ℝ → Matrix p q ℝ) (X : Matrix m n ℝ)
    (i : p) (k : q) (j : m) (l : n) :
    jacobianMatrix F X (i, k) (j, l) =
      (fderiv ℝ F X) (Matrix.single j l (1 : ℝ)) i k := by
  rfl

/-!
## Evaluating `fderiv` via Jacobian entries
-/

/-- Evaluating `fderiv` via the Jacobian entries:
`(fderiv ℝ F X) H` is obtained by contracting the Jacobian with `H`. -/
theorem fderiv_eq_jacobian_mul [Fintype m] [Fintype n]
    (F : Matrix m n ℝ → Matrix p q ℝ) (X H : Matrix m n ℝ)
    (i : p) (k : q) :
    (fderiv ℝ F X) H i k =
      ∑ j : m, ∑ l : n, jacobianMatrix F X (i, k) (j, l) * H j l := by
  classical
  -- unfold Jacobian entries
  simp only [jacobianMatrix_eq_fderiv_basis]
  -- decompose `H` into the standard basis
  have h_decomp : H = ∑ j : m, ∑ l : n, Matrix.single j l (H j l) := by
    simpa using (Matrix.matrix_eq_sum_single H)
  conv_lhs => rw [h_decomp]
  -- linearity through sums
  simp only [map_sum]
  -- pull out entries `(i, k)`
  rw [Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro l _
  -- rewrite `single j l (H j l)` as a scalar multiple of `single j l 1`
  have hs : Matrix.single j l (H j l) = (H j l) • Matrix.single j l (1 : ℝ) := by
    simp [smul_eq_mul]
  -- apply `map_smul` and commute the scalar
  calc
    (fderiv ℝ F X) (Matrix.single j l (H j l)) i k
        = (fderiv ℝ F X) ((H j l) • Matrix.single j l (1 : ℝ)) i k := by
            rw [hs]
    _ = (H j l) * (fderiv ℝ F X) (Matrix.single j l (1 : ℝ)) i k := by
            rw [map_smul, smul_apply, smul_eq_mul]
    _ = (fderiv ℝ F X) (Matrix.single j l (1 : ℝ)) i k * H j l := by
            simp [mul_comm]

end Jacobian

/-!
## Chain rule
-/

section ChainRule

variable {m n p q r s : Type*}
variable [Fintype m] [Fintype n] [Fintype p] [Fintype q] [Fintype r] [Fintype s]

@[simp]
theorem matrix_fderiv_comp
    (F : Matrix m n ℝ → Matrix p q ℝ)
    (G : Matrix p q ℝ → Matrix r s ℝ)
    (X : Matrix m n ℝ)
    (hF : DifferentiableAt ℝ F X)
    (hG : DifferentiableAt ℝ G (F X)) :
    fderiv ℝ (G ∘ F) X = (fderiv ℝ G (F X)).comp (fderiv ℝ F X) := by
  simpa using (fderiv_comp X hG hF)

theorem jacobianMatrix_comp
    [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
    (F : Matrix m n ℝ → Matrix p q ℝ)
    (G : Matrix p q ℝ → Matrix r s ℝ)
    (X : Matrix m n ℝ)
    (hF : DifferentiableAt ℝ F X)
    (hG : DifferentiableAt ℝ G (F X))
    (i : r) (k : s) (j : m) (l : n) :
    jacobianMatrix (G ∘ F) X (i, k) (j, l) =
      ∑ i' : p, ∑ k' : q,
        jacobianMatrix G (F X) (i, k) (i', k') *
          jacobianMatrix F X (i', k') (j, l) := by
  simp only [jacobianMatrix]
  rw [fderiv_comp X hG hF]
  simp only [ContinuousLinearMap.comp_apply]
  exact fderiv_eq_jacobian_mul (m := p) (n := q) (p := r) (q := s)
    G (F X) ((fderiv ℝ F X) (Matrix.single j l (1 : ℝ))) i k

end ChainRule

/-!
## Basic rules
-/

section BasicRules

variable {m n p q : Type*}
variable [Fintype m] [Fintype n] [Fintype p] [Fintype q]
variable [DecidableEq m] [DecidableEq n]

theorem jacobianMatrix_linear
    (L : Matrix m n ℝ →L[ℝ] Matrix p q ℝ)
    (X : Matrix m n ℝ)
    (i : p) (k : q) (j : m) (l : n) :
    jacobianMatrix (fun Y => L Y) X (i, k) (j, l) =
      L (Matrix.single j l (1 : ℝ)) i k := by
  classical
  simp [jacobianMatrix]

theorem jacobianMatrix_id
    (X : Matrix m n ℝ)
    (i j : m) (k l : n) :
    jacobianMatrix (id : Matrix m n ℝ → Matrix m n ℝ) X (i, k) (j, l) =
      if i = j ∧ k = l then (1 : ℝ) else 0 := by
  classical
  simp [jacobianMatrix]
  by_cases h : (i = j ∧ k = l)
  · rcases h with ⟨rfl, rfl⟩
    simp [Matrix.single_apply_same]
  · have h' : ¬ (j = i ∧ l = k) := by
      intro hji
      apply h
      exact ⟨hji.1.symm, hji.2.symm⟩
    simp [h, Matrix.single_apply_of_ne (i := j) (j := l) (c := (1 : ℝ)) (i' := i) (j' := k) h']

theorem jacobianMatrix_const
    (C : Matrix p q ℝ) (X : Matrix m n ℝ)
    (i : p) (k : q) (j : m) (l : n) :
    jacobianMatrix (fun _ : Matrix m n ℝ => C) X (i, k) (j, l) = 0 := by
  classical
  simp [jacobianMatrix]

theorem jacobianMatrix_add
    (F G : Matrix m n ℝ → Matrix p q ℝ) (X : Matrix m n ℝ)
    (hF : DifferentiableAt ℝ F X) (hG : DifferentiableAt ℝ G X)
    (i : p) (k : q) (j : m) (l : n) :
    jacobianMatrix (fun Y => F Y + G Y) X (i, k) (j, l) =
      jacobianMatrix F X (i, k) (j, l) + jacobianMatrix G X (i, k) (j, l) := by
  unfold jacobianMatrix
  have h_add : (fun Y => F Y + G Y) = fun Y => (F + G) Y := rfl
  rw [h_add]
  rw [fderiv_add hF hG]
  simp only [ContinuousLinearMap.add_apply]
  rfl

theorem jacobianMatrix_smul
    (c : ℝ) (F : Matrix m n ℝ → Matrix p q ℝ) (X : Matrix m n ℝ)
    (hF : DifferentiableAt ℝ F X)
    (i : p) (k : q) (j : m) (l : n) :
    jacobianMatrix (fun Y => c • F Y) X (i, k) (j, l) =
      c * jacobianMatrix F X (i, k) (j, l) := by
  unfold jacobianMatrix
  have h_smul : (fun Y => c • F Y) = fun Y => (c • F) Y := rfl
  rw [h_smul]
  rw [fderiv_const_smul hF]
  simp only [ContinuousLinearMap.smul_apply]
  rfl

end BasicRules

end Matrix
