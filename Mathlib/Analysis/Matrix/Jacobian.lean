/-
Copyright (c) 2026 Zebo Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zebo Liu
-/
module
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Matrix.Normed

/-!
# Jacobian matrix for matrix-valued functions of matrix variables

For a function `F : Matrix m n 𝕜 → Matrix p q 𝕜`, we define a Jacobian matrix
`jacobianMatrix F X : Matrix (p × q) (m × n) 𝕜` at a point `X`.

The entry `jacobianMatrix F X (i, k) (j, l)` is the `(i, k)`-entry of the Fréchet derivative
`fderiv 𝕜 F X` applied to the standard basis matrix `Matrix.single j l 1`.

To avoid instance-mismatch issues, we fix the matrix norm/topology *locally* to the Frobenius one.
-/

@[expose] public section

open scoped BigOperators Matrix.Norms.Frobenius

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace
attribute [local instance] Fintype.ofFinite

namespace Matrix

/-!
## Jacobian matrix
-/

section Jacobian

variable {𝕜 m n p q : Type*}
variable [NontriviallyNormedField 𝕜]
variable [DecidableEq m] [DecidableEq n]
variable (F : Matrix m n 𝕜 → Matrix p q 𝕜) (X : Matrix m n 𝕜)

/-- The Jacobian matrix of a matrix-valued function of a matrix variable.

`jacobianMatrix F X` is indexed by `(p × q)` (output coordinates) and `(m × n)` (input coordinates),
and is defined by
`J[(i, k), (j, l)] = (fderiv 𝕜 F X (Matrix.single j l 1)) i k`.
-/
noncomputable def jacobianMatrix : Matrix (p × q) (m × n) 𝕜 :=
  fun ik jl => fderiv 𝕜 F X (Matrix.single jl.1 jl.2 (1 : 𝕜)) ik.1 ik.2

@[simp]
theorem jacobianMatrix_eq_fderiv_basis
    (ik : p × q) (jl : m × n) :
    jacobianMatrix F X ik jl =
      fderiv 𝕜 F X (Matrix.single jl.1 jl.2 1) ik.1 ik.2 := rfl

/-!
## Evaluating `fderiv` via Jacobian entries
-/

/-- Evaluating `fderiv` via the Jacobian entries:
`(fderiv 𝕜 F X) H` is obtained by contracting the Jacobian with `H`. -/
theorem fderiv_eq_jacobian_mul [Fintype m] [Fintype n]
    (H : Matrix m n 𝕜)
    (i : p) (k : q) :
    (fderiv 𝕜 F X) H i k =
      ∑ j : m, ∑ l : n, jacobianMatrix F X (i, k) (j, l) * H j l := by
  classical
  have h_decomp : H = ∑ j : m, ∑ l : n, H j l • Matrix.single j l 1 := by
    simpa using Matrix.matrix_eq_sum_single H
  conv_lhs => rw [h_decomp]
  simp [-smul_single, Matrix.sum_apply, mul_comm]

end Jacobian

/-!
## Chain rule
-/

section ChainRule

variable {𝕜 m n p q r s : Type*}
variable [NontriviallyNormedField 𝕜]
variable (F : Matrix m n 𝕜 → Matrix p q 𝕜)
variable (G : Matrix p q 𝕜 → Matrix r s 𝕜)
variable (X : Matrix m n 𝕜)

@[simp]
theorem matrix_fderiv_comp
    [Finite m] [Finite n] [Finite p] [Finite q] [Finite r] [Finite s]
    (hF : DifferentiableAt 𝕜 F X)
    (hG : DifferentiableAt 𝕜 G (F X)) :
    fderiv 𝕜 (G ∘ F) X = (fderiv 𝕜 G (F X)).comp (fderiv 𝕜 F X) := by
  simpa using (fderiv_comp X hG hF)

theorem jacobianMatrix_comp
    [Finite m] [Finite n] [Fintype p] [Fintype q] [Finite r] [Finite s]
    [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
    (hF : DifferentiableAt 𝕜 F X)
    (hG : DifferentiableAt 𝕜 G (F X))
    (i : r) (k : s) (j : m) (l : n) :
    jacobianMatrix (G ∘ F) X (i, k) (j, l) =
      ∑ i' : p, ∑ k' : q,
        jacobianMatrix G (F X) (i, k) (i', k') *
          jacobianMatrix F X (i', k') (j, l) := by
  simp only [jacobianMatrix]
  rw [fderiv_comp X hG hF]
  simp only [ContinuousLinearMap.comp_apply]
  exact fderiv_eq_jacobian_mul (m := p) (n := q) (p := r) (q := s)
    G (F X) ((fderiv 𝕜 F X) (Matrix.single j l (1 : 𝕜))) i k

end ChainRule

/-!
## Basic rules
-/

section BasicRules

variable {𝕜 m n p q : Type*}
variable [NontriviallyNormedField 𝕜]
variable [DecidableEq m] [DecidableEq n]

theorem jacobianMatrix_linear
    (L : Matrix m n 𝕜 →L[𝕜] Matrix p q 𝕜)
    (X : Matrix m n 𝕜)
    (i : p) (k : q) (j : m) (l : n) :
    jacobianMatrix (fun Y => L Y) X (i, k) (j, l) =
      L (Matrix.single j l (1 : 𝕜)) i k := by
  simp only [jacobianMatrix, ContinuousLinearMap.fderiv]

theorem jacobianMatrix_id
    (X : Matrix m n 𝕜)
    (i j : m) (k l : n) :
    jacobianMatrix (id : Matrix m n 𝕜 → Matrix m n 𝕜) X (i, k) (j, l) =
      if i = j ∧ k = l then (1 : 𝕜) else 0 := by
  simp only [jacobianMatrix_eq_fderiv_basis, fderiv_id, ContinuousLinearMap.coe_id', id_eq]
  grind

theorem jacobianMatrix_const
    (C : Matrix p q 𝕜) (X : Matrix m n 𝕜)
    (i : p) (k : q) (j : m) (l : n) :
    jacobianMatrix (fun _ : Matrix m n 𝕜 => C) X (i, k) (j, l) = 0 := by
  simp only [jacobianMatrix_eq_fderiv_basis, fderiv_fun_const, Pi.zero_apply,
    ContinuousLinearMap.zero_apply, zero_apply]

section Fintype

variable [Finite m] [Finite n] [Finite p] [Finite q]

theorem jacobianMatrix_add
    (F G : Matrix m n 𝕜 → Matrix p q 𝕜) (X : Matrix m n 𝕜)
    (hF : DifferentiableAt 𝕜 F X) (hG : DifferentiableAt 𝕜 G X)
    (i : p) (k : q) (j : m) (l : n) :
    jacobianMatrix (fun Y => F Y + G Y) X (i, k) (j, l) =
      jacobianMatrix F X (i, k) (j, l) + jacobianMatrix G X (i, k) (j, l) := by
  simp [jacobianMatrix, fderiv_fun_add, *]

theorem jacobianMatrix_smul
    (c : 𝕜) (F : Matrix m n 𝕜 → Matrix p q 𝕜) (X : Matrix m n 𝕜)
    (hF : DifferentiableAt 𝕜 F X)
    (i : p) (k : q) (j : m) (l : n) :
    jacobianMatrix (fun Y => c • F Y) X (i, k) (j, l) =
      c * jacobianMatrix F X (i, k) (j, l) := by
  simp [jacobianMatrix, fderiv_fun_const_smul, *]

end Fintype

end BasicRules

end Matrix
