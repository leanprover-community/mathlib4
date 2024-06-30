/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

#align_import algebra.lie.matrix from "leanprover-community/mathlib"@"55e2dfde0cff928ce5c70926a3f2c7dee3e2dd99"

/-!
# Lie algebras of matrices

An important class of Lie algebras are those arising from the associative algebra structure on
square matrices over a commutative ring. This file provides some very basic definitions whose
primary value stems from their utility when constructing the classical Lie algebras using matrices.

## Main definitions

  * `lieEquivMatrix'`
  * `Matrix.lieConj`
  * `Matrix.reindexLieEquiv`

## Tags

lie algebra, matrix
-/


universe u v w w₁ w₂

section Matrices

open scoped Matrix

variable {R : Type u} [CommRing R]
variable {n : Type w} [DecidableEq n] [Fintype n]

/-- The natural equivalence between linear endomorphisms of finite free modules and square matrices
is compatible with the Lie algebra structures. -/
def lieEquivMatrix' : Module.End R (n → R) ≃ₗ⁅R⁆ Matrix n n R :=
  { LinearMap.toMatrix' with
    map_lie' := fun {T S} => by
      let f := @LinearMap.toMatrix' R _ n n _ _
      change f (T.comp S - S.comp T) = f T * f S - f S * f T
      have h : ∀ T S : Module.End R _, f (T.comp S) = f T * f S := LinearMap.toMatrix'_comp
      rw [map_sub, h, h] }
#align lie_equiv_matrix' lieEquivMatrix'

@[simp]
theorem lieEquivMatrix'_apply (f : Module.End R (n → R)) :
    lieEquivMatrix' f = LinearMap.toMatrix' f :=
  rfl
#align lie_equiv_matrix'_apply lieEquivMatrix'_apply

@[simp]
theorem lieEquivMatrix'_symm_apply (A : Matrix n n R) :
    (@lieEquivMatrix' R _ n _ _).symm A = Matrix.toLin' A :=
  rfl
#align lie_equiv_matrix'_symm_apply lieEquivMatrix'_symm_apply

/-- An invertible matrix induces a Lie algebra equivalence from the space of matrices to itself. -/
def Matrix.lieConj (P : Matrix n n R) (h : Invertible P) : Matrix n n R ≃ₗ⁅R⁆ Matrix n n R :=
  ((@lieEquivMatrix' R _ n _ _).symm.trans (P.toLinearEquiv' h).lieConj).trans lieEquivMatrix'
#align matrix.lie_conj Matrix.lieConj

@[simp]
theorem Matrix.lieConj_apply (P A : Matrix n n R) (h : Invertible P) :
    P.lieConj h A = P * A * P⁻¹ := by
  simp [LinearEquiv.conj_apply, Matrix.lieConj, LinearMap.toMatrix'_comp,
    LinearMap.toMatrix'_toLin']
#align matrix.lie_conj_apply Matrix.lieConj_apply

@[simp]
theorem Matrix.lieConj_symm_apply (P A : Matrix n n R) (h : Invertible P) :
    (P.lieConj h).symm A = P⁻¹ * A * P := by
  simp [LinearEquiv.symm_conj_apply, Matrix.lieConj, LinearMap.toMatrix'_comp,
    LinearMap.toMatrix'_toLin']
#align matrix.lie_conj_symm_apply Matrix.lieConj_symm_apply

variable {m : Type w₁} [DecidableEq m] [Fintype m] (e : n ≃ m)

/-- For square matrices, the natural map that reindexes a matrix's rows and columns with equivalent
types, `Matrix.reindex`, is an equivalence of Lie algebras. -/
def Matrix.reindexLieEquiv : Matrix n n R ≃ₗ⁅R⁆ Matrix m m R :=
  { Matrix.reindexLinearEquiv R R e e with
    toFun := Matrix.reindex e e
    map_lie' := fun {_ _} => by
      simp only [LieRing.of_associative_ring_bracket, Matrix.reindex_apply,
        Matrix.submatrix_mul_equiv, Matrix.submatrix_sub, Pi.sub_apply] }
#align matrix.reindex_lie_equiv Matrix.reindexLieEquiv

@[simp]
theorem Matrix.reindexLieEquiv_apply (M : Matrix n n R) :
    Matrix.reindexLieEquiv e M = Matrix.reindex e e M :=
  rfl
#align matrix.reindex_lie_equiv_apply Matrix.reindexLieEquiv_apply

@[simp]
theorem Matrix.reindexLieEquiv_symm :
    (Matrix.reindexLieEquiv e : _ ≃ₗ⁅R⁆ _).symm = Matrix.reindexLieEquiv e.symm :=
  rfl
#align matrix.reindex_lie_equiv_symm Matrix.reindexLieEquiv_symm

end Matrices
