/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen

! This file was ported from Lean 3 source module linear_algebra.matrix.basis
! leanprover-community/mathlib commit 6c263e4bfc2e6714de30f22178b4d0ca4d149a76
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.Matrix.Reindex
import Mathbin.LinearAlgebra.Matrix.ToLin

/-!
# Bases and matrices

This file defines the map `basis.to_matrix` that sends a family of vectors to
the matrix of their coordinates with respect to some basis.

## Main definitions

 * `basis.to_matrix e v` is the matrix whose `i, j`th entry is `e.repr (v j) i`
 * `basis.to_matrix_equiv` is `basis.to_matrix` bundled as a linear equiv

## Main results

 * `linear_map.to_matrix_id_eq_basis_to_matrix`: `linear_map.to_matrix b c id`
   is equal to `basis.to_matrix b c`
 * `basis.to_matrix_mul_to_matrix`: multiplying `basis.to_matrix` with another
   `basis.to_matrix` gives a `basis.to_matrix`

## Tags

matrix, basis
-/


noncomputable section

open LinearMap Matrix Set Submodule

open BigOperators

open Matrix

section BasisToMatrix

variable {ι ι' κ κ' : Type _}

variable {R M : Type _} [CommSemiring R] [AddCommMonoid M] [Module R M]

variable {R₂ M₂ : Type _} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

open Function Matrix

/-- From a basis `e : ι → M` and a family of vectors `v : ι' → M`, make the matrix whose columns
are the vectors `v i` written in the basis `e`. -/
def Basis.toMatrix (e : Basis ι R M) (v : ι' → M) : Matrix ι ι' R := fun i j => e.repr (v j) i
#align basis.to_matrix Basis.toMatrix

variable (e : Basis ι R M) (v : ι' → M) (i : ι) (j : ι')

namespace Basis

theorem toMatrix_apply : e.toMatrix v i j = e.repr (v j) i :=
  rfl
#align basis.to_matrix_apply Basis.toMatrix_apply

theorem toMatrix_transpose_apply : (e.toMatrix v)ᵀ j = e.repr (v j) :=
  funext fun _ => rfl
#align basis.to_matrix_transpose_apply Basis.toMatrix_transpose_apply

theorem toMatrix_eq_toMatrix_constr [Fintype ι] [DecidableEq ι] (v : ι → M) :
    e.toMatrix v = LinearMap.toMatrix e e (e.constr ℕ v) :=
  by
  ext
  rw [Basis.toMatrix_apply, LinearMap.toMatrix_apply, Basis.constr_basis]
#align basis.to_matrix_eq_to_matrix_constr Basis.toMatrix_eq_toMatrix_constr

-- TODO (maybe) Adjust the definition of `basis.to_matrix` to eliminate the transpose.
theorem CoePiBasisFun.toMatrix_eq_transpose [Fintype ι] :
    ((Pi.basisFun R ι).toMatrix : Matrix ι ι R → Matrix ι ι R) = Matrix.transpose :=
  by
  ext (M i j)
  rfl
#align basis.coe_pi_basis_fun.to_matrix_eq_transpose Basis.CoePiBasisFun.toMatrix_eq_transpose

@[simp]
theorem toMatrix_self [DecidableEq ι] : e.toMatrix e = 1 :=
  by
  rw [Basis.toMatrix]
  ext (i j)
  simp [Basis.equivFun, Matrix.one_apply, Finsupp.single_apply, eq_comm]
#align basis.to_matrix_self Basis.toMatrix_self

theorem toMatrix_update [DecidableEq ι'] (x : M) :
    e.toMatrix (Function.update v j x) = Matrix.updateColumn (e.toMatrix v) j (e.repr x) :=
  by
  ext (i' k)
  rw [Basis.toMatrix, Matrix.updateColumn_apply, e.to_matrix_apply]
  split_ifs
  · rw [h, update_same j x v]
  · rw [update_noteq h]
#align basis.to_matrix_update Basis.toMatrix_update

/-- The basis constructed by `units_smul` has vectors given by a diagonal matrix. -/
@[simp]
theorem toMatrix_unitsSmul [DecidableEq ι] (e : Basis ι R₂ M₂) (w : ι → R₂ˣ) :
    e.toMatrix (e.units_smul w) = diagonal (coe ∘ w) :=
  by
  ext (i j)
  by_cases h : i = j
  · simp [h, to_matrix_apply, units_smul_apply, Units.smul_def]
  · simp [h, to_matrix_apply, units_smul_apply, Units.smul_def, Ne.symm h]
#align basis.to_matrix_units_smul Basis.toMatrix_unitsSmul

/-- The basis constructed by `is_unit_smul` has vectors given by a diagonal matrix. -/
@[simp]
theorem toMatrix_isUnitSmul [DecidableEq ι] (e : Basis ι R₂ M₂) {w : ι → R₂}
    (hw : ∀ i, IsUnit (w i)) : e.toMatrix (e.isUnitSmul hw) = diagonal w :=
  e.toMatrix_unitsSmul _
#align basis.to_matrix_is_unit_smul Basis.toMatrix_isUnitSmul

@[simp]
theorem sum_toMatrix_smul_self [Fintype ι] : (∑ i : ι, e.toMatrix v i j • e i) = v j := by
  simp_rw [e.to_matrix_apply, e.sum_repr]
#align basis.sum_to_matrix_smul_self Basis.sum_toMatrix_smul_self

theorem toMatrix_map_vecMul {S : Type _} [Ring S] [Algebra R S] [Fintype ι] (b : Basis ι R S)
    (v : ι' → S) : ((b.toMatrix v).map <| algebraMap R S).vecMul b = v :=
  by
  ext i
  simp_rw [vec_mul, dot_product, Matrix.map_apply, ← Algebra.commutes, ← Algebra.smul_def,
    sum_to_matrix_smul_self]
#align basis.to_matrix_map_vec_mul Basis.toMatrix_map_vecMul

@[simp]
theorem toLin_toMatrix [Fintype ι] [Fintype ι'] [DecidableEq ι'] (v : Basis ι' R M) :
    Matrix.toLin v e (e.toMatrix v) = id :=
  v.ext fun i => by rw [to_lin_self, id_apply, e.sum_to_matrix_smul_self]
#align basis.to_lin_to_matrix Basis.toLin_toMatrix

/-- From a basis `e : ι → M`, build a linear equivalence between families of vectors `v : ι → M`,
and matrices, making the matrix whose columns are the vectors `v i` written in the basis `e`. -/
def toMatrixEquiv [Fintype ι] (e : Basis ι R M) : (ι → M) ≃ₗ[R] Matrix ι ι R
    where
  toFun := e.toMatrix
  map_add' v w := by
    ext (i j)
    change _ = _ + _
    rw [e.to_matrix_apply, Pi.add_apply, LinearEquiv.map_add]
    rfl
  map_smul' := by
    intro c v
    ext (i j)
    rw [e.to_matrix_apply, Pi.smul_apply, LinearEquiv.map_smul]
    rfl
  invFun m j := ∑ i, m i j • e i
  left_inv := by
    intro v
    ext j
    exact e.sum_to_matrix_smul_self v j
  right_inv := by
    intro m
    ext (k l)
    simp only [e.to_matrix_apply, ← e.equiv_fun_apply, ← e.equiv_fun_symm_apply,
      LinearEquiv.apply_symm_apply]
#align basis.to_matrix_equiv Basis.toMatrixEquiv

end Basis

section MulLinearMapToMatrix

variable {N : Type _} [AddCommMonoid N] [Module R N]

variable (b : Basis ι R M) (b' : Basis ι' R M) (c : Basis κ R N) (c' : Basis κ' R N)

variable (f : M →ₗ[R] N)

open LinearMap

section Fintype

variable [Fintype ι'] [Fintype κ] [Fintype κ']

@[simp]
theorem basis_toMatrix_mul_linearMap_toMatrix [DecidableEq ι'] :
    c.toMatrix c' ⬝ LinearMap.toMatrix b' c' f = LinearMap.toMatrix b' c f :=
  (Matrix.toLin b' c).Injective
    (by
      haveI := Classical.decEq κ' <;>
        rw [to_lin_to_matrix, to_lin_mul b' c' c, to_lin_to_matrix, c.to_lin_to_matrix, id_comp])
#align basis_to_matrix_mul_linear_map_to_matrix basis_toMatrix_mul_linearMap_toMatrix

variable [Fintype ι]

@[simp]
theorem linearMap_toMatrix_mul_basis_toMatrix [DecidableEq ι] [DecidableEq ι'] :
    LinearMap.toMatrix b' c' f ⬝ b'.toMatrix b = LinearMap.toMatrix b c' f :=
  (Matrix.toLin b c').Injective
    (by rw [to_lin_to_matrix, to_lin_mul b b' c', to_lin_to_matrix, b'.to_lin_to_matrix, comp_id])
#align linear_map_to_matrix_mul_basis_to_matrix linearMap_toMatrix_mul_basis_toMatrix

theorem basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix [DecidableEq ι] [DecidableEq ι'] :
    c.toMatrix c' ⬝ LinearMap.toMatrix b' c' f ⬝ b'.toMatrix b = LinearMap.toMatrix b c f := by
  rw [basis_toMatrix_mul_linearMap_toMatrix, linearMap_toMatrix_mul_basis_toMatrix]
#align basis_to_matrix_mul_linear_map_to_matrix_mul_basis_to_matrix basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix

theorem basis_toMatrix_mul [DecidableEq κ] (b₁ : Basis ι R M) (b₂ : Basis ι' R M) (b₃ : Basis κ R N)
    (A : Matrix ι' κ R) : b₁.toMatrix b₂ ⬝ A = LinearMap.toMatrix b₃ b₁ (toLin b₃ b₂ A) :=
  by
  have := basis_toMatrix_mul_linearMap_toMatrix b₃ b₁ b₂ (Matrix.toLin b₃ b₂ A)
  rwa [LinearMap.toMatrix_toLin] at this
#align basis_to_matrix_mul basis_toMatrix_mul

theorem mul_basis_toMatrix [DecidableEq ι] [DecidableEq ι'] (b₁ : Basis ι R M) (b₂ : Basis ι' R M)
    (b₃ : Basis κ R N) (A : Matrix κ ι R) :
    A ⬝ b₁.toMatrix b₂ = LinearMap.toMatrix b₂ b₃ (toLin b₁ b₃ A) :=
  by
  have := linearMap_toMatrix_mul_basis_toMatrix b₂ b₁ b₃ (Matrix.toLin b₁ b₃ A)
  rwa [LinearMap.toMatrix_toLin] at this
#align mul_basis_to_matrix mul_basis_toMatrix

theorem basis_toMatrix_basisFun_mul (b : Basis ι R (ι → R)) (A : Matrix ι ι R) :
    b.toMatrix (Pi.basisFun R ι) ⬝ A = of fun i j => b.repr (Aᵀ j) i := by
  classical
    simp only [basis_toMatrix_mul _ _ (Pi.basisFun R ι), Matrix.toLin_eq_toLin']
    ext (i j)
    rw [LinearMap.toMatrix_apply, Matrix.toLin'_apply, Pi.basisFun_apply,
      Matrix.mulVec_stdBasis_apply, Matrix.of_apply]
#align basis_to_matrix_basis_fun_mul basis_toMatrix_basisFun_mul

/-- A generalization of `linear_map.to_matrix_id`. -/
@[simp]
theorem LinearMap.toMatrix_id_eq_basis_toMatrix [DecidableEq ι] :
    LinearMap.toMatrix b b' id = b'.toMatrix b :=
  by
  haveI := Classical.decEq ι'
  rw [← @basis_toMatrix_mul_linearMap_toMatrix _ _ ι, to_matrix_id, Matrix.mul_one]
#align linear_map.to_matrix_id_eq_basis_to_matrix LinearMap.toMatrix_id_eq_basis_toMatrix

/-- See also `basis.to_matrix_reindex` which gives the `simp` normal form of this result. -/
theorem Basis.toMatrix_reindex' [DecidableEq ι] [DecidableEq ι'] (b : Basis ι R M) (v : ι' → M)
    (e : ι ≃ ι') : (b.reindex e).toMatrix v = Matrix.reindexAlgEquiv _ e (b.toMatrix (v ∘ e)) :=
  by
  ext
  simp only [Basis.toMatrix_apply, Basis.repr_reindex, Matrix.reindexAlgEquiv_apply,
    Matrix.reindex_apply, Matrix.submatrix_apply, Function.comp_apply, e.apply_symm_apply,
    Finsupp.mapDomain_equiv_apply]
#align basis.to_matrix_reindex' Basis.toMatrix_reindex'

end Fintype

/-- A generalization of `basis.to_matrix_self`, in the opposite direction. -/
@[simp]
theorem Basis.toMatrix_mul_toMatrix {ι'' : Type _} [Fintype ι'] (b'' : ι'' → M) :
    b.toMatrix b' ⬝ b'.toMatrix b'' = b.toMatrix b'' :=
  by
  have := Classical.decEq ι
  have := Classical.decEq ι'
  haveI := Classical.decEq ι''
  ext (i j)
  simp only [Matrix.mul_apply, Basis.toMatrix_apply, Basis.sum_repr_mul_repr]
#align basis.to_matrix_mul_to_matrix Basis.toMatrix_mul_toMatrix

/-- `b.to_matrix b'` and `b'.to_matrix b` are inverses. -/
theorem Basis.toMatrix_mul_toMatrix_flip [DecidableEq ι] [Fintype ι'] :
    b.toMatrix b' ⬝ b'.toMatrix b = 1 := by rw [Basis.toMatrix_mul_toMatrix, Basis.toMatrix_self]
#align basis.to_matrix_mul_to_matrix_flip Basis.toMatrix_mul_toMatrix_flip

/-- A matrix whose columns form a basis `b'`, expressed w.r.t. a basis `b`, is invertible. -/
def Basis.invertibleToMatrix [DecidableEq ι] [Fintype ι] (b b' : Basis ι R₂ M₂) :
    Invertible (b.toMatrix b') :=
  ⟨b'.toMatrix b, Basis.toMatrix_mul_toMatrix_flip _ _, Basis.toMatrix_mul_toMatrix_flip _ _⟩
#align basis.invertible_to_matrix Basis.invertibleToMatrix

@[simp]
theorem Basis.toMatrix_reindex (b : Basis ι R M) (v : ι' → M) (e : ι ≃ ι') :
    (b.reindex e).toMatrix v = (b.toMatrix v).submatrix e.symm id :=
  by
  ext
  simp only [Basis.toMatrix_apply, Basis.repr_reindex, Matrix.submatrix_apply, id.def,
    Finsupp.mapDomain_equiv_apply]
#align basis.to_matrix_reindex Basis.toMatrix_reindex

@[simp]
theorem Basis.toMatrix_map (b : Basis ι R M) (f : M ≃ₗ[R] N) (v : ι → N) :
    (b.map f).toMatrix v = b.toMatrix (f.symm ∘ v) :=
  by
  ext
  simp only [Basis.toMatrix_apply, Basis.map, LinearEquiv.trans_apply]
#align basis.to_matrix_map Basis.toMatrix_map

end MulLinearMapToMatrix

end BasisToMatrix

