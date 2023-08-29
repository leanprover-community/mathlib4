/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.ToLin

#align_import linear_algebra.matrix.basis from "leanprover-community/mathlib"@"6c263e4bfc2e6714de30f22178b4d0ca4d149a76"

/-!
# Bases and matrices

This file defines the map `Basis.toMatrix` that sends a family of vectors to
the matrix of their coordinates with respect to some basis.

## Main definitions

 * `Basis.toMatrix e v` is the matrix whose `i, j`th entry is `e.repr (v j) i`
 * `basis.toMatrixEquiv` is `Basis.toMatrix` bundled as a linear equiv

## Main results

 * `LinearMap.toMatrix_id_eq_basis_toMatrix`: `LinearMap.toMatrix b c id`
   is equal to `Basis.toMatrix b c`
 * `Basis.toMatrix_mul_toMatrix`: multiplying `Basis.toMatrix` with another
   `Basis.toMatrix` gives a `Basis.toMatrix`

## Tags

matrix, basis
-/


noncomputable section

open LinearMap Matrix Set Submodule

open BigOperators

open Matrix

section BasisToMatrix

variable {ι ι' κ κ' : Type*}

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

variable {R₂ M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

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
    e.toMatrix v = LinearMap.toMatrix e e (e.constr ℕ v) := by
  ext
  -- ⊢ toMatrix e v i✝ x✝ = ↑(LinearMap.toMatrix e e) (↑(constr e ℕ) v) i✝ x✝
  rw [Basis.toMatrix_apply, LinearMap.toMatrix_apply, Basis.constr_basis]
  -- 🎉 no goals
#align basis.to_matrix_eq_to_matrix_constr Basis.toMatrix_eq_toMatrix_constr

-- TODO (maybe) Adjust the definition of `Basis.toMatrix` to eliminate the transpose.
theorem coePiBasisFun.toMatrix_eq_transpose [Fintype ι] :
    ((Pi.basisFun R ι).toMatrix : Matrix ι ι R → Matrix ι ι R) = Matrix.transpose := by
  ext M i j
  -- ⊢ toMatrix (Pi.basisFun R ι) M i j = Mᵀ i j
  rfl
  -- 🎉 no goals
#align basis.coe_pi_basis_fun.to_matrix_eq_transpose Basis.coePiBasisFun.toMatrix_eq_transpose

@[simp]
theorem toMatrix_self [DecidableEq ι] : e.toMatrix e = 1 := by
  unfold Basis.toMatrix
  -- ⊢ (fun i j => ↑(↑e.repr (↑e j)) i) = 1
  ext i j
  -- ⊢ ↑(↑e.repr (↑e j)) i = OfNat.ofNat 1 i j
  simp [Basis.equivFun, Matrix.one_apply, Finsupp.single_apply, eq_comm]
  -- 🎉 no goals
#align basis.to_matrix_self Basis.toMatrix_self

theorem toMatrix_update [DecidableEq ι'] (x : M) :
    e.toMatrix (Function.update v j x) = Matrix.updateColumn (e.toMatrix v) j (e.repr x) := by
  ext i' k
  -- ⊢ toMatrix e (update v j x) i' k = updateColumn (toMatrix e v) j (↑(↑e.repr x) …
  rw [Basis.toMatrix, Matrix.updateColumn_apply, e.toMatrix_apply]
  -- ⊢ ↑(↑e.repr (update v j x k)) i' = if k = j then ↑(↑e.repr x) i' else ↑(↑e.rep …
  split_ifs with h
  -- ⊢ ↑(↑e.repr (update v j x k)) i' = ↑(↑e.repr x) i'
  · rw [h, update_same j x v]
    -- 🎉 no goals
  · rw [update_noteq h]
    -- 🎉 no goals
#align basis.to_matrix_update Basis.toMatrix_update

/-- The basis constructed by `unitsSMul` has vectors given by a diagonal matrix. -/
@[simp]
theorem toMatrix_unitsSMul [DecidableEq ι] (e : Basis ι R₂ M₂) (w : ι → R₂ˣ) :
    e.toMatrix (e.unitsSMul w) = diagonal ((↑) ∘ w) := by
  ext i j
  -- ⊢ toMatrix e (↑(unitsSMul e w)) i j = Matrix.diagonal (Units.val ∘ w) i j
  by_cases h : i = j
  -- ⊢ toMatrix e (↑(unitsSMul e w)) i j = Matrix.diagonal (Units.val ∘ w) i j
  · simp [h, toMatrix_apply, unitsSMul_apply, Units.smul_def]
    -- 🎉 no goals
  · simp [h, toMatrix_apply, unitsSMul_apply, Units.smul_def, Ne.symm h]
    -- 🎉 no goals
#align basis.to_matrix_units_smul Basis.toMatrix_unitsSMul

/-- The basis constructed by `isUnitSMul` has vectors given by a diagonal matrix. -/
@[simp]
theorem toMatrix_isUnitSMul [DecidableEq ι] (e : Basis ι R₂ M₂) {w : ι → R₂}
    (hw : ∀ i, IsUnit (w i)) : e.toMatrix (e.isUnitSMul hw) = diagonal w :=
  e.toMatrix_unitsSMul _
#align basis.to_matrix_is_unit_smul Basis.toMatrix_isUnitSMul

@[simp]
theorem sum_toMatrix_smul_self [Fintype ι] : ∑ i : ι, e.toMatrix v i j • e i = v j := by
  simp_rw [e.toMatrix_apply, e.sum_repr]
  -- 🎉 no goals
#align basis.sum_to_matrix_smul_self Basis.sum_toMatrix_smul_self

theorem toMatrix_map_vecMul {S : Type*} [Ring S] [Algebra R S] [Fintype ι] (b : Basis ι R S)
    (v : ι' → S) : ((b.toMatrix v).map <| algebraMap R S).vecMul b = v := by
  ext i
  -- ⊢ vecMul (↑b) (Matrix.map (toMatrix b v) ↑(algebraMap R S)) i = v i
  simp_rw [vecMul, dotProduct, Matrix.map_apply, ← Algebra.commutes, ← Algebra.smul_def,
    sum_toMatrix_smul_self]
#align basis.to_matrix_map_vec_mul Basis.toMatrix_map_vecMul

@[simp]
theorem toLin_toMatrix [Fintype ι] [Fintype ι'] [DecidableEq ι'] (v : Basis ι' R M) :
    Matrix.toLin v e (e.toMatrix v) = LinearMap.id :=
  v.ext fun i => by rw [toLin_self, id_apply, e.sum_toMatrix_smul_self]
                    -- 🎉 no goals
#align basis.to_lin_to_matrix Basis.toLin_toMatrix

/-- From a basis `e : ι → M`, build a linear equivalence between families of vectors `v : ι → M`,
and matrices, making the matrix whose columns are the vectors `v i` written in the basis `e`. -/
def toMatrixEquiv [Fintype ι] (e : Basis ι R M) : (ι → M) ≃ₗ[R] Matrix ι ι R where
  toFun := e.toMatrix
  map_add' v w := by
    ext i j
    -- ⊢ toMatrix e (v + w) i j = (toMatrix e v + toMatrix e w) i j
    change _ = _ + _
    -- ⊢ toMatrix e (v + w) i j = toMatrix e v i j + toMatrix e w i j
    rw [e.toMatrix_apply, Pi.add_apply, LinearEquiv.map_add]
    -- ⊢ ↑(↑e.repr (v j) + ↑e.repr (w j)) i = toMatrix e v i j + toMatrix e w i j
    rfl
    -- 🎉 no goals
  map_smul' := by
    intro c v
    -- ⊢ AddHom.toFun { toFun := toMatrix e, map_add' := (_ : ∀ (v w : ι → M), toMatr …
    ext i j
    -- ⊢ AddHom.toFun { toFun := toMatrix e, map_add' := (_ : ∀ (v w : ι → M), toMatr …
    dsimp only []
    -- ⊢ toMatrix e (c • v) i j = (↑(RingHom.id R) c • toMatrix e v) i j
    rw [e.toMatrix_apply, Pi.smul_apply, LinearEquiv.map_smul]
    -- ⊢ ↑(c • ↑e.repr (v j)) i = (↑(RingHom.id R) c • toMatrix e v) i j
    rfl
    -- 🎉 no goals
  invFun m j := ∑ i, m i j • e i
  left_inv := by
    intro v
    -- ⊢ (fun m j => ∑ i : ι, m i j • ↑e i) (AddHom.toFun { toAddHom := { toFun := to …
    ext j
    -- ⊢ (fun m j => ∑ i : ι, m i j • ↑e i) (AddHom.toFun { toAddHom := { toFun := to …
    exact e.sum_toMatrix_smul_self v j
    -- 🎉 no goals
  right_inv := by
    intro m
    -- ⊢ AddHom.toFun { toAddHom := { toFun := toMatrix e, map_add' := (_ : ∀ (v w :  …
    ext k l
    -- ⊢ AddHom.toFun { toAddHom := { toFun := toMatrix e, map_add' := (_ : ∀ (v w :  …
    simp only [e.toMatrix_apply, ← e.equivFun_apply, ← e.equivFun_symm_apply,
      LinearEquiv.apply_symm_apply]
#align basis.to_matrix_equiv Basis.toMatrixEquiv

end Basis

section MulLinearMapToMatrix

variable {N : Type*} [AddCommMonoid N] [Module R N]

variable (b : Basis ι R M) (b' : Basis ι' R M) (c : Basis κ R N) (c' : Basis κ' R N)

variable (f : M →ₗ[R] N)

open LinearMap

section Fintype

variable [Fintype ι'] [Fintype κ] [Fintype κ']

@[simp]
theorem basis_toMatrix_mul_linearMap_toMatrix [DecidableEq ι'] :
    c.toMatrix c' * LinearMap.toMatrix b' c' f = LinearMap.toMatrix b' c f :=
  (Matrix.toLin b' c).injective
    (by
      haveI := Classical.decEq κ'
      -- ⊢ ↑(toLin b' c) (Basis.toMatrix c ↑c' * ↑(toMatrix b' c') f) = ↑(toLin b' c) ( …
      rw [toLin_toMatrix, toLin_mul b' c' c, toLin_toMatrix, c.toLin_toMatrix, id_comp])
      -- 🎉 no goals
#align basis_to_matrix_mul_linear_map_to_matrix basis_toMatrix_mul_linearMap_toMatrix

variable [Fintype ι]

@[simp]
theorem linearMap_toMatrix_mul_basis_toMatrix [DecidableEq ι] [DecidableEq ι'] :
    LinearMap.toMatrix b' c' f * b'.toMatrix b = LinearMap.toMatrix b c' f :=
  (Matrix.toLin b c').injective
    (by rw [toLin_toMatrix, toLin_mul b b' c', toLin_toMatrix, b'.toLin_toMatrix, comp_id])
        -- 🎉 no goals
#align linear_map_to_matrix_mul_basis_to_matrix linearMap_toMatrix_mul_basis_toMatrix

theorem basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix [DecidableEq ι] [DecidableEq ι'] :
    c.toMatrix c' * LinearMap.toMatrix b' c' f * b'.toMatrix b = LinearMap.toMatrix b c f := by
  rw [basis_toMatrix_mul_linearMap_toMatrix, linearMap_toMatrix_mul_basis_toMatrix]
  -- 🎉 no goals
#align basis_to_matrix_mul_linear_map_to_matrix_mul_basis_to_matrix basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix

theorem basis_toMatrix_mul [DecidableEq κ] (b₁ : Basis ι R M) (b₂ : Basis ι' R M) (b₃ : Basis κ R N)
    (A : Matrix ι' κ R) : b₁.toMatrix b₂ * A = LinearMap.toMatrix b₃ b₁ (toLin b₃ b₂ A) := by
  have := basis_toMatrix_mul_linearMap_toMatrix b₃ b₁ b₂ (Matrix.toLin b₃ b₂ A)
  -- ⊢ Basis.toMatrix b₁ ↑b₂ * A = ↑(toMatrix b₃ b₁) (↑(toLin b₃ b₂) A)
  rwa [LinearMap.toMatrix_toLin] at this
  -- 🎉 no goals
#align basis_to_matrix_mul basis_toMatrix_mul

theorem mul_basis_toMatrix [DecidableEq ι] [DecidableEq ι'] (b₁ : Basis ι R M) (b₂ : Basis ι' R M)
    (b₃ : Basis κ R N) (A : Matrix κ ι R) :
    A * b₁.toMatrix b₂ = LinearMap.toMatrix b₂ b₃ (toLin b₁ b₃ A) := by
  have := linearMap_toMatrix_mul_basis_toMatrix b₂ b₁ b₃ (Matrix.toLin b₁ b₃ A)
  -- ⊢ A * Basis.toMatrix b₁ ↑b₂ = ↑(toMatrix b₂ b₃) (↑(toLin b₁ b₃) A)
  rwa [LinearMap.toMatrix_toLin] at this
  -- 🎉 no goals
#align mul_basis_to_matrix mul_basis_toMatrix

theorem basis_toMatrix_basisFun_mul (b : Basis ι R (ι → R)) (A : Matrix ι ι R) :
    b.toMatrix (Pi.basisFun R ι) * A = of fun i j => b.repr (Aᵀ j) i := by
  classical
    simp only [basis_toMatrix_mul _ _ (Pi.basisFun R ι), Matrix.toLin_eq_toLin']
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.toLin'_apply, Pi.basisFun_apply,
      Matrix.mulVec_stdBasis_apply, Matrix.of_apply]
#align basis_to_matrix_basis_fun_mul basis_toMatrix_basisFun_mul

/-- A generalization of `LinearMap.toMatrix_id`. -/
@[simp]
theorem LinearMap.toMatrix_id_eq_basis_toMatrix [DecidableEq ι] :
    LinearMap.toMatrix b b' id = b'.toMatrix b := by
  haveI := Classical.decEq ι'
  -- ⊢ ↑(toMatrix b b') id = Basis.toMatrix b' ↑b
  rw [← @basis_toMatrix_mul_linearMap_toMatrix _ _ ι, toMatrix_id, Matrix.mul_one]
  -- 🎉 no goals
#align linear_map.to_matrix_id_eq_basis_to_matrix LinearMap.toMatrix_id_eq_basis_toMatrix

/-- See also `Basis.toMatrix_reindex` which gives the `simp` normal form of this result. -/
theorem Basis.toMatrix_reindex' [DecidableEq ι] [DecidableEq ι'] (b : Basis ι R M) (v : ι' → M)
    (e : ι ≃ ι') : (b.reindex e).toMatrix v = Matrix.reindexAlgEquiv _ e (b.toMatrix (v ∘ e)) := by
  ext
  -- ⊢ toMatrix (reindex b e) v i✝ x✝ = ↑(reindexAlgEquiv R e) (toMatrix b (v ∘ ↑e) …
  simp only [Basis.toMatrix_apply, Basis.repr_reindex, Matrix.reindexAlgEquiv_apply,
    Matrix.reindex_apply, Matrix.submatrix_apply, Function.comp_apply, e.apply_symm_apply,
    Finsupp.mapDomain_equiv_apply]
#align basis.to_matrix_reindex' Basis.toMatrix_reindex'

end Fintype

/-- A generalization of `Basis.toMatrix_self`, in the opposite direction. -/
@[simp]
theorem Basis.toMatrix_mul_toMatrix {ι'' : Type*} [Fintype ι'] (b'' : ι'' → M) :
    b.toMatrix b' * b'.toMatrix b'' = b.toMatrix b'' := by
  haveI := Classical.decEq ι
  -- ⊢ toMatrix b ↑b' * toMatrix b' b'' = toMatrix b b''
  haveI := Classical.decEq ι'
  -- ⊢ toMatrix b ↑b' * toMatrix b' b'' = toMatrix b b''
  haveI := Classical.decEq ι''
  -- ⊢ toMatrix b ↑b' * toMatrix b' b'' = toMatrix b b''
  ext i j
  -- ⊢ (toMatrix b ↑b' * toMatrix b' b'') i j = toMatrix b b'' i j
  simp only [Matrix.mul_apply, Basis.toMatrix_apply, Basis.sum_repr_mul_repr]
  -- 🎉 no goals
#align basis.to_matrix_mul_to_matrix Basis.toMatrix_mul_toMatrix

/-- `b.toMatrix b'` and `b'.toMatrix b` are inverses. -/
theorem Basis.toMatrix_mul_toMatrix_flip [DecidableEq ι] [Fintype ι'] :
    b.toMatrix b' * b'.toMatrix b = 1 := by rw [Basis.toMatrix_mul_toMatrix, Basis.toMatrix_self]
                                            -- 🎉 no goals
#align basis.to_matrix_mul_to_matrix_flip Basis.toMatrix_mul_toMatrix_flip

/-- A matrix whose columns form a basis `b'`, expressed w.r.t. a basis `b`, is invertible. -/
def Basis.invertibleToMatrix [DecidableEq ι] [Fintype ι] (b b' : Basis ι R₂ M₂) :
    Invertible (b.toMatrix b') :=
  ⟨b'.toMatrix b, Basis.toMatrix_mul_toMatrix_flip _ _, Basis.toMatrix_mul_toMatrix_flip _ _⟩
#align basis.invertible_to_matrix Basis.invertibleToMatrix

@[simp]
theorem Basis.toMatrix_reindex (b : Basis ι R M) (v : ι' → M) (e : ι ≃ ι') :
    (b.reindex e).toMatrix v = (b.toMatrix v).submatrix e.symm _root_.id := by
  ext
  -- ⊢ toMatrix (reindex b e) v i✝ x✝ = submatrix (toMatrix b v) (↑e.symm) _root_.i …
  simp only [Basis.toMatrix_apply, Basis.repr_reindex, Matrix.submatrix_apply, id.def,
    Finsupp.mapDomain_equiv_apply]
#align basis.to_matrix_reindex Basis.toMatrix_reindex

@[simp]
theorem Basis.toMatrix_map (b : Basis ι R M) (f : M ≃ₗ[R] N) (v : ι → N) :
    (b.map f).toMatrix v = b.toMatrix (f.symm ∘ v) := by
  ext
  -- ⊢ toMatrix (Basis.map b f) v i✝ x✝ = toMatrix b (↑(LinearEquiv.symm f) ∘ v) i✝ …
  simp only [Basis.toMatrix_apply, Basis.map, LinearEquiv.trans_apply, (· ∘ ·)]
  -- 🎉 no goals
#align basis.to_matrix_map Basis.toMatrix_map

end MulLinearMapToMatrix

end BasisToMatrix
