/-
Copyright (c) 2024 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Yunzhou Xie
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis

/-!
# Composition of matrices

This file shows that Mₙ(Mₘ(R)) ≃ Mₙₘ(R), Mₙ(Rᵒᵖ) ≃ₐ[K] Mₙ(R)ᵒᵖ
and also different levels of equivalence when R is an AddCommMonoid,
Semiring, and Algebra over a CommSemiring K.

## Main results

* `Matrix.comp` is an equivalence between `Matrix I J (Matrix K L R)` and
  `I × K` by `J × L` matrices.
* `Matrix.swap` is an equivalence between `(I × J)` by `(K × L)` matrices and
  `J × I` by `L × K` matrices.

-/

namespace Matrix

variable (I J K L R R' : Type*)

/-- I by J matrix where each entry is a K by L matrix is equivalent to
    I × K by J × L matrix -/
@[simps]
def comp : Matrix I J (Matrix K L R) ≃ Matrix (I × K) (J × L) R where
  toFun m ik jl := m ik.1 jl.1 ik.2 jl.2
  invFun n i j k l := n (i, k) (j, l)
  left_inv _ := rfl
  right_inv _ := rfl

theorem comp_map_map (M : Matrix I J (Matrix K L R)) (f : R → R') :
  comp I J K L _ (M.map (fun M' => M'.map f)) = (comp I J K L _ M).map f := rfl

variable {R I J K L} in
@[simp]
theorem comp_stdBasisMatrix_stdBasisMatrix
    [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L] [Zero R] (i j k l r) :
    comp I J K L R (stdBasisMatrix i j (stdBasisMatrix k l r))
      = stdBasisMatrix (i, k) (j, l) r := by
  ext ⟨i', k'⟩ ⟨j', l'⟩
  dsimp [comp_apply]
  obtain hi | rfl := ne_or_eq i i'
  · rw [StdBasisMatrix.apply_of_row_ne hi,
      StdBasisMatrix.apply_of_row_ne (ne_of_apply_ne Prod.fst hi), Matrix.zero_apply]
  obtain hj | rfl := ne_or_eq j j'
  · rw [StdBasisMatrix.apply_of_col_ne _ _ hj,
      StdBasisMatrix.apply_of_col_ne _ _ (ne_of_apply_ne Prod.fst hj), Matrix.zero_apply]
  rw [StdBasisMatrix.apply_same]
  obtain hk | rfl := ne_or_eq k k'
  · rw [StdBasisMatrix.apply_of_row_ne hk,
      StdBasisMatrix.apply_of_row_ne (ne_of_apply_ne Prod.snd hk)]
  obtain hj | rfl := ne_or_eq l l'
  · rw [StdBasisMatrix.apply_of_col_ne _ _ hj,
      StdBasisMatrix.apply_of_col_ne _ _ (ne_of_apply_ne Prod.snd hj)]
  rw [StdBasisMatrix.apply_same, StdBasisMatrix.apply_same]

variable {R I J K L} in
@[simp]
theorem comp_symm_stdBasisMatrix_stdBasisMatrix
    [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L] [Zero R] (ii jj r) :
    (comp I J K L R).symm (stdBasisMatrix ii jj r) =
      (stdBasisMatrix ii.1 jj.1 (stdBasisMatrix ii.2 jj.2 r)) :=
  (comp I J K L R).symm_apply_eq.2 <| comp_stdBasisMatrix_stdBasisMatrix _ _ _ _ _ |>.symm

variable {R I J K L} in
@[simp]
theorem comp_symm_stdBasisMatrix
    [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L] [Zero R] (i j k l r) :
    (comp I J K L R).symm (stdBasisMatrix (i, k) (j, l) r)
      = (stdBasisMatrix i j (stdBasisMatrix k l r)) :=
  (comp _ _ _ _ _).symm_apply_eq.2 <| (comp_stdBasisMatrix_stdBasisMatrix _ _ _ _ _).symm

section AddCommMonoid

variable [AddCommMonoid R]

/-- `Matrix.comp` as `AddEquiv` -/
def compAddEquiv : Matrix I J (Matrix K L R) ≃+ Matrix (I × K) (J × L) R where
  __ := Matrix.comp I J K L R
  map_add' _ _ := rfl

@[simp]
theorem compAddEquiv_apply (M : Matrix I J (Matrix K L R)) :
    compAddEquiv I J K L R M = comp I J K L R M := rfl

@[simp]
theorem compAddEquiv_symm_apply (M : Matrix (I × K) (J × L) R) :
    (compAddEquiv I J K L R).symm M = (comp I J K L R).symm M := rfl

end AddCommMonoid

section Semiring

variable [Semiring R] [Fintype I] [Fintype J]

/-- `Matrix.comp` as `RingEquiv` -/
def compRingEquiv : Matrix I I (Matrix J J R) ≃+* Matrix (I × J) (I × J) R where
  __ := Matrix.compAddEquiv I I J J R
  map_mul' _ _ := by ext; exact (Matrix.sum_apply ..).trans <| .symm <| Fintype.sum_prod_type ..

@[simp]
theorem compRingEquiv_apply (M : Matrix I I (Matrix J J R)) :
    compRingEquiv I J R M = comp I I J J R M := rfl

@[simp]
theorem compRingEquiv_symm_apply (M : Matrix (I × J) (I × J) R) :
    (compRingEquiv I J R).symm M = (comp I I J J R).symm M := rfl

end Semiring

section LinearMap

variable (K : Type*) [CommSemiring K] [AddCommMonoid R] [Module K R]

/-- `Matrix.comp` as `LinearEquiv` -/
@[simps!]
def compLinearEquiv : Matrix I J (Matrix K L R) ≃ₗ[K] Matrix (I × K) (J × L) R where
  __ := Matrix.compAddEquiv I J K L R
  map_smul' _ _ := rfl

end LinearMap

section Algebra

variable (K : Type*) [CommSemiring K] [Semiring R] [Fintype I] [Fintype J] [Algebra K R]

variable [DecidableEq I] [DecidableEq J]

/-- `Matrix.comp` as `AlgEquiv` -/
def compAlgEquiv : Matrix I I (Matrix J J R) ≃ₐ[K] Matrix (I × J) (I × J) R where
  __ := Matrix.compRingEquiv I J R
  commutes' c := by
    ext _ _
    simp only [compRingEquiv, compAddEquiv, comp, AddEquiv.toEquiv_eq_coe, RingEquiv.toEquiv_eq_coe,
      Equiv.toFun_as_coe, EquivLike.coe_coe, RingEquiv.coe_mk, AddEquiv.coe_mk, Equiv.coe_fn_mk,
      algebraMap_eq_diagonal]
    rw [Pi.algebraMap_def, Pi.algebraMap_def, Algebra.algebraMap_eq_smul_one',
      Algebra.algebraMap_eq_smul_one', ← diagonal_one, diagonal_apply, diagonal_apply]
    aesop

@[simp]
theorem compAlgEquiv_apply (M : Matrix I I (Matrix J J R)) :
    compAlgEquiv I J R K M = comp I I J J R M := rfl

@[simp]
theorem compAlgEquiv_symm_apply (M : Matrix (I × J) (I × J) R) :
    (compAlgEquiv I J R K).symm M = (comp I I J J R).symm M := rfl

end Algebra

end Matrix
