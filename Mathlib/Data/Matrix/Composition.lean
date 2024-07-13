/-
Copyright (c) 2024 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Yunzhou Xie
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Reindex
/-!
# Composition of matrices
## Main results

* `Matrix.comp` is an equivalence between `Matrix I J (Matrix K L R)` and
  `I × K` by `J × L` matrices.
* `Matrix.swap` is an equivalence between `(I × J)` by `(K × L)` matrices and
  `J × I` by `L × K` matrices.

This file shows that Mₙ(Mₘ(R)) ≃ Mₙₘ(R), Mₙ(Mₘ(R)) ≃ Mₘ(Mₙ(R)), Mn(Rᵒᵖ) ≃ₐ[K] Mₙ(R)ᵒᵖ
and also different levels of equivalence when R is an AddCommMonoid,
Semiring, and Algebra over a CommSemiring K.
-/

namespace Matrix

variable  (I J K L R : Type*)

/-- I by J matrix where each entry is a K by L matrix is equivalent to
    I × K by J × L matrix -/
@[simps]
def comp : Matrix I J (Matrix K L R) ≃ Matrix (I × K) (J × L) R where
  toFun m ik jl := m ik.1 jl.1 ik.2 jl.2
  invFun n i j k l := n (i, k) (j, l)
  left_inv _ := rfl
  right_inv _ := rfl

section AddCommMonoid

variable [AddCommMonoid R]

/-- `Matrix.comp` as `AddEquiv` -/
@[simps!]
def compAddEquiv : Matrix I J (Matrix K L R) ≃+ Matrix (I × K) (J × L) R where
  __ := Matrix.comp I J K L R
  map_add' _ _ := rfl

end AddCommMonoid

section Semiring

variable [Semiring R] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- `Matrix.comp` as `RingEquiv` -/
@[simps!]
def compRingEquiv : Matrix I I (Matrix J J R) ≃+* Matrix (I × J) (I × J) R where
  __ := Matrix.compAddEquiv I I J J R
  map_mul' _ _ := by
    ext _ _
    exact (Matrix.sum_apply _ _ _ _).trans $ Eq.symm Fintype.sum_prod_type

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
@[simps!]
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

open MulOpposite in
/-- n-by-n matrices over an opposite ring Rᵒᵖ is isomorphic to the opposite ring of
  n-by-n matrices over R -/
@[simps]
def transposeAlgEquiv':
    Matrix I I Rᵐᵒᵖ ≃ₐ[K] (Matrix I I R)ᵐᵒᵖ where
  toFun M := op (M.transpose.map (fun d => unop d))
  invFun M := (unop M).transpose.map (fun d => op d)
  left_inv a := by aesop
  right_inv a := by aesop
  map_mul' x y := unop_injective $ by ext; simp [transpose_map, transpose_apply, mul_apply]
  map_add' x y := by aesop
  commutes' k := by
    simp only [algebraMap_apply, op_inj]
    ext i j
    simp only [map_apply, transpose_apply, algebraMap_matrix_apply]
    aesop

end Algebra

end Matrix
