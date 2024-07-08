/-
Copyright (c) 2024 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Yunzhou Xie
-/

import Mathlib.Data.Matrix.Basic

/-!
## Main results
# Composition of matrices
This file shows that Mₙ(Mₘ(R)) ≃ Mₙₘ(R), Mₙ(Mₘ(R)) ≃ Mₘ(Mₙ(R)), Mn(Rᵒᵖ) ≃ₐ[K] Mₙ(R)ᵒᵖ
and also different levels of equivalence when R is an AddCommMonoid,
Semiring, and Algebra over a CommSemiring K.
-/

namespace Matrix

variable  (I J K L R : Type*)

/-- Mₙ(Mₘ(R)) ≃ Mₙₘ(R) -/
@[simps]
def comp : Matrix I J (Matrix K L R) ≃ Matrix (I × K) (J × L) R where
  toFun m ik jl := m ik.1 jl.1 ik.2 jl.2
  invFun n i j k l := n (i, k) (j, l)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Mₙ(Mₘ(R)) ≃ Mₘ(Mₙ(R)) -/
@[simps]
def swap : Matrix (I × J) (K × L) R ≃ Matrix (J × I) (L × K) R where
  toFun m ji kl := m (ji.2, ji.1) (kl.2, kl.1)
  invFun n ij kl := n (ij.2, ij.1) (kl.2, kl.1)
  left_inv _ := rfl
  right_inv _ := rfl

section AddCommMonoid

variable [AddCommMonoid R]

/-- Mₙ(Mₘ(R)) ≃+ Mₙₘ(R) -/
@[simps!]
def compAddEquiv : Matrix I J (Matrix K L R) ≃+ Matrix (I × K) (J × L) R :=
{
  Matrix.comp I J K L R with
  map_add' := fun _ _ ↦ rfl
}

/-- Mₙ(Mₘ(R)) ≃+ Mₘ(Mₙ(R)) -/
@[simps!]
def swapAddEquiv : Matrix (I × J) (K × L) R ≃+ Matrix (J × I) (L × K) R :=
{
  Matrix.swap I J K L R with
  map_add' := fun _ _ ↦ rfl
}

end AddCommMonoid

section Semiring

variable [Semiring R] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- Mₙ(Mₘ(R)) ≃+* Mₙₘ(R) -/
@[simps!]
def compRingEquiv : Matrix I I (Matrix J J R) ≃+* Matrix (I × J) (I × J) R :=
{
  Matrix.compAddEquiv I I J J R with
  map_mul' := fun _ _ ↦ by
    ext _ _
    refine (Matrix.sum_apply _ _ _ _).trans $ Eq.symm Fintype.sum_prod_type
}

/-- Mₙ(Mₘ(R)) ≃+* Mₘ(Mₙ(R)) -/
@[simps!]
def swapRingEquiv : Matrix (I × J) (I × J) R ≃+* Matrix (J × I) (J × I) R :=
{
  Matrix.swapAddEquiv I J I J R with
  map_mul' := fun _ _ ↦ by
    ext _ _
    simp only [swapAddEquiv, swap, AddEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe,
      AddEquiv.coe_mk, Equiv.coe_fn_mk, mul_apply, Fintype.sum_prod_type]
    exact Finset.sum_comm
}

end Semiring

section LinearMap

variable (K : Type*) [CommSemiring K] [AddCommMonoid R] [Module K R]

/-- Mₙ(Mₘ(R)) ≃ₗ[K] Mₙₘ(R) -/
@[simps!]
def compLinearEquiv : Matrix I J (Matrix K L R) ≃ₗ[K] Matrix (I × K) (J × L) R :=
{
  Matrix.compAddEquiv I J K L R with
  map_smul' := fun _ _ ↦ rfl
}

/-- Mₙ(Mₘ(R)) ≃ₗ[K] Mₘ(Mₙ(R)) -/
@[simps!]
def swapLinearEquiv : Matrix (I × J) (K × L) R ≃ₗ[K] Matrix (J × I) (L × K) R :=
{
  Matrix.swapAddEquiv I J K L R with
  map_smul' := fun _ _ ↦ rfl
}

end LinearMap

section Algebra

variable (K : Type*) [CommSemiring K] [Semiring R] [Fintype I] [Fintype J] [Algebra K R]

variable [DecidableEq I] [DecidableEq J]

/-- Mₙ(Mₘ(R)) ≃ₐ[K] Mₙₘ(R) -/
@[simps!]
def compAlgEquiv : Matrix I I (Matrix J J R) ≃ₐ[K] Matrix (I × J) (I × J) R :=
{
  Matrix.compRingEquiv I J R with
  commutes' := fun c ↦ by
    ext ⟨i1, j1⟩ ⟨i2, j2⟩
    simp only [compRingEquiv, compAddEquiv, comp, AddEquiv.toEquiv_eq_coe, RingEquiv.toEquiv_eq_coe,
      Equiv.toFun_as_coe, EquivLike.coe_coe, RingEquiv.coe_mk, AddEquiv.coe_mk, Equiv.coe_fn_mk,
      algebraMap_eq_diagonal]
    rw [Pi.algebraMap_def, Pi.algebraMap_def, Algebra.algebraMap_eq_smul_one',
      Algebra.algebraMap_eq_smul_one', ← diagonal_one, diagonal_apply, diagonal_apply]
    aesop
}

/-- Mₙ(Mₘ(R)) ≃ₐ[K] Mₘ(Mₙ(R)) -/
@[simps!]
def swapAlgEquiv : Matrix (I × J) (I × J) R ≃ₐ[K] Matrix (J × I) (J × I) R :=
{
  Matrix.swapRingEquiv I J R with
  commutes' := fun c ↦ by
    ext ⟨i1, j1⟩ ⟨i2, j2⟩
    simp only [swapRingEquiv, swapAddEquiv, swap, AddEquiv.toEquiv_eq_coe, RingEquiv.toEquiv_eq_coe,
      Equiv.toFun_as_coe, EquivLike.coe_coe, RingEquiv.coe_mk, AddEquiv.coe_mk, Equiv.coe_fn_mk,
      algebraMap_eq_diagonal]
    rw [Pi.algebraMap_def, Pi.algebraMap_def, Algebra.algebraMap_eq_smul_one',
      diagonal_apply, diagonal_apply]
    aesop
}

open MulOpposite in
/-- n-by-n matrices over an opposite ring Rᵒᵖ is isomorphic to the opposite ring of
  n-by-n matrices over R -/
@[simps]
def matrixEquivMatrixMopAlgebra:
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
