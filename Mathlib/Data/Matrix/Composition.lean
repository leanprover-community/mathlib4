/-
Copyright (c) 2024 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Yunzhou Xie, Eric Wieser
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

section Basic
variable {R I J K L}

theorem comp_map_map (M : Matrix I J (Matrix K L R)) (f : R → R') :
  comp I J K L _ (M.map (fun M' => M'.map f)) = (comp I J K L _ M).map f := rfl

@[simp]
theorem comp_single_single
    [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L] [Zero R] (i j k l r) :
    comp I J K L R (single i j (single k l r))
      = single (i, k) (j, l) r := by
  ext ⟨i', k'⟩ ⟨j', l'⟩
  dsimp [comp_apply]
  obtain hi | rfl := ne_or_eq i i'
  · rw [single_apply_of_row_ne hi,
      single_apply_of_row_ne (ne_of_apply_ne Prod.fst hi), Matrix.zero_apply]
  obtain hj | rfl := ne_or_eq j j'
  · rw [single_apply_of_col_ne _ _ hj,
      single_apply_of_col_ne _ _ (ne_of_apply_ne Prod.fst hj), Matrix.zero_apply]
  rw [single_apply_same]
  obtain hk | rfl := ne_or_eq k k'
  · rw [single_apply_of_row_ne hk,
      single_apply_of_row_ne (ne_of_apply_ne Prod.snd hk)]
  obtain hj | rfl := ne_or_eq l l'
  · rw [single_apply_of_col_ne _ _ hj,
      single_apply_of_col_ne _ _ (ne_of_apply_ne Prod.snd hj)]
  rw [single_apply_same, single_apply_same]

@[deprecated (since := "2025-05-05")] alias comp_stdBasisMatrix_stdBasisMatrix := comp_single_single

@[simp]
theorem comp_symm_single
    [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L] [Zero R] (ii jj r) :
    (comp I J K L R).symm (single ii jj r) =
      (single ii.1 jj.1 (single ii.2 jj.2 r)) :=
  (comp I J K L R).symm_apply_eq.2 <| comp_single_single _ _ _ _ _ |>.symm

@[deprecated (since := "2025-05-05")] alias comp_symm_stdBasisMatrix := comp_symm_single

@[simp]
theorem comp_diagonal_diagonal [DecidableEq I] [DecidableEq J] [Zero R] (d : I → J → R) :
    comp I I J J R (diagonal fun i => diagonal fun j => d i j)
      = diagonal fun ij => d ij.1 ij.2 := by
  ext ⟨i₁, j₁⟩ ⟨i₂, j₂⟩
  dsimp [comp_apply]
  obtain hi | rfl := ne_or_eq i₁ i₂
  · rw [diagonal_apply_ne _ hi, diagonal_apply_ne _ (ne_of_apply_ne Prod.fst hi),
      Matrix.zero_apply]
  rw [diagonal_apply_eq]
  obtain hj | rfl := ne_or_eq j₁ j₂
  · rw [diagonal_apply_ne _ hj, diagonal_apply_ne _ (ne_of_apply_ne Prod.snd hj)]
  rw [diagonal_apply_eq, diagonal_apply_eq]

@[simp]
theorem comp_symm_diagonal [DecidableEq I] [DecidableEq J] [Zero R] (d : I × J → R) :
    (comp I I J J R).symm (diagonal d) = diagonal fun i => diagonal fun j => d (i, j) :=
  (comp I I J J R).symm_apply_eq.2 <| (comp_diagonal_diagonal fun i j => d (i, j)).symm

theorem comp_transpose (M : Matrix I J (Matrix K L R)) :
  comp J I K L R Mᵀ = (comp _ _ _ _ R <| M.map (·ᵀ))ᵀ := rfl

theorem comp_map_transpose (M : Matrix I J (Matrix K L R)) :
  comp I J L K R (M.map (·ᵀ)) = (comp _ _ _ _ R Mᵀ)ᵀ := rfl

theorem comp_symm_transpose (M : Matrix (I × K) (J × L) R) :
  (comp J I L K R).symm Mᵀ = (((comp I J K L R).symm M).map (·ᵀ))ᵀ := rfl

end Basic

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
  commutes' _ := comp_diagonal_diagonal _

@[simp]
theorem compAlgEquiv_apply (M : Matrix I I (Matrix J J R)) :
    compAlgEquiv I J R K M = comp I I J J R M := rfl

@[simp]
theorem compAlgEquiv_symm_apply (M : Matrix (I × J) (I × J) R) :
    (compAlgEquiv I J R K).symm M = (comp I I J J R).symm M := rfl

end Algebra

end Matrix
