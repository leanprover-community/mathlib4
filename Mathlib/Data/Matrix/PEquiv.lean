/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.PEquiv

/-!
# partial equivalences for matrices

Using partial equivalences to represent matrices.
This file introduces the function `PEquiv.toMatrix`, which returns a matrix containing ones and
zeros. For any partial equivalence `f`, `f.toMatrix i j = 1 ↔ f i = some j`.

The following important properties of this function are proved
`toMatrix_trans : (f.trans g).toMatrix = f.toMatrix * g.toMatrix`
`toMatrix_symm  : f.symm.toMatrix = f.toMatrixᵀ`
`toMatrix_refl : (PEquiv.refl n).toMatrix = 1`
`toMatrix_bot : ⊥.toMatrix = 0`

This theory gives the matrix representation of projection linear maps, and their right inverses.
For example, the matrix `(single (0 : Fin 1) (i : Fin n)).toMatrix` corresponds to the ith
projection map from R^n to R.

Any injective function `Fin m → Fin n` gives rise to a `PEquiv`, whose matrix is the projection
map from R^m → R^n represented by the same function. The transpose of this matrix is the right
inverse of this map, sending anything not in the image to zero.

## notations

This file uses `ᵀ` for `Matrix.transpose`.
-/

assert_not_exists Field

namespace PEquiv

open Matrix

universe u v

variable {k l m n : Type*}
variable {α β : Type*}

open Matrix

/-- `toMatrix` returns a matrix containing ones and zeros. `f.toMatrix i j` is `1` if
  `f i = some j` and `0` otherwise -/
def toMatrix [DecidableEq n] [Zero α] [One α] (f : m ≃. n) : Matrix m n α :=
  of fun i j => if j ∈ f i then (1 : α) else 0

-- TODO: set as an equation lemma for `toMatrix`, see https://github.com/leanprover-community/mathlib4/pull/3024
@[simp]
theorem toMatrix_apply [DecidableEq n] [Zero α] [One α] (f : m ≃. n) (i j) :
    toMatrix f i j = if j ∈ f i then (1 : α) else 0 :=
  rfl

theorem toMatrix_mul_apply [Fintype m] [DecidableEq m] [NonAssocSemiring α] (f : l ≃. m) (i j)
    (M : Matrix m n α) : (f.toMatrix * M :) i j = Option.casesOn (f i) 0 fun fi => M fi j := by
  dsimp [toMatrix, Matrix.mul_apply]
  rcases h : f i with - | fi
  · simp
  · rw [Finset.sum_eq_single fi] <;> simp +contextual [eq_comm]

theorem mul_toMatrix_apply [Fintype m] [NonAssocSemiring α] [DecidableEq n] (M : Matrix l m α)
    (f : m ≃. n) (i j) : (M * f.toMatrix :) i j = Option.casesOn (f.symm j) 0 (M i) := by
  dsimp [Matrix.mul_apply, toMatrix_apply]
  rcases h : f.symm j with - | fj
  · simp [h, ← f.eq_some_iff]
  · rw [Finset.sum_eq_single fj]
    · simp [h, ← f.eq_some_iff]
    · rintro b - n
      simp [h, ← f.eq_some_iff, n.symm]
    · simp

theorem toMatrix_symm [DecidableEq m] [DecidableEq n] [Zero α] [One α] (f : m ≃. n) :
    (f.symm.toMatrix : Matrix n m α) = f.toMatrixᵀ := by
  ext
  simp only [transpose, mem_iff_mem f, toMatrix_apply]
  congr

@[simp]
theorem toMatrix_refl [DecidableEq n] [Zero α] [One α] :
    ((PEquiv.refl n).toMatrix : Matrix n n α) = 1 := by
  ext
  simp [toMatrix_apply, one_apply]

@[simp]
theorem toMatrix_toPEquiv_apply [DecidableEq n] [Zero α] [One α] (f : m ≃ n) (i) :
    f.toPEquiv.toMatrix i = Pi.single (f i) (1 : α) := by
  ext
  simp [toMatrix_apply, Pi.single_apply, eq_comm]

@[simp]
theorem transpose_toMatrix_toPEquiv_apply
    [DecidableEq m] [DecidableEq n] [Zero α] [One α] (f : m ≃ n) (j) :
    f.toPEquiv.toMatrixᵀ j = Pi.single (f.symm j) (1 : α) := by
  ext
  simp [toMatrix_apply, Pi.single_apply, eq_comm, ← Equiv.apply_eq_iff_eq_symm_apply]

theorem toMatrix_toPEquiv_mul [Fintype m] [DecidableEq m]
    [NonAssocSemiring α] (f : l ≃ m) (M : Matrix m n α) :
    f.toPEquiv.toMatrix * M = M.submatrix f id := by
  ext i j
  rw [toMatrix_mul_apply, Equiv.toPEquiv_apply, submatrix_apply, id]

theorem mul_toMatrix_toPEquiv [Fintype m] [DecidableEq n]
    [NonAssocSemiring α] (M : Matrix l m α) (f : m ≃ n) :
    (M * f.toPEquiv.toMatrix) = M.submatrix id f.symm :=
  Matrix.ext fun i j => by
    rw [PEquiv.mul_toMatrix_apply, ← Equiv.toPEquiv_symm, Equiv.toPEquiv_apply,
      Matrix.submatrix_apply, id]

lemma toMatrix_toPEquiv_mulVec [DecidableEq n] [Fintype n]
    [NonAssocSemiring α] (σ : m ≃ n) (a : n → α) :
    σ.toPEquiv.toMatrix *ᵥ a = a ∘ σ := by
  ext j
  simp [toMatrix, mulVec, dotProduct]

lemma vecMul_toMatrix_toPEquiv [DecidableEq n] [Fintype m]
    [NonAssocSemiring α] (σ : m ≃ n) (a : m → α) :
    a ᵥ* σ.toPEquiv.toMatrix = a ∘ σ.symm := by
  classical
  ext j
  simp [toMatrix, σ.apply_eq_iff_eq_symm_apply, vecMul, dotProduct]

theorem toMatrix_trans [Fintype m] [DecidableEq m] [DecidableEq n] [NonAssocSemiring α] (f : l ≃. m)
    (g : m ≃. n) : ((f.trans g).toMatrix : Matrix l n α) = f.toMatrix * g.toMatrix := by
  ext i j
  rw [toMatrix_mul_apply]
  dsimp [toMatrix, PEquiv.trans]
  cases f i <;> simp

@[simp]
theorem toMatrix_bot [DecidableEq n] [Zero α] [One α] :
    ((⊥ : PEquiv m n).toMatrix : Matrix m n α) = 0 :=
  rfl

theorem toMatrix_injective [DecidableEq n] [MulZeroOneClass α] [Nontrivial α] :
    Function.Injective (@toMatrix m n α _ _ _) := by
  intro f g
  refine not_imp_not.1 ?_
  simp only [Matrix.ext_iff.symm, toMatrix_apply, PEquiv.ext_iff, not_forall, exists_imp]
  intro i hi
  use i
  rcases hf : f i with - | fi
  · rcases hg : g i with - | gi
    · rw [hf, hg] at hi; exact (hi rfl).elim
    · use gi
      simp
  · use fi
    simp [hf.symm, Ne.symm hi]

theorem toMatrix_swap [DecidableEq n] [AddGroupWithOne α] (i j : n) :
    (Equiv.swap i j).toPEquiv.toMatrix =
      (1 : Matrix n n α) - (single i i).toMatrix - (single j j).toMatrix + (single i j).toMatrix +
        (single j i).toMatrix := by
  ext
  dsimp [toMatrix, single, Equiv.swap_apply_def, Equiv.toPEquiv, one_apply]
  split_ifs <;> simp_all

@[simp]
theorem single_mul_single [Fintype n] [DecidableEq k] [DecidableEq m] [DecidableEq n]
    [NonAssocSemiring α] (a : m) (b : n) (c : k) :
    ((single a b).toMatrix : Matrix _ _ α) * (single b c).toMatrix = (single a c).toMatrix := by
  rw [← toMatrix_trans, single_trans_single]

theorem single_mul_single_of_ne [Fintype n] [DecidableEq n] [DecidableEq k] [DecidableEq m]
    [NonAssocSemiring α] {b₁ b₂ : n} (hb : b₁ ≠ b₂) (a : m) (c : k) :
    (single a b₁).toMatrix * (single b₂ c).toMatrix = (0 : Matrix _ _ α) := by
  rw [← toMatrix_trans, single_trans_single_of_ne hb, toMatrix_bot]

/-- Restatement of `single_mul_single`, which will simplify expressions in `simp` normal form,
  when associativity may otherwise need to be carefully applied. -/
@[simp]
theorem single_mul_single_right [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k]
    [DecidableEq m] [Semiring α] (a : m) (b : n) (c : k) (M : Matrix k l α) :
    (single a b).toMatrix * ((single b c).toMatrix * M) = (single a c).toMatrix * M := by
  rw [← Matrix.mul_assoc, single_mul_single]

/-- We can also define permutation matrices by permuting the rows of the identity matrix. -/
theorem toMatrix_toPEquiv_eq [DecidableEq n] [Zero α] [One α] (σ : Equiv.Perm n) :
    σ.toPEquiv.toMatrix = (1 : Matrix n n α).submatrix σ id :=
  Matrix.ext fun _ _ => if_congr Option.some_inj rfl rfl

@[simp]
lemma map_toMatrix [DecidableEq n] [NonAssocSemiring α] [NonAssocSemiring β]
    (f : α →+* β) (σ : m ≃. n) : σ.toMatrix.map f = σ.toMatrix := by
  ext i j
  simp

end PEquiv
