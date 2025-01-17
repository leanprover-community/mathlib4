/-
Copyright (c) 2024 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Data.Matrix.PEquiv

/-!
# Swap matrices

A swap matrix indexed by `i` and `j` is the matrix that, when multiplying another matrix
on the left (resp. on the right), swaps the `i`-th row with the `j`-th row
(resp. the `i`-th column with the `j`-th column).

Swap matrices are a special case of *elementary matrices*. For transvections see
`Mathlib.LinearAlgebra.Matrix.Transvection`.

## Implementation detail

This is a thin wrapper around `(Equiv.swap i j).toPEquiv.toMatrix`.
-/

namespace Equiv

open Matrix

variable {α n m : Type*}

lemma toPEquiv_toMatrix_mulVec_apply [Fintype n] [DecidableEq n]
    [NonAssocSemiring α] (σ : m ≃ n) (i : m) (a : n → α) :
    (σ.toPEquiv.toMatrix *ᵥ a) i = a (σ i) := by
  induction a using Pi.induction_add with
  | hone => simp
  | hmul f g hf hg => simp [hf, hg, Matrix.mulVec_add]
  | hsingle => simp [Pi.single_apply]

lemma toPEquiv_toMatrix_vecMul_apply [Fintype m] [DecidableEq n]
    [NonAssocSemiring α] (σ : m ≃ n) (i : n) (a : m → α) :
    (a ᵥ* σ.toPEquiv.toMatrix) i = a (σ.symm i) := by
  classical
  induction a using Pi.induction_add with
  | hone => simp
  | hmul f g hf hg => simp [hf, hg, Matrix.add_vecMul]
  | hsingle =>
      simp only [single_vecMul, PEquiv.toMatrix_apply, toPEquiv_apply, Option.mem_def,
        Option.some.injEq, mul_ite, mul_one, mul_zero, Pi.single_apply, symm_apply_eq]
      simp_rw [eq_comm]

end Equiv

namespace Matrix

section Def

variable {R n : Type*} [Zero R] [One R] [DecidableEq n]

variable (R) in
/-- The swap matrix `swap R i j` is the identity matrix with the
`i`-th and `j`-th rows modified such that multiplying by it on the
left (resp. right) corresponds to swapping the `i`-th and `j`-th row (resp. column). -/
def swap (i j : n) : Matrix n n R :=
  (Equiv.swap i j).toPEquiv.toMatrix

lemma swap_comm (i j : n) :
    swap R i j = swap R j i := by
  simp only [swap, Equiv.swap_comm]

@[simp]
lemma swap_transpose (i j : n) : (swap R i j).transpose = swap R i j := by
  simp only [swap]
  rw [← PEquiv.toMatrix_symm, ← Equiv.toPEquiv_symm, ← Equiv.Perm.inv_def, Equiv.swap_inv]

end Def

section

variable {R n : Type*} [Semiring R] [DecidableEq n]

@[simp]
lemma map_swap {S : Type*} [Semiring S] (f : R →+* S) (i j : n) :
    (swap R i j).map f = swap S i j := by
  simp [swap]

variable [Fintype n]

lemma swap_mulVec_single_left (i j : n) (r : R) :
    swap R i j *ᵥ Pi.single i r = Pi.single j r := by
  simp only [swap, Equiv.toPEquiv_toMatrix_mulVec_single, Equiv.symm_swap]
  rw [Equiv.swap_apply_left]

/-- Variant of `Matrix.swap_mulVec_single` with `i` and `j` switched in `Pi.single`. -/
lemma swap_mulVec_single_right (i j : n) (r : R) :
    swap R i j *ᵥ Pi.single j r = Pi.single i r := by
  rw [swap_comm, swap_mulVec_single_left]

lemma swap_mulVec_single_of_ne {i j k : n} (hik : k ≠ i) (hjk : k ≠ j) (r : R) :
    swap R i j *ᵥ Pi.single k r = Pi.single k r := by
  simp only [swap, Equiv.toPEquiv_toMatrix_mulVec_single, Equiv.symm_swap,
    Equiv.swap_apply_of_ne_of_ne hik hjk]

lemma swap_mulVec_apply (i j : n) (a : n → R) :
    (swap R i j *ᵥ a) i = a j := by
  simp [swap, Equiv.toPEquiv_toMatrix_mulVec_apply]

/-- Multiplying with `swap R i j` on the left swaps the `i`-th row with the `j`-th row. -/
@[simp]
lemma swap_mul_apply_left (a i j : n) (g : Matrix n n R) :
    (swap R i j * g) i a = g j a := by
  simp [swap, PEquiv.toPEquiv_mul_matrix]

/-- Multiplying with `swap R i j` on the left swaps the `j`-th row with the `i`-th row. -/
@[simp]
lemma swap_mul_apply_right (a i j : n) (g : Matrix n n R) :
    (swap R i j * g) j a = g i a := by
  rw [swap_comm, swap_mul_apply_left]

lemma swap_mul_of_ne {a b i j : n} (hai : a ≠ i) (haj : a ≠ j) (g : Matrix n n R) :
    (swap R i j * g) a b = g a b := by
  simp [swap, PEquiv.toPEquiv_mul_matrix, Equiv.swap_apply_of_ne_of_ne hai haj]

/-- Multiplying with `swap R i j` on the right swaps the `i`-th column with the `j`-th column. -/
@[simp]
lemma mul_swap_apply_left (a i j : n) (g : Matrix n n R) :
    (g * swap R i j) a i = g a j := by
  simp [swap, PEquiv.mul_toPEquiv_toMatrix]

/-- Multiplying with `swap R i j` on the right swaps the `j`-th column with the `i`-th column. -/
@[simp]
lemma mul_swap_apply_right (a i j : n) (g : Matrix n n R) :
    (g * swap R i j) a j = g a i := by
  rw [swap_comm, mul_swap_apply_left]

lemma mul_swap_of_ne {a b : n} {i j : n} (hbi : b ≠ i) (hbj : b ≠ j) (g : Matrix n n R) :
    (g * swap R i j) a b = g a b := by
  simp [swap, PEquiv.mul_toPEquiv_toMatrix, Equiv.swap_apply_of_ne_of_ne hbi hbj]

/-- Swap matrices are self inverse. -/
lemma swap_mul_self (i j : n) : swap R i j * swap R i j = 1 := by
  simp only [swap]
  rw [← Equiv.swap_inv, Equiv.Perm.inv_def]
  apply Equiv.toPEquiv_toMatrix_mul_symm_toPEquiv_toMatrix

end

namespace GeneralLinearGroup

variable (R : Type*) {n : Type*} [CommRing R] [DecidableEq n] [Fintype n]

/-- `Matrix.swap` as an element of `GL n R`. -/
@[simps]
def swap (i j : n) : GL n R where
  val := Matrix.swap R i j
  inv := Matrix.swap R i j
  val_inv := swap_mul_self i j
  inv_val := swap_mul_self i j

variable {R} {S : Type*} [CommRing S] (f : R →+* S)

@[simp]
lemma map_swap (i j : n) : (swap R i j).map f = swap S i j := by
  ext : 1
  simp [swap]

end GeneralLinearGroup

end Matrix
