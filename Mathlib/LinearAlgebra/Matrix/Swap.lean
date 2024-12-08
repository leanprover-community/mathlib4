/-
Copyright (c) 2024 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Swap matrices

A swap matrix indexed by `i` and `j` is the matrix that, when multiplying another matrix
on the left (resp. on the right), swaps the `i`-th row with the `j`-th row
(resp. the `i`-th column with the `j`-th column).

Swap matrices are a special case of *elementary matrices*. For transvections see
`Mathlib.LinearAlgebra.Matrix.Transvection`.
-/

namespace Matrix

variable {R : Type*} [Ring R]
variable {n m : Type*}

lemma ext_of_mulVec [DecidableEq m] [Fintype m] {g k : Matrix n m R}
    (h : ∀ i, g *ᵥ Pi.single i 1 = k *ᵥ Pi.single i 1) :
    g = k := by
  ext i j
  simp only [mulVec_single, mul_one] at h
  exact congrFun (h j) i

@[simp]
lemma stdBasisMatrix_transpose [DecidableEq n] (i j : n) (a : R) :
    (stdBasisMatrix i j a).transpose = stdBasisMatrix j i a := by
  unfold stdBasisMatrix
  aesop

end Matrix

namespace Matrix

section Def

variable {R n : Type*} [Ring R] [DecidableEq n]

variable (R) in
/-- The swap matrix `swap R i j` is the identity matrix with the
`i`-th and `j`-th rows modified such that multiplying by it on the
left (resp. right) corresponds to swapping the `i`-th and `j`-th row (resp. column). -/
def swap (i j : n) : Matrix n n R :=
  1 - stdBasisMatrix i i 1
    - stdBasisMatrix j j 1
    + stdBasisMatrix i j 1
    + stdBasisMatrix j i 1

lemma swap_eq_swap (i j : n) :
    swap R i j = swap R j i := by
  simp only [swap]
  abel

@[simp]
lemma swap_transpose (i j : n) : (swap R i j).transpose = swap R i j := by
  simp only [swap, transpose_add, transpose_sub, transpose_one, stdBasisMatrix_transpose]
  abel

@[simp]
lemma map_swap {S : Type*} [Ring S] (f : R →+* S) (i j : n) : (swap R i j).map f = swap S i j := by
  ext a b
  simp only [swap, map_apply, add_apply, sub_apply, stdBasisMatrix, map_add, map_sub,
    RingHom.map_ite_one_zero, add_left_inj, sub_left_inj]
  by_cases h : a = b
  · subst h
    simp
  · simp_all

variable [Fintype n]

lemma swap_mulVec_single (i j : n) (r : R) :
    swap R i j *ᵥ Pi.single i r = Pi.single j r := by
  ext l
  simp only [swap, Matrix.add_mulVec, Matrix.sub_mulVec, one_mulVec, Matrix.mulVec_stdBasisMatrix,
    Pi.single_eq_same, mul_one, one_mul, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  split_ifs <;> aesop

/-- Variant of `Matrix.swap_mulVec_single` with `i` and `j` switched in `Pi.single`. -/
lemma swap_mulVec_single' (i j : n) (r : R) :
    swap R i j *ᵥ Pi.single j r = Pi.single i r := by
  rw [swap_eq_swap, swap_mulVec_single]

lemma swap_mulVec_single_of_ne {i j k : n} (hik : i ≠ k) (hjk : j ≠ k) (r : R) :
    swap R i j *ᵥ Pi.single k r = Pi.single k r := by
  ext l
  simp only [swap, add_mulVec, sub_mulVec, one_mulVec, mulVec_stdBasisMatrix,
    Pi.single_eq_same, mul_one, one_mul, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  split_ifs <;> aesop

lemma swap_mulVec_apply (i j : n) (a : n → R) :
    (swap R i j *ᵥ a) i = a j := by
  induction' a using Pi.induction_add with f g hf hg x y
  · simp
  · simp [mulVec_add, hf, hg]
  · by_cases h : i = x
    · subst h
      simp_rw [swap_mulVec_single, Pi.single_apply]
      aesop
    · by_cases hj : j = x
      · subst hj
        simp_rw [swap_mulVec_single', Pi.single_apply]
      simp_rw [swap_mulVec_single_of_ne h hj, Pi.single_apply]
      aesop

/-- Multiplying with `swap R i j` on the left swaps the `i`-th row with the `j`-th row. -/
@[simp]
lemma swap_mul_apply (a i j : n) (g : Matrix n n R) :
    (swap R i j * g) i a = g j a := by
  by_cases i = j
  all_goals simp [swap, add_mul, sub_mul]; aesop

/-- Multiplying with `swap R i j` on the left swaps the `j`-th row with the `i`-th row. -/
@[simp]
lemma swap_mul_apply' (a i j : n) (g : Matrix n n R) :
    (swap R i j * g) j a = g i a := by
  rw [swap_eq_swap, swap_mul_apply]

@[simp]
lemma swap_mul_of_ne {a b i j : n} (hai : a ≠ i) (haj : a ≠ j) (g : Matrix n n R) :
    (swap R i j * g) a b = g a b := by
  by_cases i = j
  all_goals simp [swap, add_mul, sub_mul]; aesop

/-- Multiplying with `swap R i j` on the right swaps the `i`-th column with the `j`-th column. -/
@[simp]
lemma mul_swap_apply (a i j : n) (g : Matrix n n R) :
    (g * swap R i j) a i = g a j := by
  by_cases i = j
  all_goals simp [swap, mul_add, mul_sub]; aesop

/-- Multiplying with `swap R i j` on the right swaps the `j`-th column with the `i`-th column. -/
@[simp]
lemma mul_swap_apply' (a i j : n) (g : Matrix n n R) :
    (g * swap R i j) a j = g a i := by
  rw [swap_eq_swap, mul_swap_apply]

@[simp]
lemma mul_swap_of_ne {a b : n} {i j : n} (hbi : b ≠ i) (hbj : b ≠ j) (g : Matrix n n R) :
    (g * swap R i j) a b = g a b := by
  by_cases i = j
  all_goals simp [swap, mul_add, mul_sub]; aesop

/-- Swap matrices are self inverse. -/
lemma swap_mul_self (i j : n) : swap R i j * swap R i j = 1 := by
  refine ext_of_mulVec (fun k ↦ ?_)
  rw [one_mulVec, ← Matrix.mulVec_mulVec]
  by_cases hik : i = k
  · subst hik
    rw [swap_mulVec_single, swap_eq_swap, swap_mulVec_single]
  · by_cases hjk : j = k
    · subst hjk
      rw [swap_eq_swap, swap_mulVec_single, swap_eq_swap, swap_mulVec_single]
    · rw [swap_mulVec_single_of_ne hik hjk, swap_mulVec_single_of_ne hik hjk]

end Def

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
  simp

end GeneralLinearGroup

end Matrix
