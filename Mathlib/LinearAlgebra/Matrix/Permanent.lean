/-
Copyright (c) 2024 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Matrix.Diagonal
/-!
# Permanent of a matrix

This file defines the permanent of a matrix, `Matrix.permanent`, and some of its properties.

## Main definitions

* `Matrix.permanent`: the permanent of a square matrix, as a sum over permutations

-/

open Equiv Fintype Finset

namespace Matrix

variable {n : Type*} [DecidableEq n] [Fintype n]
variable {R : Type*} [CommSemiring R]

/-- The permanent of a square matrix defined as a sum over all permutations. This is analogous to
the determinant but without alternating signs. -/
def permanent (M : Matrix n n R) : R := ∑ σ : Perm n, ∏ i, M (σ i) i

@[simp]
theorem permanent_diagonal {d : n → R} : permanent (diagonal d) = ∏ i, d i := by
  refine (sum_eq_single 1 (fun σ _ hσ ↦ ?_) (fun h ↦ (h <| mem_univ _).elim)).trans ?_
  · match not_forall.mp (mt Equiv.ext hσ) with
    | ⟨x, hx⟩ => exact Finset.prod_eq_zero (mem_univ x) (if_neg hx)
  · simp only [Perm.one_apply, diagonal_apply_eq]

@[simp]
theorem permanent_zero [Nonempty n] : permanent (0 : Matrix n n R) = 0 := by simp [permanent]

@[simp]
theorem permanent_one : permanent (1 : Matrix n n R) = 1 := by
  rw [← diagonal_one]; simp [-diagonal_one]

theorem permanent_isEmpty [IsEmpty n] {A : Matrix n n R} : permanent A = 1 := by simp [permanent]

theorem permanent_eq_one_of_card_eq_zero {A : Matrix n n R} (h : card n = 0) : permanent A = 1 :=
  haveI : IsEmpty n := card_eq_zero_iff.mp h
  permanent_isEmpty

/-- If `n` has only one element, the permanent of an `n` by `n` matrix is just that element.
Although `Unique` implies `DecidableEq` and `Fintype`, the instances might
not be syntactically equal. Thus, we need to fill in the args explicitly. -/
@[simp]
theorem permanent_unique {n : Type*} [Unique n] [DecidableEq n] [Fintype n] (A : Matrix n n R) :
    permanent A = A default default := by simp [permanent, univ_unique]

theorem permanent_eq_elem_of_subsingleton [Subsingleton n] (A : Matrix n n R) (k : n) :
    permanent A = A k k := by
  have := uniqueOfSubsingleton k
  convert permanent_unique A

theorem permanent_eq_elem_of_card_eq_one {A : Matrix n n R} (h : card n = 1) (k : n) :
    permanent A = A k k :=
  haveI : Subsingleton n := card_le_one_iff_subsingleton.mp h.le
  permanent_eq_elem_of_subsingleton _ _

/-- Transposing a matrix preserves the permanent. -/
@[simp]
theorem permanent_transpose (M : Matrix n n R) : Mᵀ.permanent = M.permanent := by
  refine sum_bijective _ inv_involutive.bijective _ _ ?_
  intro σ
  apply Fintype.prod_equiv σ
  simp

/-- Permuting the columns does not change the permanent. -/
theorem permanent_permute_cols (σ : Perm n) (M : Matrix n n R) :
    (M.submatrix σ id).permanent = M.permanent :=
  (Group.mulLeft_bijective σ).sum_comp fun τ ↦ ∏ i : n, M (τ i) i

/-- Permuting the rows does not change the permanent. -/
theorem permanent_permute_rows (σ : Perm n) (M : Matrix n n R) :
    (M.submatrix id σ).permanent = M.permanent := by
  rw [← permanent_transpose, transpose_submatrix, permanent_permute_cols, permanent_transpose]

end Matrix
