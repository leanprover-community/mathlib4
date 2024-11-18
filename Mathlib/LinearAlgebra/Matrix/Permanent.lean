/-
Copyright (c) 2024 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Matrix.Basic
/-!
# Permanent of a matrix

This file defines the permanent of a matrix, `Matrix.perm`, and some of its properties.

## Main definitions

* `Matrix.perm`: the permanent of a square matrix, as a sum over permutations

-/

open Equiv Fintype Finset

namespace Matrix

open Matrix

variable {n : Type*} [DecidableEq n] [Fintype n]
variable {R : Type*} [CommSemiring R]

/-- The permanent of a matrix defined as a sum over all permutations -/
def perm (M : Matrix n n R) : R := ∑ σ : Perm n, ∏ i, M (σ i) i

@[simp]
theorem perm_diagonal {d : n → R} : perm (diagonal d) = ∏ i, d i := by
  refine (sum_eq_single 1 (fun σ _ hσ ↦ ?_) (fun h ↦ (h <| mem_univ _).elim)).trans ?_
  · match not_forall.mp (mt Equiv.ext hσ) with
    | ⟨x, hx⟩ => exact Finset.prod_eq_zero (mem_univ x) (if_neg hx)
  · simp only [Perm.one_apply, diagonal_apply_eq]

@[simp]
theorem perm_zero [Nonempty n] : perm (0 : Matrix n n R) = 0 := by simp [perm]

@[simp]
theorem perm_one : perm (1 : Matrix n n R) = 1 := by rw [← diagonal_one]; simp [-diagonal_one]

theorem perm_isEmpty [IsEmpty n] {A : Matrix n n R} : perm A = 1 := by simp [perm]

theorem perm_eq_one_of_card_eq_zero {A : Matrix n n R} (h : card n = 0) : perm A = 1 :=
  haveI : IsEmpty n := card_eq_zero_iff.mp h
  perm_isEmpty

/-- If `n` has only one element, the permanent of an `n` by `n` matrix is just that element.
Although `Unique` implies `DecidableEq` and `Fintype`, the instances might
not be syntactically equal. Thus, we need to fill in the args explicitly. -/
@[simp]
theorem perm_unique {n : Type*} [Unique n] [DecidableEq n] [Fintype n] (A : Matrix n n R) :
    perm A = A default default := by simp [perm, univ_unique]

theorem perm_eq_elem_of_subsingleton [Subsingleton n] (A : Matrix n n R) (k : n) :
    perm A = A k k := by
  have := uniqueOfSubsingleton k
  convert perm_unique A

theorem perm_eq_elem_of_card_eq_one {A : Matrix n n R} (h : card n = 1) (k : n) :
    perm A = A k k :=
  haveI : Subsingleton n := card_le_one_iff_subsingleton.mp h.le
  perm_eq_elem_of_subsingleton _ _

/-- Transposing a matrix preserves the permanent. -/
@[simp]
theorem perm_transpose (M : Matrix n n R) : Mᵀ.perm = M.perm := by
  refine sum_bijective _ inv_involutive.bijective _ _ ?_
  intro σ
  apply Fintype.prod_equiv σ
  simp

/-- Permuting the columns does not change the permanent. -/
theorem perm_permute_cols (σ : Perm n) (M : Matrix n n R) :
    (M.submatrix σ id).perm = M.perm :=
  (Group.mulLeft_bijective σ).sum_comp fun τ ↦ ∏ i : n, M (τ i) i

/-- Permuting the rows does not change the permanent. -/
theorem perm_permute_rows (σ : Perm n) (M : Matrix n n R) :
    (M.submatrix id σ).perm = M.perm := by
  rw [← perm_transpose, transpose_submatrix, perm_permute_cols, perm_transpose]

end Matrix
