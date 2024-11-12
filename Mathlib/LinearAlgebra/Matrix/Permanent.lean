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

 - `Matrix.perm`: the permanent of a square matrix, as a sum over permutations

-/

universe u v

open Equiv Fintype Finset

namespace Matrix

open Matrix

variable {n : Type*} [DecidableEq n] [Fintype n]
variable {R : Type v} [CommRing R]

/-- The permanent of a matrix defined as a sum over all permutations -/
def perm (M : Matrix n n R) : R := ∑ σ : Perm n, ∏ i, M (σ i) i


@[simp]
theorem perm_diagonal {d : n → R} : perm (diagonal d) = ∏ i, d i := by
  refine (Finset.sum_eq_single 1 ?_ ?_).trans ?_
  · rintro σ - h2
    cases' not_forall.1 (mt Equiv.ext h2) with x h3
    apply Finset.prod_eq_zero (mem_univ x)
    exact if_neg h3
  · simp
  · simp

@[simp]
theorem perm_zero (_ : Nonempty n) : perm (0 : Matrix n n R) = 0 := by simp [perm]

@[simp]
theorem perm_one : perm (1 : Matrix n n R) = 1 := by rw [← diagonal_one]; simp [-diagonal_one]

theorem perm_isEmpty [IsEmpty n] {A : Matrix n n R} : perm A = 1 := by simp [perm]

@[simp]
theorem coe_perm_isEmpty [IsEmpty n] : (perm : Matrix n n R → R) = Function.const _ 1 := by
  ext
  exact perm_isEmpty

theorem perm_eq_one_of_card_eq_zero {A : Matrix n n R} (h : Fintype.card n = 0) : perm A = 1 :=
  haveI : IsEmpty n := Fintype.card_eq_zero_iff.mp h
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

theorem perm_eq_elem_of_card_eq_one {A : Matrix n n R} (h : Fintype.card n = 1) (k : n) :
    perm A = A k k :=
  haveI : Subsingleton n := Fintype.card_le_one_iff_subsingleton.mp h.le
  perm_eq_elem_of_subsingleton _ _

/-- Transposing a matrix preserves the permanent. -/
@[simp]
theorem perm_transpose (M : Matrix n n R) : Mᵀ.perm = M.perm := by
  rw [perm, perm]
  refine Fintype.sum_bijective _ inv_involutive.bijective _ _ ?_
  intro σ
  apply Fintype.prod_equiv σ
  simp

/-- Permuting the columns does not change the permanent. -/
theorem perm_permute (σ : Perm n) (M : Matrix n n R) :
    (M.submatrix σ id).perm = M.perm := by
  refine Fintype.sum_bijective _ (Group.mulLeft_bijective σ) _ _ ?_
  intro τ
  rfl

/-- Permuting the rows does not change the permanent. -/
theorem perm_permute' (σ : Perm n) (M : Matrix n n R) :
    (M.submatrix id σ).perm = M.perm := by
  rw [perm, perm]
  refine Fintype.sum_bijective _ (Group.mulRight_bijective σ⁻¹) _ _ ?_
  intro τ
  refine Fintype.prod_bijective _ (Equiv.bijective σ) _ _ ?_
  simp

end Matrix
