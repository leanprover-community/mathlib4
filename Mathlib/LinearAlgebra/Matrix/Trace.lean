/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.RowCol
import Mathlib.Data.Matrix.Notation

/-!
# Trace of a matrix

This file defines the trace of a matrix, the map sending a matrix to the sum of its diagonal
entries.

See also `LinearAlgebra.Trace` for the trace of an endomorphism.

## Tags

matrix, trace, diagonal

-/


open Matrix

namespace Matrix

variable {ι m n p : Type*} {α R S : Type*}
variable [Fintype m] [Fintype n] [Fintype p]

section AddCommMonoid

variable [AddCommMonoid R]

/-- The trace of a square matrix. For more bundled versions, see:
* `Matrix.traceAddMonoidHom`
* `Matrix.traceLinearMap`
-/
def trace (A : Matrix n n R) : R :=
  ∑ i, diag A i

lemma trace_diagonal {o} [Fintype o] [DecidableEq o] (d : o → R) :
    trace (diagonal d) = ∑ i, d i := by
  simp only [trace, diag_apply, diagonal_apply_eq]

variable (n R)

@[simp]
theorem trace_zero : trace (0 : Matrix n n R) = 0 :=
  (Finset.sum_const (0 : R)).trans <| smul_zero _

variable {n R}

@[simp]
lemma trace_eq_zero_of_isEmpty [IsEmpty n] (A : Matrix n n R) : trace A = 0 := by simp [trace]

@[simp]
theorem trace_add (A B : Matrix n n R) : trace (A + B) = trace A + trace B :=
  Finset.sum_add_distrib

@[simp]
theorem trace_smul [DistribSMul α R] (r : α) (A : Matrix n n R) :
    trace (r • A) = r • trace A :=
  Finset.smul_sum.symm

@[simp]
theorem trace_transpose (A : Matrix n n R) : trace Aᵀ = trace A :=
  rfl

@[simp]
theorem trace_conjTranspose [StarAddMonoid R] (A : Matrix n n R) : trace Aᴴ = star (trace A) :=
  (star_sum _ _).symm

variable (n α R)

/-- `Matrix.trace` as an `AddMonoidHom` -/
@[simps]
def traceAddMonoidHom : Matrix n n R →+ R where
  toFun := trace
  map_zero' := trace_zero n R
  map_add' := trace_add

/-- `Matrix.trace` as a `LinearMap` -/
@[simps]
def traceLinearMap [Semiring α] [Module α R] : Matrix n n R →ₗ[α] R where
  toFun := trace
  map_add' := trace_add
  map_smul' := trace_smul

variable {n α R}

@[simp]
theorem trace_list_sum (l : List (Matrix n n R)) : trace l.sum = (l.map trace).sum :=
  map_list_sum (traceAddMonoidHom n R) l

@[simp]
theorem trace_multiset_sum (s : Multiset (Matrix n n R)) : trace s.sum = (s.map trace).sum :=
  map_multiset_sum (traceAddMonoidHom n R) s

@[simp]
theorem trace_sum (s : Finset ι) (f : ι → Matrix n n R) :
    trace (∑ i ∈ s, f i) = ∑ i ∈ s, trace (f i) :=
  map_sum (traceAddMonoidHom n R) f s

theorem _root_.AddMonoidHom.map_trace [AddCommMonoid S] {F : Type*} [FunLike F R S]
    [AddMonoidHomClass F R S] (f : F) (A : Matrix n n R) :
    f (trace A) = trace ((f : R →+ S).mapMatrix A) :=
  map_sum f (fun i => diag A i) Finset.univ

lemma trace_blockDiagonal [DecidableEq p] (M : p → Matrix n n R) :
    trace (blockDiagonal M) = ∑ i, trace (M i) := by
  simp [blockDiagonal, trace, Finset.sum_comm (γ := n), Fintype.sum_prod_type]

lemma trace_blockDiagonal' [DecidableEq p] {m : p → Type*} [∀ i, Fintype (m i)]
    (M : ∀ i, Matrix (m i) (m i) R) :
    trace (blockDiagonal' M) = ∑ i, trace (M i) := by
  simp [blockDiagonal', trace, Finset.sum_sigma']

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup R]

@[simp]
theorem trace_sub (A B : Matrix n n R) : trace (A - B) = trace A - trace B :=
  Finset.sum_sub_distrib

@[simp]
theorem trace_neg (A : Matrix n n R) : trace (-A) = -trace A :=
  Finset.sum_neg_distrib

end AddCommGroup

section One

variable [DecidableEq n] [AddCommMonoidWithOne R]

@[simp]
theorem trace_one : trace (1 : Matrix n n R) = Fintype.card n := by
  simp_rw [trace, diag_one, Pi.one_def, Finset.sum_const, nsmul_one, Finset.card_univ]

end One

section Mul

@[simp]
theorem trace_transpose_mul [AddCommMonoid R] [Mul R] (A : Matrix m n R) (B : Matrix n m R) :
    trace (Aᵀ * Bᵀ) = trace (A * B) :=
  Finset.sum_comm

theorem trace_mul_comm [AddCommMonoid R] [CommMagma R] (A : Matrix m n R) (B : Matrix n m R) :
    trace (A * B) = trace (B * A) := by rw [← trace_transpose, ← trace_transpose_mul, transpose_mul]

theorem trace_mul_cycle [NonUnitalCommSemiring R] (A : Matrix m n R) (B : Matrix n p R)
    (C : Matrix p m R) : trace (A * B * C) = trace (C * A * B) := by
  rw [trace_mul_comm, Matrix.mul_assoc]

theorem trace_mul_cycle' [NonUnitalCommSemiring R] (A : Matrix m n R) (B : Matrix n p R)
    (C : Matrix p m R) : trace (A * (B * C)) = trace (C * (A * B)) := by
  rw [← Matrix.mul_assoc, trace_mul_comm]

@[simp]
theorem trace_replicateCol_mul_replicateRow {ι : Type*} [Unique ι] [NonUnitalNonAssocSemiring R]
    (a b : n → R) : trace (replicateCol ι a * replicateRow ι b) = a ⬝ᵥ b := by
  apply Finset.sum_congr rfl
  simp [mul_apply]

@[deprecated (since := "2025-03-20")] alias trace_col_mul_row := trace_replicateCol_mul_replicateRow

end Mul

lemma trace_submatrix_succ {n : ℕ} [AddCommMonoid R]
    (M : Matrix (Fin n.succ) (Fin n.succ) R) :
    M 0 0 + trace (submatrix M Fin.succ Fin.succ) = trace M := by
  delta trace
  rw [← (finSuccEquiv n).symm.sum_comp]
  simp

section CommSemiring

variable [DecidableEq m] [CommSemiring R]

-- TODO(https://github.com/leanprover-community/mathlib4/issues/6607): fix elaboration so that the ascription isn't needed
theorem trace_units_conj (M : (Matrix m m R)ˣ) (N : Matrix m m R) :
    trace ((M : Matrix _ _ _) * N * (↑M⁻¹ : Matrix _ _ _)) = trace N := by
  rw [trace_mul_cycle, Units.inv_mul, one_mul]

set_option linter.docPrime false in
-- TODO(https://github.com/leanprover-community/mathlib4/issues/6607): fix elaboration so that the ascription isn't needed
theorem trace_units_conj' (M : (Matrix m m R)ˣ) (N : Matrix m m R) :
    trace ((↑M⁻¹ : Matrix _ _ _) * N * (↑M : Matrix _ _ _)) = trace N :=
  trace_units_conj M⁻¹ N

end CommSemiring

section Fin

variable [AddCommMonoid R]

/-! ### Special cases for `Fin n` for low values of `n`
-/

@[simp]
theorem trace_fin_zero (A : Matrix (Fin 0) (Fin 0) R) : trace A = 0 :=
  rfl

theorem trace_fin_one (A : Matrix (Fin 1) (Fin 1) R) : trace A = A 0 0 :=
  add_zero _

theorem trace_fin_two (A : Matrix (Fin 2) (Fin 2) R) : trace A = A 0 0 + A 1 1 :=
  congr_arg (_ + ·) (add_zero (A 1 1))

theorem trace_fin_three (A : Matrix (Fin 3) (Fin 3) R) : trace A = A 0 0 + A 1 1 + A 2 2 := by
  rw [← add_zero (A 2 2), add_assoc]
  rfl

@[simp]
theorem trace_fin_one_of (a : R) : trace !![a] = a :=
  trace_fin_one _

@[simp]
theorem trace_fin_two_of (a b c d : R) : trace !![a, b; c, d] = a + d :=
  trace_fin_two _

@[simp]
theorem trace_fin_three_of (a b c d e f g h i : R) :
    trace !![a, b, c; d, e, f; g, h, i] = a + e + i :=
  trace_fin_three _

end Fin

section single

variable {l m n : Type*} {R α : Type*} [DecidableEq l] [DecidableEq m] [DecidableEq n]
variable [Fintype n] [AddCommMonoid α] (i j : n) (c : α)

@[simp]
theorem trace_single_eq_of_ne (h : i ≠ j) : trace (single i j c) = 0 := by
  simp [trace, h]

@[deprecated (since := "2025-05-05")]
alias StdBasisMatrix.trace_zero := trace_single_eq_of_ne

@[simp]
theorem trace_single_eq_same : trace (single i i c) = c := by
  simp [trace]

@[deprecated (since := "2025-05-05")]
alias StdBasisMatrix.trace_eq := trace_single_eq_same

end single

end Matrix
