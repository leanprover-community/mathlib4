/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Invertible
import Mathlib.Data.Matrix.Basic

#align_import data.matrix.invertible from "leanprover-community/mathlib"@"722b3b152ddd5e0cf21c0a29787c76596cb6b422"

/-! # Extra lemmas about invertible matrices

A few of the `Invertible` lemmas generalize to multiplication of rectangular matrices.

For lemmas about the matrix inverse in terms of the determinant and adjugate, see `Matrix.inv`
in `LinearAlgebra/Matrix/NonsingularInverse.lean`.
-/


open scoped Matrix

variable {m n : Type*} {α : Type*}

variable [Fintype n] [DecidableEq n] [Semiring α]

namespace Matrix

#align matrix.inv_of_mul_self invOf_mul_self
#align matrix.mul_inv_of_self mul_invOf_self

/-- A copy of `invOf_mul_self_assoc` for rectangular matrices. -/
protected theorem invOf_mul_self_assoc (A : Matrix n n α) (B : Matrix n m α) [Invertible A] :
    ⅟ A * (A * B) = B := by rw [← Matrix.mul_assoc, invOf_mul_self, Matrix.one_mul]
#align matrix.inv_of_mul_self_assoc Matrix.invOf_mul_self_assoc

/-- A copy of `mul_invOf_self_assoc` for rectangular matrices. -/
protected theorem mul_invOf_self_assoc (A : Matrix n n α) (B : Matrix n m α) [Invertible A] :
    A * (⅟ A * B) = B := by rw [← Matrix.mul_assoc, mul_invOf_self, Matrix.one_mul]
#align matrix.mul_inv_of_self_assoc Matrix.mul_invOf_self_assoc

/-- A copy of `mul_invOf_mul_self_cancel` for rectangular matrices. -/
protected theorem mul_invOf_mul_self_cancel (A : Matrix m n α) (B : Matrix n n α) [Invertible B] :
    A * ⅟ B * B = A := by rw [Matrix.mul_assoc, invOf_mul_self, Matrix.mul_one]
#align matrix.mul_inv_of_mul_self_cancel Matrix.mul_invOf_mul_self_cancel

/-- A copy of `mul_mul_invOf_self_cancel` for rectangular matrices. -/
protected theorem mul_mul_invOf_self_cancel (A : Matrix m n α) (B : Matrix n n α) [Invertible B] :
    A * B * ⅟ B = A := by rw [Matrix.mul_assoc, mul_invOf_self, Matrix.mul_one]
#align matrix.mul_mul_inv_of_self_cancel Matrix.mul_mul_invOf_self_cancel

#align matrix.invertible_mul invertibleMul
#align matrix.inv_of_mul invOf_mul
#align matrix.invertible_of_invertible_mul invertibleOfInvertibleMul
#align matrix.invertible_of_mul_invertible invertibleOfMulInvertible

end Matrix

#align invertible.matrix_mul_left Invertible.mulLeft
#align invertible.matrix_mul_right Invertible.mulRight
