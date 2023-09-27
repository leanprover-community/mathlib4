/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Invertible
import Mathlib.Data.Matrix.Basic

#align_import data.matrix.invertible from "leanprover-community/mathlib"@"722b3b152ddd5e0cf21c0a29787c76596cb6b422"

/-! # Extra lemmas about invertible matrices

Many of the `Invertible` lemmas are about `*`; this restates them to be about `⬝`.

For lemmas about the matrix inverse in terms of the determinant and adjugate, see `Matrix.inv`
in `LinearAlgebra/Matrix/NonsingularInverse.lean`.
-/


open scoped Matrix

variable {m n : Type*} {α : Type*}

variable [Fintype n] [DecidableEq n] [Semiring α]

namespace Matrix

/-- A copy of `invOf_mul_self` using `⬝` not `*`. -/
protected theorem invOf_mul_self (A : Matrix n n α) [Invertible A] : ⅟ A ⬝ A = 1 :=
  invOf_mul_self A
#align matrix.inv_of_mul_self Matrix.invOf_mul_self

/-- A copy of `mul_invOf_self` using `⬝` not `*`. -/
protected theorem mul_invOf_self (A : Matrix n n α) [Invertible A] : A ⬝ ⅟ A = 1 :=
  mul_invOf_self A
#align matrix.mul_inv_of_self Matrix.mul_invOf_self

/-- A copy of `invOf_mul_self_assoc` using `⬝` not `*`. -/
protected theorem invOf_mul_self_assoc (A : Matrix n n α) (B : Matrix n m α) [Invertible A] :
    ⅟ A ⬝ (A ⬝ B) = B := by rw [← Matrix.mul_assoc, Matrix.invOf_mul_self, Matrix.one_mul]
#align matrix.inv_of_mul_self_assoc Matrix.invOf_mul_self_assoc

/-- A copy of `mul_invOf_self_assoc` using `⬝` not `*`. -/
protected theorem mul_invOf_self_assoc (A : Matrix n n α) (B : Matrix n m α) [Invertible A] :
    A ⬝ (⅟ A ⬝ B) = B := by rw [← Matrix.mul_assoc, Matrix.mul_invOf_self, Matrix.one_mul]
#align matrix.mul_inv_of_self_assoc Matrix.mul_invOf_self_assoc

/-- A copy of `mul_invOf_mul_self_cancel` using `⬝` not `*`. -/
protected theorem mul_invOf_mul_self_cancel (A : Matrix m n α) (B : Matrix n n α) [Invertible B] :
    A ⬝ ⅟ B ⬝ B = A := by rw [Matrix.mul_assoc, Matrix.invOf_mul_self, Matrix.mul_one]
#align matrix.mul_inv_of_mul_self_cancel Matrix.mul_invOf_mul_self_cancel

/-- A copy of `mul_mul_invOf_self_cancel` using `⬝` not `*`. -/
protected theorem mul_mul_invOf_self_cancel (A : Matrix m n α) (B : Matrix n n α) [Invertible B] :
    A ⬝ B ⬝ ⅟ B = A := by rw [Matrix.mul_assoc, Matrix.mul_invOf_self, Matrix.mul_one]
#align matrix.mul_mul_inv_of_self_cancel Matrix.mul_mul_invOf_self_cancel

/-- A copy of `invertibleMul` using `⬝` not `*`. -/
@[reducible]
protected def invertibleMul (A B : Matrix n n α) [Invertible A] [Invertible B] :
    Invertible (A ⬝ B) :=
  { invertibleMul _ _ with invOf := ⅟ B ⬝ ⅟ A }
#align matrix.invertible_mul Matrix.invertibleMul

/-- A copy of `Invertible.mul` using `⬝` not `*`.-/
@[reducible]
def _root_.Invertible.matrixMul {A B : Matrix n n α} (_ : Invertible A) (_ : Invertible B) :
    Invertible (A ⬝ B) :=
  invertibleMul _ _
#align invertible.matrix_mul Invertible.matrixMul

protected theorem invOf_mul {A B : Matrix n n α} [Invertible A] [Invertible B]
    [Invertible (A ⬝ B)] : ⅟ (A ⬝ B) = ⅟ B ⬝ ⅟ A :=
  invOf_mul _ _
#align matrix.inv_of_mul Matrix.invOf_mul

/-- A copy of `invertibleOfInvertibleMul` using `⬝` not `*`. -/
@[reducible]
protected def invertibleOfInvertibleMul (a b : Matrix n n α) [Invertible a] [Invertible (a ⬝ b)] :
    Invertible b :=
  { invertibleOfInvertibleMul a b with invOf := ⅟ (a ⬝ b) ⬝ a }
#align matrix.invertible_of_invertible_mul Matrix.invertibleOfInvertibleMul

/-- A copy of `invertibleOfMulInvertible` using `⬝` not `*`. -/
@[reducible]
protected def invertibleOfMulInvertible (a b : Matrix n n α) [Invertible (a ⬝ b)] [Invertible b] :
    Invertible a :=
  { invertibleOfMulInvertible a b with invOf := b ⬝ ⅟ (a ⬝ b) }
#align matrix.invertible_of_mul_invertible Matrix.invertibleOfMulInvertible

end Matrix

/-- A copy of `Invertible.mulLeft` using `⬝` not `*`. -/
@[reducible]
def Invertible.matrixMulLeft {a : Matrix n n α} (_ : Invertible a) (b : Matrix n n α) :
    Invertible b ≃ Invertible (a ⬝ b) where
  toFun _ := Matrix.invertibleMul a b
  invFun _ := Matrix.invertibleOfInvertibleMul a _
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
#align invertible.matrix_mul_left Invertible.matrixMulLeft

/-- A copy of `Invertible.mulRight` using `⬝` not `*`. -/
@[reducible]
def Invertible.matrixMulRight (a : Matrix n n α) {b : Matrix n n α} (_ : Invertible b) :
    Invertible a ≃ Invertible (a ⬝ b) where
  toFun _ := Matrix.invertibleMul a b
  invFun _ := Matrix.invertibleOfMulInvertible _ b
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
#align invertible.matrix_mul_right Invertible.matrixMulRight
