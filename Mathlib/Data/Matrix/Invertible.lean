/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Data.Matrix.Basic

/-! # Extra lemmas about invertible matrices

A few of the `Invertible` lemmas generalize to multiplication of rectangular matrices.

For lemmas about the matrix inverse in terms of the determinant and adjugate, see `Matrix.inv`
in `LinearAlgebra/Matrix/NonsingularInverse.lean`.

## Main results

* `Matrix.invertibleConjTranspose`
* `Matrix.invertibleTranspose`
* `Matrix.isUnit_conjTranpose`
* `Matrix.isUnit_tranpose`
-/


open scoped Matrix

variable {m n : Type*} {α : Type*}
variable [Fintype n] [DecidableEq n]

namespace Matrix

section Semiring
variable [Semiring α]

/-- A copy of `invOf_mul_cancel_left` for rectangular matrices. -/
protected theorem invOf_mul_cancel_left (A : Matrix n n α) (B : Matrix n m α) [Invertible A] :
    ⅟ A * (A * B) = B := by rw [← Matrix.mul_assoc, invOf_mul_self, Matrix.one_mul]

/-- A copy of `mul_invOf_cancel_left` for rectangular matrices. -/
protected theorem mul_invOf_cancel_left (A : Matrix n n α) (B : Matrix n m α) [Invertible A] :
    A * (⅟ A * B) = B := by rw [← Matrix.mul_assoc, mul_invOf_self, Matrix.one_mul]

/-- A copy of `invOf_mul_cancel_right` for rectangular matrices. -/
protected theorem invOf_mul_cancel_right (A : Matrix m n α) (B : Matrix n n α) [Invertible B] :
    A * ⅟ B * B = A := by rw [Matrix.mul_assoc, invOf_mul_self, Matrix.mul_one]

/-- A copy of `mul_invOf_cancel_right` for rectangular matrices. -/
protected theorem mul_invOf_cancel_right (A : Matrix m n α) (B : Matrix n n α) [Invertible B] :
    A * B * ⅟ B = A := by rw [Matrix.mul_assoc, mul_invOf_self, Matrix.mul_one]

@[deprecated (since := "2024-09-07")] alias invOf_mul_self_assoc := invOf_mul_cancel_left
@[deprecated (since := "2024-09-07")] alias mul_invOf_self_assoc := mul_invOf_cancel_left
@[deprecated (since := "2024-09-07")] alias mul_invOf_mul_self_cancel := invOf_mul_cancel_right
@[deprecated (since := "2024-09-07")] alias mul_mul_invOf_self_cancel := mul_invOf_cancel_right

section ConjTranspose
variable [StarRing α] (A : Matrix n n α)

/-- The conjugate transpose of an invertible matrix is invertible. -/
instance invertibleConjTranspose [Invertible A] : Invertible Aᴴ := Invertible.star _

lemma conjTranspose_invOf [Invertible A] [Invertible Aᴴ] : (⅟A)ᴴ = ⅟(Aᴴ) := star_invOf _

/-- A matrix is invertible if the conjugate transpose is invertible. -/
def invertibleOfInvertibleConjTranspose [Invertible Aᴴ] : Invertible A := by
  rw [← conjTranspose_conjTranspose A, ← star_eq_conjTranspose]
  infer_instance

@[simp] lemma isUnit_conjTranspose : IsUnit Aᴴ ↔ IsUnit A := isUnit_star

end ConjTranspose

end Semiring

section CommSemiring

variable [CommSemiring α] (A : Matrix n n α)

/-- The transpose of an invertible matrix is invertible. -/
instance invertibleTranspose [Invertible A] : Invertible Aᵀ where
  invOf := (⅟A)ᵀ
  invOf_mul_self := by rw [← transpose_mul, mul_invOf_self, transpose_one]
  mul_invOf_self := by rw [← transpose_mul, invOf_mul_self, transpose_one]

lemma transpose_invOf [Invertible A] [Invertible Aᵀ] : (⅟A)ᵀ = ⅟(Aᵀ) := by
  letI := invertibleTranspose A
  convert (rfl : _ = ⅟(Aᵀ))

/-- `Aᵀ` is invertible when `A` is. -/
def invertibleOfInvertibleTranspose [Invertible Aᵀ] : Invertible A where
  invOf := (⅟(Aᵀ))ᵀ
  invOf_mul_self := by rw [← transpose_one, ← mul_invOf_self Aᵀ, transpose_mul, transpose_transpose]
  mul_invOf_self := by rw [← transpose_one, ← invOf_mul_self Aᵀ, transpose_mul, transpose_transpose]

/-- Together `Matrix.invertibleTranspose` and `Matrix.invertibleOfInvertibleTranspose` form an
equivalence, although both sides of the equiv are subsingleton anyway. -/
@[simps]
def transposeInvertibleEquivInvertible : Invertible Aᵀ ≃ Invertible A where
  toFun := @invertibleOfInvertibleTranspose _ _ _ _ _ _
  invFun := @invertibleTranspose _ _ _ _ _ _
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

@[simp] lemma isUnit_transpose : IsUnit Aᵀ ↔ IsUnit A := by
  simp only [← nonempty_invertible_iff_isUnit,
    (transposeInvertibleEquivInvertible A).nonempty_congr]

end CommSemiring

end Matrix
