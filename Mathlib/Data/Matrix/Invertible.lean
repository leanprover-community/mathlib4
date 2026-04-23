/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Ahmad Alkhalawi
-/
module

public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Group.Invertible.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.SetLike

/-! # Extra lemmas about invertible matrices

A few of the `Invertible` lemmas generalize to multiplication of rectangular matrices.

For lemmas about the matrix inverse in terms of the determinant and adjugate, see `Matrix.inv`
in `Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean`.

## Main results

* `Matrix.invertibleConjTranspose`
* `Matrix.invertibleTranspose`
* `Matrix.isUnit_conjTranspose`
* `Matrix.isUnit_transpose`
-/

@[expose] public section


open scoped Matrix

variable {m n : Type*} {α : Type*}
variable [Fintype n] [DecidableEq n]

namespace Matrix

section Semiring
variable [Semiring α]

/-- A copy of `invOf_mul_cancel_left` for rectangular matrices. -/
protected theorem invOf_mul_cancel_left (A : Matrix n n α) (B : Matrix n m α) [Invertible A] :
    ⅟A * (A * B) = B := by rw [← Matrix.mul_assoc, invOf_mul_self, Matrix.one_mul]

/-- A copy of `mul_invOf_cancel_left` for rectangular matrices. -/
protected theorem mul_invOf_cancel_left (A : Matrix n n α) (B : Matrix n m α) [Invertible A] :
    A * (⅟A * B) = B := by rw [← Matrix.mul_assoc, mul_invOf_self, Matrix.one_mul]

/-- A copy of `invOf_mul_cancel_right` for rectangular matrices. -/
protected theorem invOf_mul_cancel_right (A : Matrix m n α) (B : Matrix n n α) [Invertible B] :
    A * ⅟B * B = A := by rw [Matrix.mul_assoc, invOf_mul_self, Matrix.mul_one]

/-- A copy of `mul_invOf_cancel_right` for rectangular matrices. -/
protected theorem mul_invOf_cancel_right (A : Matrix m n α) (B : Matrix n n α) [Invertible B] :
    A * B * ⅟B = A := by rw [Matrix.mul_assoc, mul_invOf_self, Matrix.mul_one]

/-- A copy oy of `invOf_mul_eq_iff_eq_mul_left` for rectangular matrices. -/
protected theorem invOf_mul_eq_iff_eq_mul_left
    {A B : Matrix n m α} {C : Matrix n n α} [Invertible C] :
    ⅟C * A = B ↔ A = C * B := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← h, Matrix.mul_invOf_cancel_left]
  · rw [h, Matrix.invOf_mul_cancel_left]

/-- A copy oy of `mul_left_eq_iff_eq_invOf_mul` for rectangular matrices. -/
protected theorem mul_left_eq_iff_eq_invOf_mul
    {A B : Matrix n m α} {C : Matrix n n α} [Invertible C] :
    C * A = B ↔ A = ⅟C * B := by
  rw [eq_comm, ← Matrix.invOf_mul_eq_iff_eq_mul_left, eq_comm]

/-- A copy oy of `mul_invOf_eq_iff_eq_mul_right` for rectangular matrices. -/
protected theorem mul_invOf_eq_iff_eq_mul_right
    {A B : Matrix m n α} {C : Matrix n n α} [Invertible C] :
    A * ⅟C = B ↔ A = B * C := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← h, Matrix.invOf_mul_cancel_right]
  · rw [h, Matrix.mul_invOf_cancel_right]

/-- A copy oy of `mul_right_eq_iff_eq_mul_invOf` for rectangular matrices. -/
protected theorem mul_right_eq_iff_eq_mul_invOf
    {A B : Matrix m n α} {C : Matrix n n α} [Invertible C] :
    A * C = B ↔ A = B * ⅟C := by
  rw [eq_comm, ← Matrix.mul_invOf_eq_iff_eq_mul_right, eq_comm]

section ConjTranspose
variable [StarRing α] (A : Matrix n n α)

/-- The conjugate transpose of an invertible matrix is invertible. -/
instance invertibleConjTranspose [Invertible A] : Invertible Aᴴ := Invertible.star _

lemma conjTranspose_invOf [Invertible A] [Invertible Aᴴ] : (⅟A)ᴴ = ⅟(Aᴴ) := star_invOf _

/-- A matrix is invertible if the conjugate transpose is invertible. -/
@[implicit_reducible]
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
@[implicit_reducible]
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

section Ring

section Woodbury

variable [Fintype m] [DecidableEq m] [Ring α]
    (A : Matrix n n α) (U : Matrix n m α) (C : Matrix m m α) (V : Matrix m n α)
    [Invertible A] [Invertible C] [Invertible (⅟C + V * ⅟A * U)]

-- No spaces around multiplication signs for better clarity
set_option linter.style.whitespace false in
lemma add_mul_mul_invOf_mul_eq_one :
    (A + U*C*V)*(⅟A - ⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A) = 1 := by
  calc
    (A + U*C*V)*(⅟A - ⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A)
    _ = A*⅟A - A*⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A + U*C*V*⅟A - U*C*V*⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A := by
      simp_rw [add_sub_assoc, add_mul, mul_sub, Matrix.mul_assoc]
    _ = (1 + U*C*V*⅟A) - (U*⅟(⅟C + V*⅟A*U)*V*⅟A + U*C*V*⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A) := by
      rw [mul_invOf_self, Matrix.one_mul]
      abel
    _ = 1 + U*C*V*⅟A - (U + U*C*V*⅟A*U)*⅟(⅟C + V*⅟A*U)*V*⅟A := by
      rw [sub_right_inj, Matrix.add_mul, Matrix.add_mul, Matrix.add_mul]
    _ = 1 + U*C*V*⅟A - U*C*(⅟C + V*⅟A*U)*⅟(⅟C + V*⅟A*U)*V*⅟A := by
      congr
      simp only [Matrix.mul_add, Matrix.mul_invOf_cancel_right, ← Matrix.mul_assoc]
    _ = 1 := by
      rw [Matrix.mul_invOf_cancel_right]
      abel

-- No spaces around multiplication signs for better clarity
set_option linter.style.whitespace false in
/-- Like `add_mul_mul_invOf_mul_eq_one`, but with multiplication reversed. -/
lemma add_mul_mul_invOf_mul_eq_one' :
    (⅟A - ⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A)*(A + U*C*V) = 1 := by
  calc
    (⅟A - ⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A)*(A + U*C*V)
    _ = ⅟A*A - ⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A*A + ⅟A*U*C*V - ⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A*U*C*V := by
      simp_rw [add_sub_assoc, _root_.mul_add, _root_.sub_mul, Matrix.mul_assoc]
    _ = (1 + ⅟A*U*C*V) - (⅟A*U*⅟(⅟C + V*⅟A*U)*V + ⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A*U*C*V) := by
      rw [invOf_mul_self, Matrix.invOf_mul_cancel_right]
      abel
    _ = 1 + ⅟A*U*C*V - ⅟A*U*⅟(⅟C + V*⅟A*U)*(V + V*⅟A*U*C*V) := by
      rw [sub_right_inj, Matrix.mul_add]
      simp_rw [Matrix.mul_assoc]
    _ = 1 + ⅟A*U*C*V - ⅟A*U*⅟(⅟C + V*⅟A*U)*(⅟C + V*⅟A*U)*C*V := by
      simp only [Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc,
        Matrix.invOf_mul_cancel_right]
    _ = 1 := by
      rw [Matrix.invOf_mul_cancel_right]
      abel

/-- If matrices `A`, `C`, and `C⁻¹ + V * A⁻¹ * U` are invertible, then so is `A + U * C * V`. -/
@[implicit_reducible]
def invertibleAddMulMul : Invertible (A + U * C * V) where
  invOf := ⅟A - ⅟A * U * ⅟(⅟C + V * ⅟A * U) * V * ⅟A
  invOf_mul_self := add_mul_mul_invOf_mul_eq_one' _ _ _ _
  mul_invOf_self := add_mul_mul_invOf_mul_eq_one _ _ _ _

/-- The **Woodbury Identity** (`⅟` version).

See `Matrix.invOf_add_mul_mul'` for the Binomial Inverse Theorem. -/
theorem invOf_add_mul_mul [Invertible (A + U * C * V)] :
    ⅟(A + U * C * V) = ⅟A - ⅟A * U * ⅟(⅟C + V * ⅟A * U) * V * ⅟A := by
  letI := invertibleAddMulMul A U C V
  convert (rfl : ⅟(A + U * C * V) = _)

end Woodbury

section BinomialInverseTheorem

variable [Fintype m] [DecidableEq m] [Ring α]
    (A : Matrix n n α) (U : Matrix n m α) (C : Matrix m m α) (V : Matrix m n α)
    [Invertible A] [Invertible (C + C * V * ⅟A * U * C)]

lemma add_mul_mul_mul_invOf_eq_one :
    (A + U * C * V) * (⅟A - ⅟A * U * C * ⅟(C + C * V * ⅟A * U * C) * C * V * ⅟A) = 1 := by
  simp only [Matrix.mul_sub, Matrix.add_mul, mul_invOf_self']
  rw [add_sub_assoc, add_eq_left, sub_eq_zero]
  simp only [← Matrix.mul_assoc, mul_invOf_self', Matrix.one_mul]
  simp only [← Matrix.add_mul]
  congr
  rw [← Matrix.mul_right_eq_iff_eq_mul_invOf]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]

lemma add_mul_mul_mul_invOf_eq_one' :
    (⅟A - ⅟A * U * C * ⅟(C + C * V * ⅟A * U * C) * C * V * ⅟A) * (A + U * C * V) = 1 := by
  simp only [Matrix.mul_add, Matrix.sub_mul, invOf_mul_self']
  rw [sub_add, sub_eq_self, sub_eq_zero]
  simp only [Matrix.mul_assoc, ← Matrix.mul_sub]
  congr
  rw [eq_sub_iff_add_eq, ← Matrix.mul_add]
  rw [Matrix.invOf_mul_eq_iff_eq_mul_left]
  simp only [Matrix.add_mul, invOf_mul_self', Matrix.mul_one, add_right_inj]
  simp only [Matrix.mul_assoc]

/-- If matrices `A` and `C + C * V * A⁻¹ * U * C` are invertible, then so is `A + U * C * V`. -/
@[implicit_reducible]
def invertibleAddMulMul' : Invertible (A + U * C * V) where
  invOf := ⅟A - ⅟A * U * C * ⅟(C + C * V * ⅟A * U * C) * C * V * ⅟A
  invOf_mul_self := add_mul_mul_mul_invOf_eq_one' A U C V
  mul_invOf_self := add_mul_mul_mul_invOf_eq_one A U C V

/-- The **Binomial Inverse Theorem** (`⅟` version).

See `Matrix.invOf_add_mul_mul` for the Woodbury identity. -/
theorem invOf_add_mul_mul' [Invertible (A + U * C * V)] :
    ⅟(A + U * C * V) = ⅟A - ⅟A * U * C * ⅟(C + C * V * ⅟A * U * C) * C * V * ⅟A := by
  letI := invertibleAddMulMul' A U C V
  convert (rfl : ⅟(A + U * C * V) = _)

end BinomialInverseTheorem

end Ring

end Matrix
