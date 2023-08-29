/-
Copyright (c) 2019 Tim Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baanen, Lu-Ming Zhang
-/
import Mathlib.Data.Matrix.Invertible
import Mathlib.LinearAlgebra.Matrix.Adjugate

#align_import linear_algebra.matrix.nonsingular_inverse from "leanprover-community/mathlib"@"722b3b152ddd5e0cf21c0a29787c76596cb6b422"

/-!
# Nonsingular inverses

In this file, we define an inverse for square matrices of invertible determinant.

For matrices that are not square or not of full rank, there is a more general notion of
pseudoinverses which we do not consider here.

The definition of inverse used in this file is the adjugate divided by the determinant.
We show that dividing the adjugate by `det A` (if possible), giving a matrix `A⁻¹` (`nonsing_inv`),
will result in a multiplicative inverse to `A`.

Note that there are at least three different inverses in mathlib:

* `A⁻¹` (`Inv.inv`): alone, this satisfies no properties, although it is usually used in
  conjunction with `Group` or `GroupWithZero`. On matrices, this is defined to be zero when no
  inverse exists.
* `⅟A` (`invOf`): this is only available in the presence of `[Invertible A]`, which guarantees an
  inverse exists.
* `Ring.inverse A`: this is defined on any `MonoidWithZero`, and just like `⁻¹` on matrices, is
  defined to be zero when no inverse exists.

We start by working with `Invertible`, and show the main results:

* `Matrix.invertibleOfDetInvertible`
* `Matrix.detInvertibleOfInvertible`
* `Matrix.isUnit_iff_isUnit_det`
* `Matrix.mul_eq_one_comm`

After this we define `Matrix.inv` and show it matches `⅟A` and `Ring.inverse A`.
The rest of the results in the file are then about `A⁻¹`

## References

  * https://en.wikipedia.org/wiki/Cramer's_rule#Finding_inverse_matrix

## Tags

matrix inverse, cramer, cramer's rule, adjugate
-/


namespace Matrix

universe u u' v

variable {l : Type*} {m : Type u} {n : Type u'} {α : Type v}

open Matrix BigOperators Equiv Equiv.Perm Finset

/-! ### Matrices are `Invertible` iff their determinants are -/


section Invertible

variable [Fintype n] [DecidableEq n] [CommRing α]

variable (A : Matrix n n α) (B : Matrix n n α)

/-- If `A.det` has a constructive inverse, produce one for `A`. -/
def invertibleOfDetInvertible [Invertible A.det] : Invertible A where
  invOf := ⅟ A.det • A.adjugate
  mul_invOf_self := by
    rw [mul_smul_comm, mul_adjugate, smul_smul, invOf_mul_self, one_smul]
    -- 🎉 no goals
  invOf_mul_self := by
    -- 🎉 no goals
    rw [smul_mul_assoc, adjugate_mul, smul_smul, invOf_mul_self, one_smul]
#align matrix.invertible_of_det_invertible Matrix.invertibleOfDetInvertible

theorem invOf_eq [Invertible A.det] [Invertible A] : ⅟ A = ⅟ A.det • A.adjugate := by
  letI := invertibleOfDetInvertible A
  -- ⊢ ⅟A = ⅟(det A) • adjugate A
  convert(rfl : ⅟ A = _)
  -- 🎉 no goals
#align matrix.inv_of_eq Matrix.invOf_eq

/-- `A.det` is invertible if `A` has a left inverse. -/
def detInvertibleOfLeftInverse (h : B * A = 1) : Invertible A.det where
  invOf := B.det
  mul_invOf_self := by rw [mul_comm, ← det_mul, h, det_one]
                       -- 🎉 no goals
                       -- 🎉 no goals
  invOf_mul_self := by rw [← det_mul, h, det_one]
#align matrix.det_invertible_of_left_inverse Matrix.detInvertibleOfLeftInverse

/-- `A.det` is invertible if `A` has a right inverse. -/
def detInvertibleOfRightInverse (h : A * B = 1) : Invertible A.det where
  invOf := B.det
  mul_invOf_self := by rw [← det_mul, h, det_one]
                       -- 🎉 no goals
                       -- 🎉 no goals
  invOf_mul_self := by rw [mul_comm, ← det_mul, h, det_one]
#align matrix.det_invertible_of_right_inverse Matrix.detInvertibleOfRightInverse

/-- If `A` has a constructive inverse, produce one for `A.det`. -/
def detInvertibleOfInvertible [Invertible A] : Invertible A.det :=
  detInvertibleOfLeftInverse A (⅟ A) (invOf_mul_self _)
#align matrix.det_invertible_of_invertible Matrix.detInvertibleOfInvertible

theorem det_invOf [Invertible A] [Invertible A.det] : (⅟ A).det = ⅟ A.det := by
  letI := detInvertibleOfInvertible A
  -- ⊢ det ⅟A = ⅟(det A)
  convert(rfl : _ = ⅟ A.det)
  -- 🎉 no goals
#align matrix.det_inv_of Matrix.det_invOf

/-- Together `Matrix.detInvertibleOfInvertible` and `Matrix.invertibleOfDetInvertible` form an
equivalence, although both sides of the equiv are subsingleton anyway. -/
@[simps]
def invertibleEquivDetInvertible : Invertible A ≃ Invertible A.det where
  toFun := @detInvertibleOfInvertible _ _ _ _ _ A
  invFun := @invertibleOfDetInvertible _ _ _ _ _ A
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
#align matrix.invertible_equiv_det_invertible Matrix.invertibleEquivDetInvertible

variable {A B}

theorem mul_eq_one_comm : A * B = 1 ↔ B * A = 1 :=
  suffices ∀ A B, A * B = 1 → B * A = 1 from ⟨this A B, this B A⟩
  fun A B h => by
  letI : Invertible B.det := detInvertibleOfLeftInverse _ _ h
  -- ⊢ B * A = 1
  letI : Invertible B := invertibleOfDetInvertible B
  -- ⊢ B * A = 1
  calc
    B * A = B * A * (B * ⅟ B) := by rw [mul_invOf_self, Matrix.mul_one]
    _ = B * (A * B * ⅟ B) := by simp only [Matrix.mul_assoc]
    _ = B * ⅟ B := by rw [h, Matrix.one_mul]
    _ = 1 := mul_invOf_self B

#align matrix.mul_eq_one_comm Matrix.mul_eq_one_comm

variable (A B)

/-- We can construct an instance of invertible A if A has a left inverse. -/
def invertibleOfLeftInverse (h : B * A = 1) : Invertible A :=
  ⟨B, h, mul_eq_one_comm.mp h⟩
#align matrix.invertible_of_left_inverse Matrix.invertibleOfLeftInverse

/-- We can construct an instance of invertible A if A has a right inverse. -/
def invertibleOfRightInverse (h : A * B = 1) : Invertible A :=
  ⟨B, mul_eq_one_comm.mp h, h⟩
#align matrix.invertible_of_right_inverse Matrix.invertibleOfRightInverse

/-- Given a proof that `A.det` has a constructive inverse, lift `A` to `(Matrix n n α)ˣ`-/
def unitOfDetInvertible [Invertible A.det] : (Matrix n n α)ˣ :=
  @unitOfInvertible _ _ A (invertibleOfDetInvertible A)
#align matrix.unit_of_det_invertible Matrix.unitOfDetInvertible

/-- When lowered to a prop, `Matrix.invertibleEquivDetInvertible` forms an `iff`. -/
theorem isUnit_iff_isUnit_det : IsUnit A ↔ IsUnit A.det := by
  simp only [← nonempty_invertible_iff_isUnit, (invertibleEquivDetInvertible A).nonempty_congr]
  -- 🎉 no goals
#align matrix.is_unit_iff_is_unit_det Matrix.isUnit_iff_isUnit_det

/-! #### Variants of the statements above with `IsUnit`-/


theorem isUnit_det_of_invertible [Invertible A] : IsUnit A.det :=
  @isUnit_of_invertible _ _ _ (detInvertibleOfInvertible A)
#align matrix.is_unit_det_of_invertible Matrix.isUnit_det_of_invertible

variable {A B}

theorem isUnit_of_left_inverse (h : B * A = 1) : IsUnit A :=
  ⟨⟨A, B, mul_eq_one_comm.mp h, h⟩, rfl⟩
#align matrix.is_unit_of_left_inverse Matrix.isUnit_of_left_inverse

theorem isUnit_of_right_inverse (h : A * B = 1) : IsUnit A :=
  ⟨⟨A, B, h, mul_eq_one_comm.mp h⟩, rfl⟩
#align matrix.is_unit_of_right_inverse Matrix.isUnit_of_right_inverse

theorem isUnit_det_of_left_inverse (h : B * A = 1) : IsUnit A.det :=
  @isUnit_of_invertible _ _ _ (detInvertibleOfLeftInverse _ _ h)
#align matrix.is_unit_det_of_left_inverse Matrix.isUnit_det_of_left_inverse

theorem isUnit_det_of_right_inverse (h : A * B = 1) : IsUnit A.det :=
  @isUnit_of_invertible _ _ _ (detInvertibleOfRightInverse _ _ h)
#align matrix.is_unit_det_of_right_inverse Matrix.isUnit_det_of_right_inverse

theorem det_ne_zero_of_left_inverse [Nontrivial α] (h : B * A = 1) : A.det ≠ 0 :=
  (isUnit_det_of_left_inverse h).ne_zero
#align matrix.det_ne_zero_of_left_inverse Matrix.det_ne_zero_of_left_inverse

theorem det_ne_zero_of_right_inverse [Nontrivial α] (h : A * B = 1) : A.det ≠ 0 :=
  (isUnit_det_of_right_inverse h).ne_zero
#align matrix.det_ne_zero_of_right_inverse Matrix.det_ne_zero_of_right_inverse

end Invertible

variable [Fintype n] [DecidableEq n] [CommRing α]

variable (A : Matrix n n α) (B : Matrix n n α)

theorem isUnit_det_transpose (h : IsUnit A.det) : IsUnit Aᵀ.det := by
  rw [det_transpose]
  -- ⊢ IsUnit (det A)
  exact h
  -- 🎉 no goals
#align matrix.is_unit_det_transpose Matrix.isUnit_det_transpose

/-! ### A noncomputable `Inv` instance  -/


/-- The inverse of a square matrix, when it is invertible (and zero otherwise).-/
noncomputable instance inv : Inv (Matrix n n α) :=
  ⟨fun A => Ring.inverse A.det • A.adjugate⟩

theorem inv_def (A : Matrix n n α) : A⁻¹ = Ring.inverse A.det • A.adjugate :=
  rfl
#align matrix.inv_def Matrix.inv_def

theorem nonsing_inv_apply_not_isUnit (h : ¬IsUnit A.det) : A⁻¹ = 0 := by
  rw [inv_def, Ring.inverse_non_unit _ h, zero_smul]
  -- 🎉 no goals
#align matrix.nonsing_inv_apply_not_is_unit Matrix.nonsing_inv_apply_not_isUnit

theorem nonsing_inv_apply (h : IsUnit A.det) : A⁻¹ = (↑h.unit⁻¹ : α) • A.adjugate := by
  rw [inv_def, ← Ring.inverse_unit h.unit, IsUnit.unit_spec]
  -- 🎉 no goals
#align matrix.nonsing_inv_apply Matrix.nonsing_inv_apply

/-- The nonsingular inverse is the same as `invOf` when `A` is invertible. -/
@[simp]
theorem invOf_eq_nonsing_inv [Invertible A] : ⅟ A = A⁻¹ := by
  letI := detInvertibleOfInvertible A
  -- ⊢ ⅟A = A⁻¹
  rw [inv_def, Ring.inverse_invertible, invOf_eq]
  -- 🎉 no goals
#align matrix.inv_of_eq_nonsing_inv Matrix.invOf_eq_nonsing_inv

/-- Coercing the result of `Units.instInv` is the same as coercing first and applying the
nonsingular inverse. -/
@[simp, norm_cast]
theorem coe_units_inv (A : (Matrix n n α)ˣ) : ↑A⁻¹ = (A⁻¹ : Matrix n n α) := by
  letI := A.invertible
  -- ⊢ ↑A⁻¹ = (↑A)⁻¹
  rw [← invOf_eq_nonsing_inv, invOf_units]
  -- 🎉 no goals
#align matrix.coe_units_inv Matrix.coe_units_inv

/-- The nonsingular inverse is the same as the general `Ring.inverse`. -/
theorem nonsing_inv_eq_ring_inverse : A⁻¹ = Ring.inverse A := by
  by_cases h_det : IsUnit A.det
  -- ⊢ A⁻¹ = Ring.inverse A
  · cases (A.isUnit_iff_isUnit_det.mpr h_det).nonempty_invertible
    -- ⊢ A⁻¹ = Ring.inverse A
    rw [← invOf_eq_nonsing_inv, Ring.inverse_invertible]
    -- 🎉 no goals
  · have h := mt A.isUnit_iff_isUnit_det.mp h_det
    -- ⊢ A⁻¹ = Ring.inverse A
    rw [Ring.inverse_non_unit _ h, nonsing_inv_apply_not_isUnit A h_det]
    -- 🎉 no goals
#align matrix.nonsing_inv_eq_ring_inverse Matrix.nonsing_inv_eq_ring_inverse

theorem transpose_nonsing_inv : A⁻¹ᵀ = Aᵀ⁻¹ := by
  rw [inv_def, inv_def, transpose_smul, det_transpose, adjugate_transpose]
  -- 🎉 no goals
#align matrix.transpose_nonsing_inv Matrix.transpose_nonsing_inv

theorem conjTranspose_nonsing_inv [StarRing α] : A⁻¹ᴴ = Aᴴ⁻¹ := by
  rw [inv_def, inv_def, conjTranspose_smul, det_conjTranspose, adjugate_conjTranspose,
    Ring.inverse_star]
#align matrix.conj_transpose_nonsing_inv Matrix.conjTranspose_nonsing_inv

/-- The `nonsing_inv` of `A` is a right inverse. -/
@[simp]
theorem mul_nonsing_inv (h : IsUnit A.det) : A * A⁻¹ = 1 := by
  cases (A.isUnit_iff_isUnit_det.mpr h).nonempty_invertible
  -- ⊢ A * A⁻¹ = 1
  rw [← invOf_eq_nonsing_inv, mul_invOf_self]
  -- 🎉 no goals
#align matrix.mul_nonsing_inv Matrix.mul_nonsing_inv

/-- The `nonsing_inv` of `A` is a left inverse. -/
@[simp]
theorem nonsing_inv_mul (h : IsUnit A.det) : A⁻¹ * A = 1 := by
  cases (A.isUnit_iff_isUnit_det.mpr h).nonempty_invertible
  -- ⊢ A⁻¹ * A = 1
  rw [← invOf_eq_nonsing_inv, invOf_mul_self]
  -- 🎉 no goals
#align matrix.nonsing_inv_mul Matrix.nonsing_inv_mul

instance [Invertible A] : Invertible A⁻¹ := by
  rw [← invOf_eq_nonsing_inv]
  -- ⊢ Invertible ⅟A
  infer_instance
  -- 🎉 no goals

@[simp]
theorem inv_inv_of_invertible [Invertible A] : A⁻¹⁻¹ = A := by
  simp only [← invOf_eq_nonsing_inv, invOf_invOf]
  -- 🎉 no goals
#align matrix.inv_inv_of_invertible Matrix.inv_inv_of_invertible

@[simp]
theorem mul_nonsing_inv_cancel_right (B : Matrix m n α) (h : IsUnit A.det) : B * A * A⁻¹ = B := by
  simp [Matrix.mul_assoc, mul_nonsing_inv A h]
  -- 🎉 no goals
#align matrix.mul_nonsing_inv_cancel_right Matrix.mul_nonsing_inv_cancel_right

@[simp]
theorem mul_nonsing_inv_cancel_left (B : Matrix n m α) (h : IsUnit A.det) : A * (A⁻¹ * B) = B := by
  simp [← Matrix.mul_assoc, mul_nonsing_inv A h]
  -- 🎉 no goals
#align matrix.mul_nonsing_inv_cancel_left Matrix.mul_nonsing_inv_cancel_left

@[simp]
theorem nonsing_inv_mul_cancel_right (B : Matrix m n α) (h : IsUnit A.det) : B * A⁻¹ * A = B := by
  simp [Matrix.mul_assoc, nonsing_inv_mul A h]
  -- 🎉 no goals
#align matrix.nonsing_inv_mul_cancel_right Matrix.nonsing_inv_mul_cancel_right

@[simp]
theorem nonsing_inv_mul_cancel_left (B : Matrix n m α) (h : IsUnit A.det) : A⁻¹ * (A * B) = B := by
  simp [← Matrix.mul_assoc, nonsing_inv_mul A h]
  -- 🎉 no goals
#align matrix.nonsing_inv_mul_cancel_left Matrix.nonsing_inv_mul_cancel_left

@[simp]
theorem mul_inv_of_invertible [Invertible A] : A * A⁻¹ = 1 :=
  mul_nonsing_inv A (isUnit_det_of_invertible A)
#align matrix.mul_inv_of_invertible Matrix.mul_inv_of_invertible

@[simp]
theorem inv_mul_of_invertible [Invertible A] : A⁻¹ * A = 1 :=
  nonsing_inv_mul A (isUnit_det_of_invertible A)
#align matrix.inv_mul_of_invertible Matrix.inv_mul_of_invertible

@[simp]
theorem mul_inv_cancel_right_of_invertible (B : Matrix m n α) [Invertible A] : B * A * A⁻¹ = B :=
  mul_nonsing_inv_cancel_right A B (isUnit_det_of_invertible A)
#align matrix.mul_inv_cancel_right_of_invertible Matrix.mul_inv_cancel_right_of_invertible

@[simp]
theorem mul_inv_cancel_left_of_invertible (B : Matrix n m α) [Invertible A] : A * (A⁻¹ * B) = B :=
  mul_nonsing_inv_cancel_left A B (isUnit_det_of_invertible A)
#align matrix.mul_inv_cancel_left_of_invertible Matrix.mul_inv_cancel_left_of_invertible

@[simp]
theorem inv_mul_cancel_right_of_invertible (B : Matrix m n α) [Invertible A] : B * A⁻¹ * A = B :=
  nonsing_inv_mul_cancel_right A B (isUnit_det_of_invertible A)
#align matrix.inv_mul_cancel_right_of_invertible Matrix.inv_mul_cancel_right_of_invertible

@[simp]
theorem inv_mul_cancel_left_of_invertible (B : Matrix n m α) [Invertible A] : A⁻¹ * (A * B) = B :=
  nonsing_inv_mul_cancel_left A B (isUnit_det_of_invertible A)
#align matrix.inv_mul_cancel_left_of_invertible Matrix.inv_mul_cancel_left_of_invertible

theorem inv_mul_eq_iff_eq_mul_of_invertible (A B C : Matrix n n α) [Invertible A] :
    A⁻¹ * B = C ↔ B = A * C :=
  ⟨fun h => by rw [← h, mul_inv_cancel_left_of_invertible],
               -- 🎉 no goals
   fun h => by rw [h, inv_mul_cancel_left_of_invertible]⟩
               -- 🎉 no goals
#align matrix.inv_mul_eq_iff_eq_mul_of_invertible Matrix.inv_mul_eq_iff_eq_mul_of_invertible

theorem mul_inv_eq_iff_eq_mul_of_invertible (A B C : Matrix n n α) [Invertible A] :
    B * A⁻¹ = C ↔ B = C * A :=
  ⟨fun h => by rw [← h, inv_mul_cancel_right_of_invertible],
               -- 🎉 no goals
   fun h => by rw [h, mul_inv_cancel_right_of_invertible]⟩
               -- 🎉 no goals
#align matrix.mul_inv_eq_iff_eq_mul_of_invertible Matrix.mul_inv_eq_iff_eq_mul_of_invertible

lemma mul_right_injective_of_invertible [Invertible A] :
    Function.Injective (fun (x : Matrix n m α) => A * x) :=
  fun _ _ h => by simpa only [inv_mul_cancel_left_of_invertible] using congr_arg (A⁻¹ * ·) h
                  -- 🎉 no goals

lemma mul_left_injective_of_invertible [Invertible A] :
    Function.Injective (fun (x : Matrix m n α) => x * A) :=
  fun a x hax => by simpa only [mul_inv_cancel_right_of_invertible] using congr_arg (· * A⁻¹) hax
                    -- 🎉 no goals

lemma mul_right_inj_of_invertible [Invertible A] {x y : Matrix n m α} : A * x = A * y ↔ x = y :=
  (mul_right_injective_of_invertible A).eq_iff

lemma mul_left_inj_of_invertible [Invertible A] {x y : Matrix m n α} : x * A = y * A ↔ x = y :=
  (mul_left_injective_of_invertible A).eq_iff

theorem nonsing_inv_cancel_or_zero : A⁻¹ * A = 1 ∧ A * A⁻¹ = 1 ∨ A⁻¹ = 0 := by
  by_cases h : IsUnit A.det
  -- ⊢ A⁻¹ * A = 1 ∧ A * A⁻¹ = 1 ∨ A⁻¹ = 0
  · exact Or.inl ⟨nonsing_inv_mul _ h, mul_nonsing_inv _ h⟩
    -- 🎉 no goals
  · exact Or.inr (nonsing_inv_apply_not_isUnit _ h)
    -- 🎉 no goals
#align matrix.nonsing_inv_cancel_or_zero Matrix.nonsing_inv_cancel_or_zero

theorem det_nonsing_inv_mul_det (h : IsUnit A.det) : A⁻¹.det * A.det = 1 := by
  rw [← det_mul, A.nonsing_inv_mul h, det_one]
  -- 🎉 no goals
#align matrix.det_nonsing_inv_mul_det Matrix.det_nonsing_inv_mul_det

@[simp]
theorem det_nonsing_inv : A⁻¹.det = Ring.inverse A.det := by
  by_cases h : IsUnit A.det
  -- ⊢ det A⁻¹ = Ring.inverse (det A)
  · cases h.nonempty_invertible
    -- ⊢ det A⁻¹ = Ring.inverse (det A)
    letI := invertibleOfDetInvertible A
    -- ⊢ det A⁻¹ = Ring.inverse (det A)
    rw [Ring.inverse_invertible, ← invOf_eq_nonsing_inv, det_invOf]
    -- 🎉 no goals
  cases isEmpty_or_nonempty n
  -- ⊢ det A⁻¹ = Ring.inverse (det A)
  · rw [det_isEmpty, det_isEmpty, Ring.inverse_one]
    -- 🎉 no goals
  · rw [Ring.inverse_non_unit _ h, nonsing_inv_apply_not_isUnit _ h, det_zero ‹_›]
    -- 🎉 no goals
#align matrix.det_nonsing_inv Matrix.det_nonsing_inv

theorem isUnit_nonsing_inv_det (h : IsUnit A.det) : IsUnit A⁻¹.det :=
  isUnit_of_mul_eq_one _ _ (A.det_nonsing_inv_mul_det h)
#align matrix.is_unit_nonsing_inv_det Matrix.isUnit_nonsing_inv_det

@[simp]
theorem nonsing_inv_nonsing_inv (h : IsUnit A.det) : A⁻¹⁻¹ = A :=
  calc
    A⁻¹⁻¹ = 1 * A⁻¹⁻¹ := by rw [Matrix.one_mul]
                            -- 🎉 no goals
    _ = A * A⁻¹ * A⁻¹⁻¹ := by rw [A.mul_nonsing_inv h]
                              -- 🎉 no goals
    _ = A := by
      rw [Matrix.mul_assoc, A⁻¹.mul_nonsing_inv (A.isUnit_nonsing_inv_det h), Matrix.mul_one]
      -- 🎉 no goals

#align matrix.nonsing_inv_nonsing_inv Matrix.nonsing_inv_nonsing_inv

theorem isUnit_nonsing_inv_det_iff {A : Matrix n n α} : IsUnit A⁻¹.det ↔ IsUnit A.det := by
  rw [Matrix.det_nonsing_inv, isUnit_ring_inverse]
  -- 🎉 no goals
#align matrix.is_unit_nonsing_inv_det_iff Matrix.isUnit_nonsing_inv_det_iff

-- `IsUnit.invertible` lifts the proposition `IsUnit A` to a constructive inverse of `A`.
/-- A version of `Matrix.invertibleOfDetInvertible` with the inverse defeq to `A⁻¹` that is
therefore noncomputable. -/
noncomputable def invertibleOfIsUnitDet (h : IsUnit A.det) : Invertible A :=
  ⟨A⁻¹, nonsing_inv_mul A h, mul_nonsing_inv A h⟩
#align matrix.invertible_of_is_unit_det Matrix.invertibleOfIsUnitDet

/-- A version of `Matrix.unitOfDetInvertible` with the inverse defeq to `A⁻¹` that is therefore
noncomputable. -/
noncomputable def nonsingInvUnit (h : IsUnit A.det) : (Matrix n n α)ˣ :=
  @unitOfInvertible _ _ _ (invertibleOfIsUnitDet A h)
#align matrix.nonsing_inv_unit Matrix.nonsingInvUnit

theorem unitOfDetInvertible_eq_nonsingInvUnit [Invertible A.det] :
    unitOfDetInvertible A = nonsingInvUnit A (isUnit_of_invertible _) := by
  ext
  -- ⊢ ↑(unitOfDetInvertible A) i✝ x✝ = ↑(nonsingInvUnit A (_ : IsUnit (det A))) i✝ …
  rfl
  -- 🎉 no goals
#align matrix.unit_of_det_invertible_eq_nonsing_inv_unit Matrix.unitOfDetInvertible_eq_nonsingInvUnit

variable {A} {B}

/-- If matrix A is left invertible, then its inverse equals its left inverse. -/
theorem inv_eq_left_inv (h : B * A = 1) : A⁻¹ = B :=
  letI := invertibleOfLeftInverse _ _ h
  invOf_eq_nonsing_inv A ▸ invOf_eq_left_inv h
#align matrix.inv_eq_left_inv Matrix.inv_eq_left_inv

/-- If matrix A is right invertible, then its inverse equals its right inverse. -/
theorem inv_eq_right_inv (h : A * B = 1) : A⁻¹ = B :=
  inv_eq_left_inv (mul_eq_one_comm.2 h)
#align matrix.inv_eq_right_inv Matrix.inv_eq_right_inv

section InvEqInv

variable {C : Matrix n n α}

/-- The left inverse of matrix A is unique when existing. -/
theorem left_inv_eq_left_inv (h : B * A = 1) (g : C * A = 1) : B = C := by
  rw [← inv_eq_left_inv h, ← inv_eq_left_inv g]
  -- 🎉 no goals
#align matrix.left_inv_eq_left_inv Matrix.left_inv_eq_left_inv

/-- The right inverse of matrix A is unique when existing. -/
theorem right_inv_eq_right_inv (h : A * B = 1) (g : A * C = 1) : B = C := by
  rw [← inv_eq_right_inv h, ← inv_eq_right_inv g]
  -- 🎉 no goals
#align matrix.right_inv_eq_right_inv Matrix.right_inv_eq_right_inv

/-- The right inverse of matrix A equals the left inverse of A when they exist. -/
theorem right_inv_eq_left_inv (h : A * B = 1) (g : C * A = 1) : B = C := by
  rw [← inv_eq_right_inv h, ← inv_eq_left_inv g]
  -- 🎉 no goals
#align matrix.right_inv_eq_left_inv Matrix.right_inv_eq_left_inv

theorem inv_inj (h : A⁻¹ = B⁻¹) (h' : IsUnit A.det) : A = B := by
  refine' left_inv_eq_left_inv (mul_nonsing_inv _ h') _
  -- ⊢ B * A⁻¹ = 1
  rw [h]
  -- ⊢ B * B⁻¹ = 1
  refine' mul_nonsing_inv _ _
  -- ⊢ IsUnit (det B)
  rwa [← isUnit_nonsing_inv_det_iff, ← h, isUnit_nonsing_inv_det_iff]
  -- 🎉 no goals
#align matrix.inv_inj Matrix.inv_inj

end InvEqInv

variable (A)

@[simp]
theorem inv_zero : (0 : Matrix n n α)⁻¹ = 0 := by
  cases' subsingleton_or_nontrivial α with ht ht
  -- ⊢ 0⁻¹ = 0
  · simp
    -- 🎉 no goals
  cases' (Fintype.card n).zero_le.eq_or_lt with hc hc
  -- ⊢ 0⁻¹ = 0
  · rw [eq_comm, Fintype.card_eq_zero_iff] at hc
    -- ⊢ 0⁻¹ = 0
    haveI := hc
    -- ⊢ 0⁻¹ = 0
    ext i
    -- ⊢ 0⁻¹ i x✝ = OfNat.ofNat 0 i x✝
    exact (IsEmpty.false i).elim
    -- 🎉 no goals
  · have hn : Nonempty n := Fintype.card_pos_iff.mp hc
    -- ⊢ 0⁻¹ = 0
    refine' nonsing_inv_apply_not_isUnit _ _
    -- ⊢ ¬IsUnit (det 0)
    simp [hn]
    -- 🎉 no goals
#align matrix.inv_zero Matrix.inv_zero

noncomputable instance : InvOneClass (Matrix n n α) :=
  { Matrix.one, Matrix.inv with inv_one := inv_eq_left_inv (by simp) }
                                                               -- 🎉 no goals

theorem inv_smul (k : α) [Invertible k] (h : IsUnit A.det) : (k • A)⁻¹ = ⅟ k • A⁻¹ :=
  inv_eq_left_inv (by simp [h, smul_smul])
                      -- 🎉 no goals
#align matrix.inv_smul Matrix.inv_smul

theorem inv_smul' (k : αˣ) (h : IsUnit A.det) : (k • A)⁻¹ = k⁻¹ • A⁻¹ :=
  inv_eq_left_inv (by simp [h, smul_smul])
                      -- 🎉 no goals
#align matrix.inv_smul' Matrix.inv_smul'

theorem inv_adjugate (A : Matrix n n α) (h : IsUnit A.det) : (adjugate A)⁻¹ = h.unit⁻¹ • A := by
  refine' inv_eq_left_inv _
  -- ⊢ (IsUnit.unit h)⁻¹ • A * adjugate A = 1
  rw [smul_mul, mul_adjugate, Units.smul_def, smul_smul, h.val_inv_mul, one_smul]
  -- 🎉 no goals
#align matrix.inv_adjugate Matrix.inv_adjugate

section Diagonal

/-- `diagonal v` is invertible if `v` is -/
def diagonalInvertible {α} [NonAssocSemiring α] (v : n → α) [Invertible v] :
    Invertible (diagonal v) :=
  Invertible.map (diagonalRingHom n α) v
#align matrix.diagonal_invertible Matrix.diagonalInvertible

theorem invOf_diagonal_eq {α} [Semiring α] (v : n → α) [Invertible v] [Invertible (diagonal v)] :
    ⅟ (diagonal v) = diagonal (⅟ v) := by
  letI := diagonalInvertible v
  -- ⊢ ⅟(diagonal v) = diagonal ⅟v
  -- Porting note: no longer need `haveI := Invertible.subsingleton (diagonal v)`
  convert(rfl : ⅟ (diagonal v) = _)
  -- 🎉 no goals
#align matrix.inv_of_diagonal_eq Matrix.invOf_diagonal_eq

/-- `v` is invertible if `diagonal v` is -/
def invertibleOfDiagonalInvertible (v : n → α) [Invertible (diagonal v)] : Invertible v where
  invOf := diag (⅟ (diagonal v))
  invOf_mul_self :=
    funext fun i => by
      letI : Invertible (diagonal v).det := detInvertibleOfInvertible _
      -- ⊢ (diag ⅟(diagonal v) * v) i = OfNat.ofNat 1 i
      rw [invOf_eq, diag_smul, adjugate_diagonal, diag_diagonal]
      -- ⊢ ((⅟(det (diagonal v)) • fun i => ∏ j in erase univ i, v j) * v) i = OfNat.of …
      dsimp
      -- ⊢ (⅟(det (diagonal v)) * ∏ j in erase univ i, v j) * v i = 1
      rw [mul_assoc, prod_erase_mul _ _ (Finset.mem_univ _), ← det_diagonal]
      -- ⊢ ⅟(det (diagonal v)) * det (diagonal fun x => v x) = 1
      exact mul_invOf_self _
      -- 🎉 no goals
  mul_invOf_self :=
    funext fun i => by
      letI : Invertible (diagonal v).det := detInvertibleOfInvertible _
      -- ⊢ (v * diag ⅟(diagonal v)) i = OfNat.ofNat 1 i
      rw [invOf_eq, diag_smul, adjugate_diagonal, diag_diagonal]
      -- ⊢ (v * ⅟(det (diagonal v)) • fun i => ∏ j in erase univ i, v j) i = OfNat.ofNa …
      dsimp
      -- ⊢ v i * (⅟(det (diagonal v)) * ∏ j in erase univ i, v j) = 1
      rw [mul_left_comm, mul_prod_erase _ _ (Finset.mem_univ _), ← det_diagonal]
      -- ⊢ ⅟(det (diagonal v)) * det (diagonal fun x => v x) = 1
      exact mul_invOf_self _
      -- 🎉 no goals
#align matrix.invertible_of_diagonal_invertible Matrix.invertibleOfDiagonalInvertible

/-- Together `Matrix.diagonalInvertible` and `Matrix.invertibleOfDiagonalInvertible` form an
equivalence, although both sides of the equiv are subsingleton anyway. -/
@[simps]
def diagonalInvertibleEquivInvertible (v : n → α) : Invertible (diagonal v) ≃ Invertible v where
  toFun := @invertibleOfDiagonalInvertible _ _ _ _ _ _
  invFun := @diagonalInvertible _ _ _ _ _ _
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
#align matrix.diagonal_invertible_equiv_invertible Matrix.diagonalInvertibleEquivInvertible

/-- When lowered to a prop, `Matrix.diagonalInvertibleEquivInvertible` forms an `iff`. -/
@[simp]
theorem isUnit_diagonal {v : n → α} : IsUnit (diagonal v) ↔ IsUnit v := by
  simp only [← nonempty_invertible_iff_isUnit,
    (diagonalInvertibleEquivInvertible v).nonempty_congr]
#align matrix.is_unit_diagonal Matrix.isUnit_diagonal

theorem inv_diagonal (v : n → α) : (diagonal v)⁻¹ = diagonal (Ring.inverse v) := by
  rw [nonsing_inv_eq_ring_inverse]
  -- ⊢ Ring.inverse (diagonal v) = diagonal (Ring.inverse v)
  by_cases h : IsUnit v
  -- ⊢ Ring.inverse (diagonal v) = diagonal (Ring.inverse v)
  · have := isUnit_diagonal.mpr h
    -- ⊢ Ring.inverse (diagonal v) = diagonal (Ring.inverse v)
    cases this.nonempty_invertible
    -- ⊢ Ring.inverse (diagonal v) = diagonal (Ring.inverse v)
    cases h.nonempty_invertible
    -- ⊢ Ring.inverse (diagonal v) = diagonal (Ring.inverse v)
    rw [Ring.inverse_invertible, Ring.inverse_invertible, invOf_diagonal_eq]
    -- 🎉 no goals
  · have := isUnit_diagonal.not.mpr h
    -- ⊢ Ring.inverse (diagonal v) = diagonal (Ring.inverse v)
    rw [Ring.inverse_non_unit _ h, Pi.zero_def, diagonal_zero, Ring.inverse_non_unit _ this]
    -- 🎉 no goals
#align matrix.inv_diagonal Matrix.inv_diagonal

end Diagonal

@[simp]
theorem inv_inv_inv (A : Matrix n n α) : A⁻¹⁻¹⁻¹ = A⁻¹ := by
  by_cases h : IsUnit A.det
  -- ⊢ A⁻¹⁻¹⁻¹ = A⁻¹
  · rw [nonsing_inv_nonsing_inv _ h]
    -- 🎉 no goals
  · simp [nonsing_inv_apply_not_isUnit _ h]
    -- 🎉 no goals
#align matrix.inv_inv_inv Matrix.inv_inv_inv

theorem mul_inv_rev (A B : Matrix n n α) : (A * B)⁻¹ = B⁻¹ * A⁻¹ := by
  simp only [inv_def]
  -- ⊢ Ring.inverse (det (A * B)) • adjugate (A * B) = Ring.inverse (det B) • adjug …
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, det_mul, adjugate_mul_distrib,
    Ring.mul_inverse_rev]
#align matrix.mul_inv_rev Matrix.mul_inv_rev

/-- A version of `List.prod_inv_reverse` for `Matrix.inv`. -/
theorem list_prod_inv_reverse : ∀ l : List (Matrix n n α), l.prod⁻¹ = (l.reverse.map Inv.inv).prod
  | [] => by rw [List.reverse_nil, List.map_nil, List.prod_nil, inv_one]
             -- 🎉 no goals
  | A::Xs => by
    rw [List.reverse_cons', List.map_concat, List.prod_concat, List.prod_cons,
      mul_inv_rev, list_prod_inv_reverse Xs]
#align matrix.list_prod_inv_reverse Matrix.list_prod_inv_reverse

/-- One form of **Cramer's rule**. See `Matrix.mulVec_cramer` for a stronger form. -/
@[simp]
theorem det_smul_inv_mulVec_eq_cramer (A : Matrix n n α) (b : n → α) (h : IsUnit A.det) :
    A.det • A⁻¹.mulVec b = cramer A b := by
  rw [cramer_eq_adjugate_mulVec, A.nonsing_inv_apply h, ← smul_mulVec_assoc, smul_smul,
    h.mul_val_inv, one_smul]
#align matrix.det_smul_inv_mul_vec_eq_cramer Matrix.det_smul_inv_mulVec_eq_cramer

/-- One form of **Cramer's rule**. See `Matrix.mulVec_cramer` for a stronger form. -/
@[simp]
theorem det_smul_inv_vecMul_eq_cramer_transpose (A : Matrix n n α) (b : n → α) (h : IsUnit A.det) :
    A.det • A⁻¹.vecMul b = cramer Aᵀ b := by
  rw [← A⁻¹.transpose_transpose, vecMul_transpose, transpose_nonsing_inv, ← det_transpose,
    Aᵀ.det_smul_inv_mulVec_eq_cramer _ (isUnit_det_transpose A h)]
#align matrix.det_smul_inv_vec_mul_eq_cramer_transpose Matrix.det_smul_inv_vecMul_eq_cramer_transpose

/-! ### Inverses of permutated matrices

Note that the simp-normal form of `Matrix.reindex` is `Matrix.submatrix`, so we prove most of these
results about only the latter.
-/


section Submatrix

variable [Fintype m]

variable [DecidableEq m]

/-- `A.submatrix e₁ e₂` is invertible if `A` is -/
def submatrixEquivInvertible (A : Matrix m m α) (e₁ e₂ : n ≃ m) [Invertible A] :
    Invertible (A.submatrix e₁ e₂) :=
  invertibleOfRightInverse _ ((⅟ A).submatrix e₂ e₁) <| by
    rw [Matrix.submatrix_mul_equiv, mul_invOf_self, submatrix_one_equiv]
    -- 🎉 no goals
#align matrix.submatrix_equiv_invertible Matrix.submatrixEquivInvertible

/-- `A` is invertible if `A.submatrix e₁ e₂` is -/
def invertibleOfSubmatrixEquivInvertible (A : Matrix m m α) (e₁ e₂ : n ≃ m)
    [Invertible (A.submatrix e₁ e₂)] : Invertible A :=
  invertibleOfRightInverse _ ((⅟ (A.submatrix e₁ e₂)).submatrix e₂.symm e₁.symm) <| by
    have : A = (A.submatrix e₁ e₂).submatrix e₁.symm e₂.symm := by simp
    -- ⊢ A * submatrix ⅟(submatrix A ↑e₁ ↑e₂) ↑e₂.symm ↑e₁.symm = 1
    -- Porting note: was
    -- conv in _ * _ =>
    --   congr
    --   rw [this]
    rw [congr_arg₂ (· * ·) this rfl]
    -- ⊢ submatrix (submatrix A ↑e₁ ↑e₂) ↑e₁.symm ↑e₂.symm * submatrix ⅟(submatrix A  …
    rw [Matrix.submatrix_mul_equiv, mul_invOf_self, submatrix_one_equiv]
    -- 🎉 no goals
#align matrix.invertible_of_submatrix_equiv_invertible Matrix.invertibleOfSubmatrixEquivInvertible

theorem invOf_submatrix_equiv_eq (A : Matrix m m α) (e₁ e₂ : n ≃ m) [Invertible A]
    [Invertible (A.submatrix e₁ e₂)] : ⅟ (A.submatrix e₁ e₂) = (⅟ A).submatrix e₂ e₁ := by
  letI := submatrixEquivInvertible A e₁ e₂
  -- ⊢ ⅟(submatrix A ↑e₁ ↑e₂) = submatrix ⅟A ↑e₂ ↑e₁
  -- Porting note: no longer need `haveI := Invertible.subsingleton (A.submatrix e₁ e₂)`
  convert(rfl : ⅟ (A.submatrix e₁ e₂) = _)
  -- 🎉 no goals
#align matrix.inv_of_submatrix_equiv_eq Matrix.invOf_submatrix_equiv_eq

/-- Together `Matrix.submatrixEquivInvertible` and
`Matrix.invertibleOfSubmatrixEquivInvertible` form an equivalence, although both sides of the
equiv are subsingleton anyway. -/
@[simps]
def submatrixEquivInvertibleEquivInvertible (A : Matrix m m α) (e₁ e₂ : n ≃ m) :
    Invertible (A.submatrix e₁ e₂) ≃ Invertible A where
  toFun _ := invertibleOfSubmatrixEquivInvertible A e₁ e₂
  invFun _ := submatrixEquivInvertible A e₁ e₂
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
#align matrix.submatrix_equiv_invertible_equiv_invertible Matrix.submatrixEquivInvertibleEquivInvertible

/-- When lowered to a prop, `Matrix.invertibleOfSubmatrixEquivInvertible` forms an `iff`. -/
@[simp]
theorem isUnit_submatrix_equiv {A : Matrix m m α} (e₁ e₂ : n ≃ m) :
    IsUnit (A.submatrix e₁ e₂) ↔ IsUnit A := by
  simp only [← nonempty_invertible_iff_isUnit,
    (submatrixEquivInvertibleEquivInvertible A _ _).nonempty_congr]
#align matrix.is_unit_submatrix_equiv Matrix.isUnit_submatrix_equiv

@[simp]
theorem inv_submatrix_equiv (A : Matrix m m α) (e₁ e₂ : n ≃ m) :
    (A.submatrix e₁ e₂)⁻¹ = A⁻¹.submatrix e₂ e₁ := by
  by_cases h : IsUnit A
  -- ⊢ (submatrix A ↑e₁ ↑e₂)⁻¹ = submatrix A⁻¹ ↑e₂ ↑e₁
  · cases h.nonempty_invertible
    -- ⊢ (submatrix A ↑e₁ ↑e₂)⁻¹ = submatrix A⁻¹ ↑e₂ ↑e₁
    letI := submatrixEquivInvertible A e₁ e₂
    -- ⊢ (submatrix A ↑e₁ ↑e₂)⁻¹ = submatrix A⁻¹ ↑e₂ ↑e₁
    rw [← invOf_eq_nonsing_inv, ← invOf_eq_nonsing_inv, invOf_submatrix_equiv_eq A]
    -- 🎉 no goals
  · have := (isUnit_submatrix_equiv e₁ e₂).not.mpr h
    -- ⊢ (submatrix A ↑e₁ ↑e₂)⁻¹ = submatrix A⁻¹ ↑e₂ ↑e₁
    simp_rw [nonsing_inv_eq_ring_inverse, Ring.inverse_non_unit _ h, Ring.inverse_non_unit _ this,
      submatrix_zero, Pi.zero_apply]
#align matrix.inv_submatrix_equiv Matrix.inv_submatrix_equiv

theorem inv_reindex (e₁ e₂ : n ≃ m) (A : Matrix n n α) : (reindex e₁ e₂ A)⁻¹ = reindex e₂ e₁ A⁻¹ :=
  inv_submatrix_equiv A e₁.symm e₂.symm
#align matrix.inv_reindex Matrix.inv_reindex

end Submatrix

/-! ### More results about determinants -/


section Det

variable [Fintype m] [DecidableEq m]

/-- A variant of `Matrix.det_units_conj`. -/
theorem det_conj {M : Matrix m m α} (h : IsUnit M) (N : Matrix m m α) : det (M * N * M⁻¹) = det N :=
  by rw [← h.unit_spec, ← coe_units_inv, det_units_conj]
     -- 🎉 no goals
#align matrix.det_conj Matrix.det_conj

/-- A variant of `Matrix.det_units_conj'`. -/
theorem det_conj' {M : Matrix m m α} (h : IsUnit M) (N : Matrix m m α) :
    det (M⁻¹ * N * M) = det N := by rw [← h.unit_spec, ← coe_units_inv, det_units_conj']
                                    -- 🎉 no goals
#align matrix.det_conj' Matrix.det_conj'

end Det

end Matrix
