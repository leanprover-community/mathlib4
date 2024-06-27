/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Eric Wieser, Jeremy Avigad, Johan Commelin
-/
import Mathlib.Data.Matrix.Invertible
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef

#align_import linear_algebra.matrix.schur_complement from "leanprover-community/mathlib"@"a176cb1219e300e85793d44583dede42377b51af"

/-! # 2×2 block matrices and the Schur complement

This file proves properties of 2×2 block matrices `[A B; C D]` that relate to the Schur complement
`D - C*A⁻¹*B`.

Some of the results here generalize to 2×2 matrices in a category, rather than just a ring. A few
results in this direction can be found in the file `CateogryTheory.Preadditive.Biproducts`,
especially the declarations `CategoryTheory.Biprod.gaussian` and `CategoryTheory.Biprod.isoElim`.
Compare with `Matrix.invertibleOfFromBlocks₁₁Invertible`.

## Main results

 * `Matrix.det_fromBlocks₁₁`, `Matrix.det_fromBlocks₂₂`: determinant of a block matrix in terms of
   the Schur complement.
 * `Matrix.invOf_fromBlocks_zero₂₁_eq`, `Matrix.invOf_fromBlocks_zero₁₂_eq`: the inverse of a
   block triangular matrix.
 * `Matrix.isUnit_fromBlocks_zero₂₁`, `Matrix.isUnit_fromBlocks_zero₁₂`: invertibility of a
   block triangular matrix.
 * `Matrix.det_one_add_mul_comm`: the **Weinstein–Aronszajn identity**.
 * `Matrix.PosSemidef.fromBlocks₁₁` and `Matrix.PosSemidef.fromBlocks₂₂`: If a matrix `A` is
  positive definite, then `[A B; Bᴴ D]` is postive semidefinite if and only if `D - Bᴴ A⁻¹ B` is
  postive semidefinite.

-/


variable {l m n α : Type*}

namespace Matrix

open scoped Matrix

section CommRing

variable [Fintype l] [Fintype m] [Fintype n]
variable [DecidableEq l] [DecidableEq m] [DecidableEq n]
variable [CommRing α]

/-- LDU decomposition of a block matrix with an invertible top-left corner, using the
Schur complement. -/
theorem fromBlocks_eq_of_invertible₁₁ (A : Matrix m m α) (B : Matrix m n α) (C : Matrix l m α)
    (D : Matrix l n α) [Invertible A] :
    fromBlocks A B C D =
      fromBlocks 1 0 (C * ⅟ A) 1 * fromBlocks A 0 0 (D - C * ⅟ A * B) *
        fromBlocks 1 (⅟ A * B) 0 1 := by
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.one_mul, Matrix.mul_one, invOf_mul_self, Matrix.mul_invOf_self_assoc,
    Matrix.mul_invOf_mul_self_cancel, Matrix.mul_assoc, add_sub_cancel]
#align matrix.from_blocks_eq_of_invertible₁₁ Matrix.fromBlocks_eq_of_invertible₁₁

/-- LDU decomposition of a block matrix with an invertible bottom-right corner, using the
Schur complement. -/
theorem fromBlocks_eq_of_invertible₂₂ (A : Matrix l m α) (B : Matrix l n α) (C : Matrix n m α)
    (D : Matrix n n α) [Invertible D] :
    fromBlocks A B C D =
      fromBlocks 1 (B * ⅟ D) 0 1 * fromBlocks (A - B * ⅟ D * C) 0 0 D *
        fromBlocks 1 0 (⅟ D * C) 1 :=
  (Matrix.reindex (Equiv.sumComm _ _) (Equiv.sumComm _ _)).injective <| by
    simpa [reindex_apply, Equiv.sumComm_symm, ← submatrix_mul_equiv _ _ _ (Equiv.sumComm n m), ←
      submatrix_mul_equiv _ _ _ (Equiv.sumComm n l), Equiv.sumComm_apply,
      fromBlocks_submatrix_sum_swap_sum_swap] using fromBlocks_eq_of_invertible₁₁ D C B A
#align matrix.from_blocks_eq_of_invertible₂₂ Matrix.fromBlocks_eq_of_invertible₂₂

section Triangular

/-! #### Block triangular matrices -/


/-- An upper-block-triangular matrix is invertible if its diagonal is. -/
def fromBlocksZero₂₁Invertible (A : Matrix m m α) (B : Matrix m n α) (D : Matrix n n α)
    [Invertible A] [Invertible D] : Invertible (fromBlocks A B 0 D) :=
  invertibleOfLeftInverse _ (fromBlocks (⅟ A) (-(⅟ A * B * ⅟ D)) 0 (⅟ D)) <| by
    simp_rw [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero,
      Matrix.neg_mul, invOf_mul_self, Matrix.mul_invOf_mul_self_cancel, add_right_neg,
      fromBlocks_one]
#align matrix.from_blocks_zero₂₁_invertible Matrix.fromBlocksZero₂₁Invertible

/-- A lower-block-triangular matrix is invertible if its diagonal is. -/
def fromBlocksZero₁₂Invertible (A : Matrix m m α) (C : Matrix n m α) (D : Matrix n n α)
    [Invertible A] [Invertible D] : Invertible (fromBlocks A 0 C D) :=
  invertibleOfLeftInverse _
      (fromBlocks (⅟ A) 0 (-(⅟ D * C * ⅟ A))
        (⅟ D)) <| by -- a symmetry argument is more work than just copying the proof
    simp_rw [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero,
      Matrix.neg_mul, invOf_mul_self, Matrix.mul_invOf_mul_self_cancel, add_left_neg,
      fromBlocks_one]
#align matrix.from_blocks_zero₁₂_invertible Matrix.fromBlocksZero₁₂Invertible

theorem invOf_fromBlocks_zero₂₁_eq (A : Matrix m m α) (B : Matrix m n α) (D : Matrix n n α)
    [Invertible A] [Invertible D] [Invertible (fromBlocks A B 0 D)] :
    ⅟ (fromBlocks A B 0 D) = fromBlocks (⅟ A) (-(⅟ A * B * ⅟ D)) 0 (⅟ D) := by
  letI := fromBlocksZero₂₁Invertible A B D
  convert (rfl : ⅟ (fromBlocks A B 0 D) = _)
#align matrix.inv_of_from_blocks_zero₂₁_eq Matrix.invOf_fromBlocks_zero₂₁_eq

theorem invOf_fromBlocks_zero₁₂_eq (A : Matrix m m α) (C : Matrix n m α) (D : Matrix n n α)
    [Invertible A] [Invertible D] [Invertible (fromBlocks A 0 C D)] :
    ⅟ (fromBlocks A 0 C D) = fromBlocks (⅟ A) 0 (-(⅟ D * C * ⅟ A)) (⅟ D) := by
  letI := fromBlocksZero₁₂Invertible A C D
  convert (rfl : ⅟ (fromBlocks A 0 C D) = _)
#align matrix.inv_of_from_blocks_zero₁₂_eq Matrix.invOf_fromBlocks_zero₁₂_eq

/-- Both diagonal entries of an invertible upper-block-triangular matrix are invertible (by reading
off the diagonal entries of the inverse). -/
def invertibleOfFromBlocksZero₂₁Invertible (A : Matrix m m α) (B : Matrix m n α) (D : Matrix n n α)
    [Invertible (fromBlocks A B 0 D)] : Invertible A × Invertible D where
  fst :=
    invertibleOfLeftInverse _ (⅟ (fromBlocks A B 0 D)).toBlocks₁₁ <| by
      have := invOf_mul_self (fromBlocks A B 0 D)
      rw [← fromBlocks_toBlocks (⅟ (fromBlocks A B 0 D)), fromBlocks_multiply] at this
      replace := congr_arg Matrix.toBlocks₁₁ this
      simpa only [Matrix.toBlocks_fromBlocks₁₁, Matrix.mul_zero, add_zero, ← fromBlocks_one] using
        this
  snd :=
    invertibleOfRightInverse _ (⅟ (fromBlocks A B 0 D)).toBlocks₂₂ <| by
      have := mul_invOf_self (fromBlocks A B 0 D)
      rw [← fromBlocks_toBlocks (⅟ (fromBlocks A B 0 D)), fromBlocks_multiply] at this
      replace := congr_arg Matrix.toBlocks₂₂ this
      simpa only [Matrix.toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add, ← fromBlocks_one] using
        this
#align matrix.invertible_of_from_blocks_zero₂₁_invertible Matrix.invertibleOfFromBlocksZero₂₁Invertible

/-- Both diagonal entries of an invertible lower-block-triangular matrix are invertible (by reading
off the diagonal entries of the inverse). -/
def invertibleOfFromBlocksZero₁₂Invertible (A : Matrix m m α) (C : Matrix n m α) (D : Matrix n n α)
    [Invertible (fromBlocks A 0 C D)] : Invertible A × Invertible D where
  fst :=
    invertibleOfRightInverse _ (⅟ (fromBlocks A 0 C D)).toBlocks₁₁ <| by
      have := mul_invOf_self (fromBlocks A 0 C D)
      rw [← fromBlocks_toBlocks (⅟ (fromBlocks A 0 C D)), fromBlocks_multiply] at this
      replace := congr_arg Matrix.toBlocks₁₁ this
      simpa only [Matrix.toBlocks_fromBlocks₁₁, Matrix.zero_mul, add_zero, ← fromBlocks_one] using
        this
  snd :=
    invertibleOfLeftInverse _ (⅟ (fromBlocks A 0 C D)).toBlocks₂₂ <| by
      have := invOf_mul_self (fromBlocks A 0 C D)
      rw [← fromBlocks_toBlocks (⅟ (fromBlocks A 0 C D)), fromBlocks_multiply] at this
      replace := congr_arg Matrix.toBlocks₂₂ this
      simpa only [Matrix.toBlocks_fromBlocks₂₂, Matrix.mul_zero, zero_add, ← fromBlocks_one] using
        this
#align matrix.invertible_of_from_blocks_zero₁₂_invertible Matrix.invertibleOfFromBlocksZero₁₂Invertible

/-- `invertibleOfFromBlocksZero₂₁Invertible` and `Matrix.fromBlocksZero₂₁Invertible` form
an equivalence. -/
def fromBlocksZero₂₁InvertibleEquiv (A : Matrix m m α) (B : Matrix m n α) (D : Matrix n n α) :
    Invertible (fromBlocks A B 0 D) ≃ Invertible A × Invertible D where
  toFun _ := invertibleOfFromBlocksZero₂₁Invertible A B D
  invFun i := by
    letI := i.1
    letI := i.2
    exact fromBlocksZero₂₁Invertible A B D
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
#align matrix.from_blocks_zero₂₁_invertible_equiv Matrix.fromBlocksZero₂₁InvertibleEquiv

/-- `invertibleOfFromBlocksZero₁₂Invertible` and `Matrix.fromBlocksZero₁₂Invertible` form
an equivalence. -/
def fromBlocksZero₁₂InvertibleEquiv (A : Matrix m m α) (C : Matrix n m α) (D : Matrix n n α) :
    Invertible (fromBlocks A 0 C D) ≃ Invertible A × Invertible D where
  toFun _ := invertibleOfFromBlocksZero₁₂Invertible A C D
  invFun i := by
    letI := i.1
    letI := i.2
    exact fromBlocksZero₁₂Invertible A C D
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
#align matrix.from_blocks_zero₁₂_invertible_equiv Matrix.fromBlocksZero₁₂InvertibleEquiv

/-- An upper block-triangular matrix is invertible iff both elements of its diagonal are.

This is a propositional form of `Matrix.fromBlocksZero₂₁InvertibleEquiv`. -/
@[simp]
theorem isUnit_fromBlocks_zero₂₁ {A : Matrix m m α} {B : Matrix m n α} {D : Matrix n n α} :
    IsUnit (fromBlocks A B 0 D) ↔ IsUnit A ∧ IsUnit D := by
  simp only [← nonempty_invertible_iff_isUnit, ← nonempty_prod,
    (fromBlocksZero₂₁InvertibleEquiv _ _ _).nonempty_congr]
#align matrix.is_unit_from_blocks_zero₂₁ Matrix.isUnit_fromBlocks_zero₂₁

/-- A lower block-triangular matrix is invertible iff both elements of its diagonal are.

This is a propositional form of `Matrix.fromBlocksZero₁₂InvertibleEquiv` forms an `iff`. -/
@[simp]
theorem isUnit_fromBlocks_zero₁₂ {A : Matrix m m α} {C : Matrix n m α} {D : Matrix n n α} :
    IsUnit (fromBlocks A 0 C D) ↔ IsUnit A ∧ IsUnit D := by
  simp only [← nonempty_invertible_iff_isUnit, ← nonempty_prod,
    (fromBlocksZero₁₂InvertibleEquiv _ _ _).nonempty_congr]
#align matrix.is_unit_from_blocks_zero₁₂ Matrix.isUnit_fromBlocks_zero₁₂

/-- An expression for the inverse of an upper block-triangular matrix, when either both elements of
diagonal are invertible, or both are not. -/
theorem inv_fromBlocks_zero₂₁_of_isUnit_iff (A : Matrix m m α) (B : Matrix m n α) (D : Matrix n n α)
    (hAD : IsUnit A ↔ IsUnit D) :
    (fromBlocks A B 0 D)⁻¹ = fromBlocks A⁻¹ (-(A⁻¹ * B * D⁻¹)) 0 D⁻¹ := by
  by_cases hA : IsUnit A
  · have hD := hAD.mp hA
    cases hA.nonempty_invertible
    cases hD.nonempty_invertible
    letI := fromBlocksZero₂₁Invertible A B D
    simp_rw [← invOf_eq_nonsing_inv, invOf_fromBlocks_zero₂₁_eq]
  · have hD := hAD.not.mp hA
    have : ¬IsUnit (fromBlocks A B 0 D) :=
      isUnit_fromBlocks_zero₂₁.not.mpr (not_and'.mpr fun _ => hA)
    simp_rw [nonsing_inv_eq_ring_inverse, Ring.inverse_non_unit _ hA, Ring.inverse_non_unit _ hD,
      Ring.inverse_non_unit _ this, Matrix.zero_mul, neg_zero, fromBlocks_zero]
#align matrix.inv_from_blocks_zero₂₁_of_is_unit_iff Matrix.inv_fromBlocks_zero₂₁_of_isUnit_iff

/-- An expression for the inverse of a lower block-triangular matrix, when either both elements of
diagonal are invertible, or both are not. -/
theorem inv_fromBlocks_zero₁₂_of_isUnit_iff (A : Matrix m m α) (C : Matrix n m α) (D : Matrix n n α)
    (hAD : IsUnit A ↔ IsUnit D) :
    (fromBlocks A 0 C D)⁻¹ = fromBlocks A⁻¹ 0 (-(D⁻¹ * C * A⁻¹)) D⁻¹ := by
  by_cases hA : IsUnit A
  · have hD := hAD.mp hA
    cases hA.nonempty_invertible
    cases hD.nonempty_invertible
    letI := fromBlocksZero₁₂Invertible A C D
    simp_rw [← invOf_eq_nonsing_inv, invOf_fromBlocks_zero₁₂_eq]
  · have hD := hAD.not.mp hA
    have : ¬IsUnit (fromBlocks A 0 C D) :=
      isUnit_fromBlocks_zero₁₂.not.mpr (not_and'.mpr fun _ => hA)
    simp_rw [nonsing_inv_eq_ring_inverse, Ring.inverse_non_unit _ hA, Ring.inverse_non_unit _ hD,
      Ring.inverse_non_unit _ this, Matrix.zero_mul, neg_zero, fromBlocks_zero]
#align matrix.inv_from_blocks_zero₁₂_of_is_unit_iff Matrix.inv_fromBlocks_zero₁₂_of_isUnit_iff

end Triangular

/-! ### 2×2 block matrices -/


section Block

/-! #### General 2×2 block matrices-/


/-- A block matrix is invertible if the bottom right corner and the corresponding schur complement
is. -/
def fromBlocks₂₂Invertible (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
    (D : Matrix n n α) [Invertible D] [Invertible (A - B * ⅟ D * C)] :
    Invertible (fromBlocks A B C D) := by
  -- factor `fromBlocks` via `fromBlocks_eq_of_invertible₂₂`, and state the inverse we expect
  convert Invertible.copy' _ _ (fromBlocks (⅟ (A - B * ⅟ D * C)) (-(⅟ (A - B * ⅟ D * C) * B * ⅟ D))
    (-(⅟ D * C * ⅟ (A - B * ⅟ D * C))) (⅟ D + ⅟ D * C * ⅟ (A - B * ⅟ D * C) * B * ⅟ D))
      (fromBlocks_eq_of_invertible₂₂ _ _ _ _) _
  · -- the product is invertible because all the factors are
    letI : Invertible (1 : Matrix n n α) := invertibleOne
    letI : Invertible (1 : Matrix m m α) := invertibleOne
    refine Invertible.mul ?_ (fromBlocksZero₁₂Invertible _ _ _)
    exact
      Invertible.mul (fromBlocksZero₂₁Invertible _ _ _)
        (fromBlocksZero₂₁Invertible _ _ _)
  · -- unfold the `Invertible` instances to get the raw factors
    show
      _ =
        fromBlocks 1 0 (-(1 * (⅟ D * C) * 1)) 1 *
          (fromBlocks (⅟ (A - B * ⅟ D * C)) (-(⅟ (A - B * ⅟ D * C) * 0 * ⅟ D)) 0 (⅟ D) *
            fromBlocks 1 (-(1 * (B * ⅟ D) * 1)) 0 1)
    -- combine into a single block matrix
    simp only [fromBlocks_multiply, invOf_one, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
      Matrix.mul_zero, add_zero, zero_add, neg_zero, Matrix.mul_neg, Matrix.neg_mul, neg_neg, ←
      Matrix.mul_assoc, add_comm (⅟D)]
#align matrix.from_blocks₂₂_invertible Matrix.fromBlocks₂₂Invertible

/-- A block matrix is invertible if the top left corner and the corresponding schur complement
is. -/
def fromBlocks₁₁Invertible (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
    (D : Matrix n n α) [Invertible A] [Invertible (D - C * ⅟ A * B)] :
    Invertible (fromBlocks A B C D) := by
  -- we argue by symmetry
  letI := fromBlocks₂₂Invertible D C B A
  letI iDCBA :=
    submatrixEquivInvertible (fromBlocks D C B A) (Equiv.sumComm _ _) (Equiv.sumComm _ _)
  exact
    iDCBA.copy' _
      (fromBlocks (⅟ A + ⅟ A * B * ⅟ (D - C * ⅟ A * B) * C * ⅟ A) (-(⅟ A * B * ⅟ (D - C * ⅟ A * B)))
        (-(⅟ (D - C * ⅟ A * B) * C * ⅟ A)) (⅟ (D - C * ⅟ A * B)))
      (fromBlocks_submatrix_sum_swap_sum_swap _ _ _ _).symm
      (fromBlocks_submatrix_sum_swap_sum_swap _ _ _ _).symm
#align matrix.from_blocks₁₁_invertible Matrix.fromBlocks₁₁Invertible

theorem invOf_fromBlocks₂₂_eq (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
    (D : Matrix n n α) [Invertible D] [Invertible (A - B * ⅟ D * C)]
    [Invertible (fromBlocks A B C D)] :
    ⅟ (fromBlocks A B C D) =
      fromBlocks (⅟ (A - B * ⅟ D * C)) (-(⅟ (A - B * ⅟ D * C) * B * ⅟ D))
        (-(⅟ D * C * ⅟ (A - B * ⅟ D * C))) (⅟ D + ⅟ D * C * ⅟ (A - B * ⅟ D * C) * B * ⅟ D) := by
  letI := fromBlocks₂₂Invertible A B C D
  convert (rfl : ⅟ (fromBlocks A B C D) = _)
#align matrix.inv_of_from_blocks₂₂_eq Matrix.invOf_fromBlocks₂₂_eq

theorem invOf_fromBlocks₁₁_eq (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
    (D : Matrix n n α) [Invertible A] [Invertible (D - C * ⅟ A * B)]
    [Invertible (fromBlocks A B C D)] :
    ⅟ (fromBlocks A B C D) =
      fromBlocks (⅟ A + ⅟ A * B * ⅟ (D - C * ⅟ A * B) * C * ⅟ A) (-(⅟ A * B * ⅟ (D - C * ⅟ A * B)))
        (-(⅟ (D - C * ⅟ A * B) * C * ⅟ A)) (⅟ (D - C * ⅟ A * B)) := by
  letI := fromBlocks₁₁Invertible A B C D
  convert (rfl : ⅟ (fromBlocks A B C D) = _)
#align matrix.inv_of_from_blocks₁₁_eq Matrix.invOf_fromBlocks₁₁_eq

/-- If a block matrix is invertible and so is its bottom left element, then so is the corresponding
Schur complement. -/
def invertibleOfFromBlocks₂₂Invertible (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
    (D : Matrix n n α) [Invertible D] [Invertible (fromBlocks A B C D)] :
    Invertible (A - B * ⅟ D * C) := by
  suffices Invertible (fromBlocks (A - B * ⅟ D * C) 0 0 D) by
    exact (invertibleOfFromBlocksZero₁₂Invertible (A - B * ⅟ D * C) 0 D).1
  letI : Invertible (1 : Matrix n n α) := invertibleOne
  letI : Invertible (1 : Matrix m m α) := invertibleOne
  letI iDC : Invertible (fromBlocks 1 0 (⅟ D * C) 1 : Matrix (Sum m n) (Sum m n) α) :=
    fromBlocksZero₁₂Invertible _ _ _
  letI iBD : Invertible (fromBlocks 1 (B * ⅟ D) 0 1 : Matrix (Sum m n) (Sum m n) α) :=
    fromBlocksZero₂₁Invertible _ _ _
  letI iBDC := Invertible.copy ‹_› _ (fromBlocks_eq_of_invertible₂₂ A B C D).symm
  refine (iBD.mulLeft _).symm ?_
  exact (iDC.mulRight _).symm iBDC
#align matrix.invertible_of_from_blocks₂₂_invertible Matrix.invertibleOfFromBlocks₂₂Invertible

/-- If a block matrix is invertible and so is its bottom left element, then so is the corresponding
Schur complement. -/
def invertibleOfFromBlocks₁₁Invertible (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
    (D : Matrix n n α) [Invertible A] [Invertible (fromBlocks A B C D)] :
    Invertible (D - C * ⅟ A * B) := by
  -- another symmetry argument
  letI iABCD' :=
    submatrixEquivInvertible (fromBlocks A B C D) (Equiv.sumComm _ _) (Equiv.sumComm _ _)
  letI iDCBA := iABCD'.copy _ (fromBlocks_submatrix_sum_swap_sum_swap _ _ _ _).symm
  exact invertibleOfFromBlocks₂₂Invertible D C B A
#align matrix.invertible_of_from_blocks₁₁_invertible Matrix.invertibleOfFromBlocks₁₁Invertible

/-- `Matrix.invertibleOfFromBlocks₂₂Invertible` and `Matrix.fromBlocks₂₂Invertible` as an
equivalence. -/
def invertibleEquivFromBlocks₂₂Invertible (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
    (D : Matrix n n α) [Invertible D] :
    Invertible (fromBlocks A B C D) ≃ Invertible (A - B * ⅟ D * C) where
  toFun _iABCD := invertibleOfFromBlocks₂₂Invertible _ _ _ _
  invFun _i_schur := fromBlocks₂₂Invertible _ _ _ _
  left_inv _iABCD := Subsingleton.elim _ _
  right_inv _i_schur := Subsingleton.elim _ _
#align matrix.invertible_equiv_from_blocks₂₂_invertible Matrix.invertibleEquivFromBlocks₂₂Invertible

/-- `Matrix.invertibleOfFromBlocks₁₁Invertible` and `Matrix.fromBlocks₁₁Invertible` as an
equivalence. -/
def invertibleEquivFromBlocks₁₁Invertible (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
    (D : Matrix n n α) [Invertible A] :
    Invertible (fromBlocks A B C D) ≃ Invertible (D - C * ⅟ A * B) where
  toFun _iABCD := invertibleOfFromBlocks₁₁Invertible _ _ _ _
  invFun _i_schur := fromBlocks₁₁Invertible _ _ _ _
  left_inv _iABCD := Subsingleton.elim _ _
  right_inv _i_schur := Subsingleton.elim _ _
#align matrix.invertible_equiv_from_blocks₁₁_invertible Matrix.invertibleEquivFromBlocks₁₁Invertible

/-- If the bottom-left element of a block matrix is invertible, then the whole matrix is invertible
iff the corresponding schur complement is. -/
theorem isUnit_fromBlocks_iff_of_invertible₂₂ {A : Matrix m m α} {B : Matrix m n α}
    {C : Matrix n m α} {D : Matrix n n α} [Invertible D] :
    IsUnit (fromBlocks A B C D) ↔ IsUnit (A - B * ⅟ D * C) := by
  simp only [← nonempty_invertible_iff_isUnit,
    (invertibleEquivFromBlocks₂₂Invertible A B C D).nonempty_congr]
#align matrix.is_unit_from_blocks_iff_of_invertible₂₂ Matrix.isUnit_fromBlocks_iff_of_invertible₂₂

/-- If the top-right element of a block matrix is invertible, then the whole matrix is invertible
iff the corresponding schur complement is. -/
theorem isUnit_fromBlocks_iff_of_invertible₁₁ {A : Matrix m m α} {B : Matrix m n α}
    {C : Matrix n m α} {D : Matrix n n α} [Invertible A] :
    IsUnit (fromBlocks A B C D) ↔ IsUnit (D - C * ⅟ A * B) := by
  simp only [← nonempty_invertible_iff_isUnit,
    (invertibleEquivFromBlocks₁₁Invertible A B C D).nonempty_congr]
#align matrix.is_unit_from_blocks_iff_of_invertible₁₁ Matrix.isUnit_fromBlocks_iff_of_invertible₁₁

end Block

/-! ### Lemmas about `Matrix.det` -/


section Det

/-- Determinant of a 2×2 block matrix, expanded around an invertible top left element in terms of
the Schur complement. -/
theorem det_fromBlocks₁₁ (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
    (D : Matrix n n α) [Invertible A] :
    (Matrix.fromBlocks A B C D).det = det A * det (D - C * ⅟ A * B) := by
  rw [fromBlocks_eq_of_invertible₁₁ (A := A), det_mul, det_mul, det_fromBlocks_zero₂₁,
    det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂, det_one, det_one, one_mul, one_mul, mul_one]
#align matrix.det_from_blocks₁₁ Matrix.det_fromBlocks₁₁

@[simp]
theorem det_fromBlocks_one₁₁ (B : Matrix m n α) (C : Matrix n m α) (D : Matrix n n α) :
    (Matrix.fromBlocks 1 B C D).det = det (D - C * B) := by
  haveI : Invertible (1 : Matrix m m α) := invertibleOne
  rw [det_fromBlocks₁₁, invOf_one, Matrix.mul_one, det_one, one_mul]
#align matrix.det_from_blocks_one₁₁ Matrix.det_fromBlocks_one₁₁

/-- Determinant of a 2×2 block matrix, expanded around an invertible bottom right element in terms
of the Schur complement. -/
theorem det_fromBlocks₂₂ (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
    (D : Matrix n n α) [Invertible D] :
    (Matrix.fromBlocks A B C D).det = det D * det (A - B * ⅟ D * C) := by
  have : fromBlocks A B C D =
      (fromBlocks D C B A).submatrix (Equiv.sumComm _ _) (Equiv.sumComm _ _) := by
    ext (i j)
    cases i <;> cases j <;> rfl
  rw [this, det_submatrix_equiv_self, det_fromBlocks₁₁]
#align matrix.det_from_blocks₂₂ Matrix.det_fromBlocks₂₂

@[simp]
theorem det_fromBlocks_one₂₂ (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α) :
    (Matrix.fromBlocks A B C 1).det = det (A - B * C) := by
  haveI : Invertible (1 : Matrix n n α) := invertibleOne
  rw [det_fromBlocks₂₂, invOf_one, Matrix.mul_one, det_one, one_mul]
#align matrix.det_from_blocks_one₂₂ Matrix.det_fromBlocks_one₂₂

/-- The **Weinstein–Aronszajn identity**. Note the `1` on the LHS is of shape m×m, while the `1` on
the RHS is of shape n×n. -/
theorem det_one_add_mul_comm (A : Matrix m n α) (B : Matrix n m α) :
    det (1 + A * B) = det (1 + B * A) :=
  calc
    det (1 + A * B) = det (fromBlocks 1 (-A) B 1) := by
      rw [det_fromBlocks_one₂₂, Matrix.neg_mul, sub_neg_eq_add]
    _ = det (1 + B * A) := by rw [det_fromBlocks_one₁₁, Matrix.mul_neg, sub_neg_eq_add]
#align matrix.det_one_add_mul_comm Matrix.det_one_add_mul_comm

/-- Alternate statement of the **Weinstein–Aronszajn identity** -/
theorem det_mul_add_one_comm (A : Matrix m n α) (B : Matrix n m α) :
    det (A * B + 1) = det (B * A + 1) := by rw [add_comm, det_one_add_mul_comm, add_comm]
#align matrix.det_mul_add_one_comm Matrix.det_mul_add_one_comm

theorem det_one_sub_mul_comm (A : Matrix m n α) (B : Matrix n m α) :
    det (1 - A * B) = det (1 - B * A) := by
  rw [sub_eq_add_neg, ← Matrix.neg_mul, det_one_add_mul_comm, Matrix.mul_neg, ← sub_eq_add_neg]
#align matrix.det_one_sub_mul_comm Matrix.det_one_sub_mul_comm

/-- A special case of the **Matrix determinant lemma** for when `A = I`. -/
theorem det_one_add_col_mul_row {ι : Type*} [Unique ι] (u v : m → α) :
    det (1 + col ι u * row ι v) = 1 + v ⬝ᵥ u := by
  rw [det_one_add_mul_comm, det_unique, Pi.add_apply, Pi.add_apply, Matrix.one_apply_eq,
    Matrix.row_mul_col_apply]
#align matrix.det_one_add_col_mul_row Matrix.det_one_add_col_mul_row

/-- The **Matrix determinant lemma**

TODO: show the more general version without `hA : IsUnit A.det` as
`(A + col u * row v).det = A.det + v ⬝ᵥ (adjugate A) *ᵥ u`.
-/
theorem det_add_col_mul_row {ι : Type*} [Unique ι]
    {A : Matrix m m α} (hA : IsUnit A.det) (u v : m → α) :
    (A + col ι u * row ι v).det = A.det * (1 + row ι v * A⁻¹ * col ι u).det := by
  nth_rewrite 1 [← Matrix.mul_one A]
  rwa [← Matrix.mul_nonsing_inv_cancel_left A (col ι u * row ι v),
    ← Matrix.mul_add, det_mul, ← Matrix.mul_assoc, det_one_add_mul_comm,
    ← Matrix.mul_assoc]

/-- A generalization of the **Matrix determinant lemma** -/
theorem det_add_mul {A : Matrix m m α} (U : Matrix m n α)
    (V : Matrix n m α) (hA : IsUnit A.det) :
    (A + U * V).det = A.det * (1 + V * A⁻¹ * U).det := by
  nth_rewrite 1 [← Matrix.mul_one A]
  rwa [← Matrix.mul_nonsing_inv_cancel_left A (U * V), ← Matrix.mul_add,
    det_mul, ← Matrix.mul_assoc, det_one_add_mul_comm, ← Matrix.mul_assoc]

end Det

end CommRing

/-! ### Lemmas about `ℝ` and `ℂ` and other `StarOrderedRing`s -/


section StarOrderedRing

variable {𝕜 : Type*} [CommRing 𝕜] [PartialOrder 𝕜] [StarRing 𝕜] [StarOrderedRing 𝕜]

scoped infixl:65 " ⊕ᵥ " => Sum.elim

theorem schur_complement_eq₁₁ [Fintype m] [DecidableEq m] [Fintype n] {A : Matrix m m 𝕜}
    (B : Matrix m n 𝕜) (D : Matrix n n 𝕜) (x : m → 𝕜) (y : n → 𝕜) [Invertible A]
    (hA : A.IsHermitian) :
    (star (x ⊕ᵥ y)) ᵥ* (fromBlocks A B Bᴴ D) ⬝ᵥ (x ⊕ᵥ y) =
      (star (x + (A⁻¹ * B) *ᵥ y)) ᵥ* A ⬝ᵥ (x + (A⁻¹ * B) *ᵥ y) +
        (star y) ᵥ* (D - Bᴴ * A⁻¹ * B) ⬝ᵥ y := by
  simp [Function.star_sum_elim, fromBlocks_mulVec, vecMul_fromBlocks, add_vecMul,
    dotProduct_mulVec, vecMul_sub, Matrix.mul_assoc, vecMul_mulVec, hA.eq,
    conjTranspose_nonsing_inv, star_mulVec]
  abel
#align matrix.schur_complement_eq₁₁ Matrix.schur_complement_eq₁₁

theorem schur_complement_eq₂₂ [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m m 𝕜)
    (B : Matrix m n 𝕜) {D : Matrix n n 𝕜} (x : m → 𝕜) (y : n → 𝕜) [Invertible D]
    (hD : D.IsHermitian) :
    (star (x ⊕ᵥ y)) ᵥ* (fromBlocks A B Bᴴ D) ⬝ᵥ (x ⊕ᵥ y) =
      (star ((D⁻¹ * Bᴴ) *ᵥ x + y)) ᵥ* D ⬝ᵥ ((D⁻¹ * Bᴴ) *ᵥ x + y) +
        (star x) ᵥ* (A - B * D⁻¹ * Bᴴ) ⬝ᵥ x := by
  simp [Function.star_sum_elim, fromBlocks_mulVec, vecMul_fromBlocks, add_vecMul,
    dotProduct_mulVec, vecMul_sub, Matrix.mul_assoc, vecMul_mulVec, hD.eq,
    conjTranspose_nonsing_inv, star_mulVec]
  abel
#align matrix.schur_complement_eq₂₂ Matrix.schur_complement_eq₂₂

theorem IsHermitian.fromBlocks₁₁ [Fintype m] [DecidableEq m] {A : Matrix m m 𝕜} (B : Matrix m n 𝕜)
    (D : Matrix n n 𝕜) (hA : A.IsHermitian) :
    (Matrix.fromBlocks A B Bᴴ D).IsHermitian ↔ (D - Bᴴ * A⁻¹ * B).IsHermitian := by
  have hBAB : (Bᴴ * A⁻¹ * B).IsHermitian := by
    apply isHermitian_conjTranspose_mul_mul
    apply hA.inv
  rw [isHermitian_fromBlocks_iff]
  constructor
  · intro h
    apply IsHermitian.sub h.2.2.2 hBAB
  · intro h
    refine ⟨hA, rfl, conjTranspose_conjTranspose B, ?_⟩
    rw [← sub_add_cancel D]
    apply IsHermitian.add h hBAB
#align matrix.is_hermitian.from_blocks₁₁ Matrix.IsHermitian.fromBlocks₁₁

theorem IsHermitian.fromBlocks₂₂ [Fintype n] [DecidableEq n] (A : Matrix m m 𝕜) (B : Matrix m n 𝕜)
    {D : Matrix n n 𝕜} (hD : D.IsHermitian) :
    (Matrix.fromBlocks A B Bᴴ D).IsHermitian ↔ (A - B * D⁻¹ * Bᴴ).IsHermitian := by
  rw [← isHermitian_submatrix_equiv (Equiv.sumComm n m), Equiv.sumComm_apply,
    fromBlocks_submatrix_sum_swap_sum_swap]
  convert IsHermitian.fromBlocks₁₁ _ _ hD <;> simp
#align matrix.is_hermitian.from_blocks₂₂ Matrix.IsHermitian.fromBlocks₂₂

theorem PosSemidef.fromBlocks₁₁ [Fintype m] [DecidableEq m] [Fintype n] {A : Matrix m m 𝕜}
    (B : Matrix m n 𝕜) (D : Matrix n n 𝕜) (hA : A.PosDef) [Invertible A] :
    (fromBlocks A B Bᴴ D).PosSemidef ↔ (D - Bᴴ * A⁻¹ * B).PosSemidef := by
  rw [PosSemidef, IsHermitian.fromBlocks₁₁ _ _ hA.1]
  constructor
  · refine fun h => ⟨h.1, fun x => ?_⟩
    have := h.2 (-((A⁻¹ * B) *ᵥ x) ⊕ᵥ x)
    rw [dotProduct_mulVec, schur_complement_eq₁₁ B D _ _ hA.1, neg_add_self, dotProduct_zero,
      zero_add] at this
    rw [dotProduct_mulVec]; exact this
  · refine fun h => ⟨h.1, fun x => ?_⟩
    rw [dotProduct_mulVec, ← Sum.elim_comp_inl_inr x, schur_complement_eq₁₁ B D _ _ hA.1]
    apply le_add_of_nonneg_of_le
    · rw [← dotProduct_mulVec]
      apply hA.posSemidef.2
    · rw [← dotProduct_mulVec (star (x ∘ Sum.inr))]
      apply h.2
#align matrix.pos_semidef.from_blocks₁₁ Matrix.PosSemidef.fromBlocks₁₁

theorem PosSemidef.fromBlocks₂₂ [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m m 𝕜)
    (B : Matrix m n 𝕜) {D : Matrix n n 𝕜} (hD : D.PosDef) [Invertible D] :
    (fromBlocks A B Bᴴ D).PosSemidef ↔ (A - B * D⁻¹ * Bᴴ).PosSemidef := by
  rw [← posSemidef_submatrix_equiv (Equiv.sumComm n m), Equiv.sumComm_apply,
    fromBlocks_submatrix_sum_swap_sum_swap]
  convert PosSemidef.fromBlocks₁₁ Bᴴ A hD <;>
    simp
#align matrix.pos_semidef.from_blocks₂₂ Matrix.PosSemidef.fromBlocks₂₂

end StarOrderedRing

end Matrix
