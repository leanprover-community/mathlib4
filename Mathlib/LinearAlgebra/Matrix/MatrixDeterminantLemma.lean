import Mathlib.LinearAlgebra.Matrix.SchurComplement

variable {l m n α : Type*}

namespace Matrix

open scoped Matrix

section CommRing

variable [Fintype l] [Fintype m] [Fintype n]

variable [DecidableEq l] [DecidableEq m] [DecidableEq n]

variable [CommRing α]

/-- A special case of the **Matrix determinant lemma** for when `A = I`.

TODO: show this more generally. -/
theorem special_case_mdl (u v : m → α) : det (1 + col u * row v) = 1 + v ⬝ᵥ u := by
  rw [det_one_add_mul_comm, det_unique, Pi.add_apply, Pi.add_apply, Matrix.one_apply_eq,
    Matrix.row_mul_col_apply]

/- The **Matrix determinant lemma** --/
theorem the_mdl (u v : m → α) {A : Matrix m m α} (hA : IsUnit A.det):
    (A + col u * row v).det = A.det * (1 + row v * (A⁻¹) * col u).det := by
    nth_rewrite 1 [← Matrix.mul_one A]
    rw [← Matrix.mul_nonsing_inv_cancel_left A (col u * row v), ←Matrix.mul_add,det_mul, ←Matrix.mul_assoc, det_one_add_mul_comm, ←Matrix.mul_assoc]
    exact hA

/- A generalization of the **Matrix determinant lemma** -/
theorem generalised_mdl {A : Matrix m m α} (U : Matrix m n α)
    (V : Matrix n m α) (hA : IsUnit A.det) :
    (A + U * V).det = A.det * (1 + V * (A⁻¹) * U).det := by
  nth_rewrite 1 [← Matrix.mul_one A]
  rwa [← Matrix.mul_nonsing_inv_cancel_left A (U * V), ←Matrix.mul_add, det_mul,
    ←Matrix.mul_assoc, det_one_add_mul_comm, ←Matrix.mul_assoc]


/- A more generalization of the **Matrix determinant lemma** -/
theorem more_generalised_mdl {A : Matrix m m α} {W : Matrix n n α} (U : Matrix m n α)
    (V : Matrix n m α) (hA : IsUnit A.det) (hW : IsUnit W.det) :
    (A + U * W * V).det = W.det * A.det * (W⁻¹ + V * (A⁻¹) * U).det := by
    nth_rewrite 1 [← Matrix.mul_one A]
    rw [← Matrix.mul_nonsing_inv_cancel_left A (U * W * V), ←Matrix.mul_add, det_mul]
    nth_rewrite 1 [← Matrix.mul_one W⁻¹]
    rw [← Matrix.mul_nonsing_inv_cancel_left W⁻¹ (V * A⁻¹ * U), ←Matrix.mul_add, det_mul]
    rw [nonsing_inv_nonsing_inv]
    rw [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc]
    rw [det_one_add_mul_comm]
    rw [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc V]
    rw [mul_comm W.det A.det]
    rw [← mul_assoc]
    rw [mul_assoc A.det]
    rw [← det_mul]
    rw [mul_nonsing_inv]
    rw [det_one]
    rw [mul_one]
    exact hW
    exact hW
    exact isUnit_nonsing_inv_det W hW
    exact hA

theorem det_add_mul_mul {A : Matrix m m α} {W : Matrix n n α} (U : Matrix m n α)
    (V : Matrix n m α) (hA : IsUnit A.det) (hW : IsUnit W.det) :
    (A + U * W * V).det = W.det * A.det * (W⁻¹ + V * (A⁻¹) * U).det := by
  nth_rewrite 1 [← Matrix.mul_one A, ← Matrix.mul_one W⁻¹]
  rwa [←Matrix.mul_nonsing_inv_cancel_left A (U * W * V), ←Matrix.mul_add, det_mul,
    ←Matrix.mul_nonsing_inv_cancel_left W⁻¹ (V * A⁻¹ * U), ←Matrix.mul_add, det_mul,
    nonsing_inv_nonsing_inv, Matrix.mul_assoc, ←Matrix.mul_assoc, det_one_add_mul_comm,
    Matrix.mul_assoc, ←Matrix.mul_assoc V, mul_comm W.det A.det, ←mul_assoc, mul_assoc A.det,
    ←det_mul, mul_nonsing_inv, det_one, mul_one]
  exact hW
  exact isUnit_nonsing_inv_det W hW
  exact hA
