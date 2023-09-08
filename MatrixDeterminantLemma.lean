import Mathlib
import Mathlib.LinearAlgebra.Matrix.SchurComplement

variable (m n: Type)
variable [Fintype m][Fintype n][DecidableEq m][DecidableEq n]


variable (R: Type)
variable [Field R][DecidableEq R]

namespace Matrix
open Matrix

lemma MatrixDeterminantLemma
  (A: Matrix m m R)(U: Matrix m n R)(V: Matrix n m R)(hA: IsUnit A.det):
  (A + U * V).det = A.det*(1 + V * (A⁻¹) * U).det := by
  nth_rewrite 1 [← Matrix.mul_one A]
  rwa [← Matrix.mul_nonsing_inv_cancel_left A (U * V), ←Matrix.mul_add, det_mul,
    ←Matrix.mul_assoc, det_one_add_mul_comm, ←Matrix.mul_assoc]
