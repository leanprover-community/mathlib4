-- Live WebAssembly version of Lean
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Polynomial.Basic


universe u u' v w

open BigOperators



variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

namespace Matrix

variable {M N : Matrix m n α}



lemma matrix_determinant_lemma (A: Matrix m m R)(B: Matrix n n R)
  (U: Matrix m n R)(V: Matrix  n m R) {hA: isNonZero A.det}:
  (A + dotProduct U V).det = A.det * (1 + dotProduct V (A⁻¹) * U).det := begin
  nth_rewrite 0 ← matrix.mul_one A,
  rwa [← mul_nonsing_inv_cancel_left A (U⬝V), ← matrix.mul_add A,
    det_mul, ← matrix.mul_assoc, det_one_add_mul_comm, ← matrix.mul_assoc],
