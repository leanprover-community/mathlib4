/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Data.Complex.Module
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Trace.Defs

#align_import ring_theory.complex from "leanprover-community/mathlib"@"9015c511549dc77a0f8d6eba021d8ac4bba20c82"

/-! # Lemmas about `Algebra.trace` and `Algebra.norm` on `ℂ` -/


open Complex

theorem Algebra.leftMulMatrix_complex (z : ℂ) :
    Algebra.leftMulMatrix Complex.basisOneI z = !![z.re, -z.im; z.im, z.re] := by
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, Complex.coe_basisOneI_repr, Complex.coe_basisOneI, mul_re,
    mul_im, Matrix.of_apply]
  fin_cases j
  · simp only [Fin.mk_zero, Matrix.cons_val_zero, one_re, mul_one, one_im, mul_zero, sub_zero,
      zero_add]
    fin_cases i <;> rfl
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons, I_re, mul_zero, I_im, mul_one,
      zero_sub, add_zero]
    fin_cases i <;> rfl
#align algebra.left_mul_matrix_complex Algebra.leftMulMatrix_complex

theorem Algebra.trace_complex_apply (z : ℂ) : Algebra.trace ℝ ℂ z = 2 * z.re := by
  rw [Algebra.trace_eq_matrix_trace Complex.basisOneI, Algebra.leftMulMatrix_complex,
    Matrix.trace_fin_two]
  exact (two_mul _).symm
#align algebra.trace_complex_apply Algebra.trace_complex_apply

theorem Algebra.norm_complex_apply (z : ℂ) : Algebra.norm ℝ z = Complex.normSq z := by
  rw [Algebra.norm_eq_matrix_det Complex.basisOneI, Algebra.leftMulMatrix_complex,
    Matrix.det_fin_two, normSq_apply]
  simp
#align algebra.norm_complex_apply Algebra.norm_complex_apply

theorem Algebra.norm_complex_eq : Algebra.norm ℝ = normSq.toMonoidHom :=
  MonoidHom.ext Algebra.norm_complex_apply
#align algebra.norm_complex_eq Algebra.norm_complex_eq
