/-
Copyright (c) 2026 Scott Wesley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Wesley
-/
module

public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Skew adjoint matrices over ℂ

In this file we prove that skew adjoint and Hermitian matrices differ by a scalar factor of i.
-/

public section

namespace Matrix
variable {n : Type*} {M : Matrix n n ℂ}

/-- If `M` is self-adjoint, then multiplying `M` by an imaginary scalar `Complex.I * x` will result
in a Hermitian matrix `(Complex.I * x) • M`. -/
theorem im_smul_hermitian_mem_skewAdjoint (x : ℝ) (h : M.IsHermitian) :
    (Complex.I * x) • M ∈ skewAdjoint (Matrix n n ℂ) := by
  simp [skewAdjoint.mem_iff, h.isSelfAdjoint.star_eq]

/-- If `M` is Hermitian, then multiplying `M` by an imaginary scalar `Complex.I * x` will result in
a self-adjoint matrix `(Complex.I * x) • M`. -/ 
theorem im_smul_skewAdjoint_isHermitian (x : ℝ) (h : M ∈ skewAdjoint (Matrix n n ℂ)) :
    ((Complex.I * x) • M).IsHermitian := by
  simp [Matrix.IsHermitian, skewAdjoint.mem_iff.mp h, ←Matrix.star_eq_conjTranspose]

end Matrix
