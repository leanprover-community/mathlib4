module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.LinearAlgebra.Complex.Module

@[expose] public section

-- Test that the `SMul ℚ ℂ` instance is correct.
example : (Complex.SMul.instSMulRealComplex : SMul ℚ ℂ) = (Algebra.toSMul : SMul ℚ ℂ) := by
  with_reducible_and_instances rfl
