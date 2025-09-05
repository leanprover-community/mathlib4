/-
Copyright (c) 2025 Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang
-/
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Krull dimension of polynomial ring

We show that not all commutative rings `R` satisfy
`ringKrullDim (Polynomial R) = ringKrullDim R + 1`,
following the construction in the reference link.

## References

<https://math.stackexchange.com/questions/1267419/examples-of-rings-whose-polynomial-rings-have-large-dimension>
-/

namespace Counterexample

namespace CounterexampleDimensionPolynomial

open PowerSeries

variable (k : Type*) [Field k]

abbrev A := (RatFunc.C (K := k)).range.comap constantCoeff

instance : IsLocalRing (A k) := sorry

theorem ringKrullDim_A_eq_one : ringKrullDim (A k) = 1 := by
  sorry

theorem ringKrullDim_polynomial_A_eq_three : ringKrullDim (Polynomial (A k)) = 3 := by sorry

end CounterexampleDimensionPolynomial

end Counterexample
