/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.Ring.Identities

/-!
# Theory of univariate polynomials

The main def is `Polynomial.binomExpansion`.
-/

@[expose] public section


noncomputable section

namespace Polynomial

universe u v w x y z

variable {R : Type u} {ι : Type x} {k : Type y} {A : Type z} {a : R}
  {n : ℕ}

section Identities

variable [CommRing R]

/-- A polynomial `f` evaluated at `x + y` can be expressed as
the evaluation of `f` at `x`, plus `y` times the (polynomial) derivative of `f` at `x`,
plus some element `k : R` times `y ^ 2`.
-/
theorem binomExpansion (f : R[X]) (x y : R) :
    ∃ k, f.eval (x + y) = f.eval x + f.derivative.eval x * y + k * y ^ 2 := by
  have hdvd : y ^ 2 ∣ f.eval (x + y) - (f.eval x + f.derivative.eval x * y) := by
    rw [eval_eq_sum, eval_eq_sum, derivative_eval]
    simp only [sum, Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun e _ => ?_
    obtain ⟨k, hk⟩ := powAddExpansion x y e
    exact ⟨f.coeff e * k, by rw [hk]; ring⟩
  obtain ⟨k, hk⟩ := hdvd
  exact ⟨k, by rw [eq_add_of_sub_eq hk]; ring⟩

/-- For any polynomial `f`, `f.eval x - f.eval y` can be expressed as `z * (x - y)`
for some `z` in the ring.
-/
theorem evalSubFactor (f : R[X]) (x y : R) : ∃ z, f.eval x - f.eval y = z * (x - y) := by
  refine ⟨f.sum fun i r => r * ∑ j ∈ Finset.range i, x ^ j * y ^ (i - 1 - j), ?_⟩
  delta eval; rw [eval₂_eq_sum, eval₂_eq_sum]
  simp only [sum, ← Finset.sum_sub_distrib, Finset.sum_mul]
  dsimp
  congr with i
  rw [mul_assoc, geom_sum₂_mul x y _, mul_sub]

end Identities

end Polynomial

@[deprecated powAddExpansion (since := "2026-09-10")]
alias Polynomial.powAddExpansion := powAddExpansion

@[deprecated powSubPowFactor (since := "2026-09-10")]
alias Polynomial.powSubPowFactor := powSubPowFactor
