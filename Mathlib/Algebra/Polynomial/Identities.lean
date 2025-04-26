/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Theory of univariate polynomials

The main def is `Polynomial.binomExpansion`.
-/


noncomputable section

namespace Polynomial

universe u v w x y z

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type x} {k : Type y} {A : Type z} {a b : R}
  {m n : ℕ}

section Identities

/- @TODO: `powAddExpansion` and `powSubPowFactor` are not specific to polynomials.
  These belong somewhere else. But not in group_power because they depend on tactic.ring_exp

  Maybe use `Data.Nat.Choose` to prove it.
-/
/-- `(x + y)^n` can be expressed as `x^n + n*x^(n-1)*y + k * y^2` for some `k` in the ring.
-/
def powAddExpansion {R : Type*} [CommSemiring R] (x y : R) :
    ∀ n : ℕ, { k // (x + y) ^ n = x ^ n + n * x ^ (n - 1) * y + k * y ^ 2 }
  | 0 => ⟨0, by simp⟩
  | 1 => ⟨0, by simp⟩
  | n + 2 => by
    obtain ⟨z, hz⟩ := (powAddExpansion x y (n + 1))
    exists x * z + (n + 1) * x ^ n + z * y
    calc
      (x + y) ^ (n + 2) = (x + y) * (x + y) ^ (n + 1) := by ring
      _ = (x + y) * (x ^ (n + 1) + ↑(n + 1) * x ^ (n + 1 - 1) * y + z * y ^ 2) := by rw [hz]
      _ = x ^ (n + 2) + ↑(n + 2) * x ^ (n + 1) * y + (x * z + (n + 1) * x ^ n + z * y) * y ^ 2 := by
        push_cast
        ring!

variable [CommRing R]

private def polyBinomAux1 (x y : R) (e : ℕ) (a : R) :
    { k : R // a * (x + y) ^ e = a * (x ^ e + e * x ^ (e - 1) * y + k * y ^ 2) } := by
  exists (powAddExpansion x y e).val
  congr
  apply (powAddExpansion _ _ _).property

private theorem poly_binom_aux2 (f : R[X]) (x y : R) :
    f.eval (x + y) =
      f.sum fun e a => a * (x ^ e + e * x ^ (e - 1) * y + (polyBinomAux1 x y e a).val * y ^ 2) := by
  unfold eval; rw [eval₂_eq_sum]; congr with (n z)
  apply (polyBinomAux1 x y _ _).property

private theorem poly_binom_aux3 (f : R[X]) (x y : R) :
    f.eval (x + y) =
      ((f.sum fun e a => a * x ^ e) + f.sum fun e a => a * e * x ^ (e - 1) * y) +
        f.sum fun e a => a * (polyBinomAux1 x y e a).val * y ^ 2 := by
  rw [poly_binom_aux2]
  simp [left_distrib, sum_add, mul_assoc]

/-- A polynomial `f` evaluated at `x + y` can be expressed as
the evaluation of `f` at `x`, plus `y` times the (polynomial) derivative of `f` at `x`,
plus some element `k : R` times `y^2`.
-/
def binomExpansion (f : R[X]) (x y : R) :
    { k : R // f.eval (x + y) = f.eval x + f.derivative.eval x * y + k * y ^ 2 } := by
  exists f.sum fun e a => a * (polyBinomAux1 x y e a).val
  rw [poly_binom_aux3]
  congr
  · rw [← eval_eq_sum]
  · rw [derivative_eval]
    exact (Finset.sum_mul ..).symm
  · exact (Finset.sum_mul ..).symm

/-- `x^n - y^n` can be expressed as `z * (x - y)` for some `z` in the ring.
-/
def powSubPowFactor (x y : R) : ∀ i : ℕ, { z : R // x ^ i - y ^ i = z * (x - y) }
  | 0 => ⟨0, by simp⟩
  | 1 => ⟨1, by simp⟩
  | k + 2 => by
    obtain ⟨z, hz⟩ := @powSubPowFactor x y (k + 1)
    exists z * x + y ^ (k + 1)
    linear_combination (norm := ring) x * hz

/-- For any polynomial `f`, `f.eval x - f.eval y` can be expressed as `z * (x - y)`
for some `z` in the ring.
-/
def evalSubFactor (f : R[X]) (x y : R) : { z : R // f.eval x - f.eval y = z * (x - y) } := by
  refine ⟨f.sum fun i r => r * (powSubPowFactor x y i).val, ?_⟩
  delta eval; rw [eval₂_eq_sum, eval₂_eq_sum]
  simp only [sum, ← Finset.sum_sub_distrib, Finset.sum_mul]
  dsimp
  congr with i
  rw [mul_assoc, ← (powSubPowFactor x y _).prop, mul_sub]

end Identities

end Polynomial
