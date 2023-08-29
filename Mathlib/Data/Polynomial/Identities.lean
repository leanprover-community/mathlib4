/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import Mathlib.Data.Polynomial.Derivative
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

#align_import data.polynomial.identities from "leanprover-community/mathlib"@"4e1eeebe63ac6d44585297e89c6e7ee5cbda487a"

/-!
# Theory of univariate polynomials

The main def is `Polynomial.binomExpansion`.
-/


noncomputable section

namespace Polynomial

open Polynomial

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
                -- 🎉 no goals
  | 1 => ⟨0, by simp⟩
                -- 🎉 no goals
  | n + 2 => by
    cases' (powAddExpansion x y (n + 1)) with z hz
    -- ⊢ { k // (x + y) ^ (n + 2) = x ^ (n + 2) + ↑(n + 2) * x ^ (n + 2 - 1) * y + k  …
    exists x * z + (n + 1) * x ^ n + z * y
    -- ⊢ (x + y) ^ (n + 2) = x ^ (n + 2) + ↑(n + 2) * x ^ (n + 2 - 1) * y + (x * z +  …
    calc
      (x + y) ^ (n + 2) = (x + y) * (x + y) ^ (n + 1) := by ring
      _ = (x + y) * (x ^ (n + 1) + ↑(n + 1) * x ^ (n + 1 - 1) * y + z * y ^ 2) := by rw [hz]
      _ = x ^ (n + 2) + ↑(n + 2) * x ^ (n + 1) * y + (x * z + (n + 1) * x ^ n + z * y) * y ^ 2 := by
        push_cast
        ring!
#align polynomial.pow_add_expansion Polynomial.powAddExpansion

variable [CommRing R]

private def polyBinomAux1 (x y : R) (e : ℕ) (a : R) :
    { k : R // a * (x + y) ^ e = a * (x ^ e + e * x ^ (e - 1) * y + k * y ^ 2) } := by
  exists (powAddExpansion x y e).val
  -- ⊢ a * (x + y) ^ e = a * (x ^ e + ↑e * x ^ (e - 1) * y + ↑(powAddExpansion x y  …
  congr
  -- ⊢ (x + y) ^ e = x ^ e + ↑e * x ^ (e - 1) * y + ↑(powAddExpansion x y e) * y ^ 2
  apply (powAddExpansion _ _ _).property
  -- 🎉 no goals

private theorem poly_binom_aux2 (f : R[X]) (x y : R) :
    f.eval (x + y) =
      f.sum fun e a => a * (x ^ e + e * x ^ (e - 1) * y + (polyBinomAux1 x y e a).val * y ^ 2) := by
  unfold eval; rw [eval₂_eq_sum]; congr with (n z)
  -- ⊢ eval₂ (RingHom.id R) (x + y) f = sum f fun e a => a * (x ^ e + ↑e * x ^ (e - …
               -- ⊢ (sum f fun e a => ↑(RingHom.id R) a * (x + y) ^ e) = sum f fun e a => a * (x …
                                  -- ⊢ ↑(RingHom.id R) z * (x + y) ^ n = z * (x ^ n + ↑n * x ^ (n - 1) * y + ↑(Poly …
  apply (polyBinomAux1 x y _ _).property
  -- 🎉 no goals

private theorem poly_binom_aux3 (f : R[X]) (x y : R) :
    f.eval (x + y) =
      ((f.sum fun e a => a * x ^ e) + f.sum fun e a => a * e * x ^ (e - 1) * y) +
        f.sum fun e a => a * (polyBinomAux1 x y e a).val * y ^ 2 := by
  rw [poly_binom_aux2]
  -- ⊢ (sum f fun e a => a * (x ^ e + ↑e * x ^ (e - 1) * y + ↑(Polynomial.polyBinom …
  simp [left_distrib, sum_add, mul_assoc]
  -- 🎉 no goals

/-- A polynomial `f` evaluated at `x + y` can be expressed as
the evaluation of `f` at `x`, plus `y` times the (polynomial) derivative of `f` at `x`,
plus some element `k : R` times `y^2`.
-/
def binomExpansion (f : R[X]) (x y : R) :
    { k : R // f.eval (x + y) = f.eval x + f.derivative.eval x * y + k * y ^ 2 } := by
  exists f.sum fun e a => a * (polyBinomAux1 x y e a).val
  -- ⊢ eval (x + y) f = eval x f + eval x (↑derivative f) * y + (sum f fun e a => a …
  rw [poly_binom_aux3]
  -- ⊢ (((sum f fun e a => a * x ^ e) + sum f fun e a => a * ↑e * x ^ (e - 1) * y)  …
  congr
  · rw [← eval_eq_sum]
    -- 🎉 no goals
  · rw [derivative_eval]
    -- ⊢ (sum f fun e a => a * ↑e * x ^ (e - 1) * y) = (sum f fun n a => a * ↑n * x ^ …
    exact Finset.sum_mul.symm
    -- 🎉 no goals
  · exact Finset.sum_mul.symm
    -- 🎉 no goals
#align polynomial.binom_expansion Polynomial.binomExpansion

/-- `x^n - y^n` can be expressed as `z * (x - y)` for some `z` in the ring.
-/
def powSubPowFactor (x y : R) : ∀ i : ℕ, { z : R // x ^ i - y ^ i = z * (x - y) }
  | 0 => ⟨0, by simp⟩
                -- 🎉 no goals
  | 1 => ⟨1, by simp⟩
                -- 🎉 no goals
  | k + 2 => by
    cases' @powSubPowFactor x y (k + 1) with z hz
    -- ⊢ { z // x ^ (k + 2) - y ^ (k + 2) = z * (x - y) }
    exists z * x + y ^ (k + 1)
    -- ⊢ x ^ (k + 2) - y ^ (k + 2) = (z * x + y ^ (k + 1)) * (x - y)
    linear_combination (norm := ring) x * hz
    -- 🎉 no goals
#align polynomial.pow_sub_pow_factor Polynomial.powSubPowFactor

/-- For any polynomial `f`, `f.eval x - f.eval y` can be expressed as `z * (x - y)`
for some `z` in the ring.
-/
def evalSubFactor (f : R[X]) (x y : R) : { z : R // f.eval x - f.eval y = z * (x - y) } := by
  refine' ⟨f.sum fun i r => r * (powSubPowFactor x y i).val, _⟩
  -- ⊢ eval x f - eval y f = (sum f fun i r => r * ↑(powSubPowFactor x y i)) * (x - …
  delta eval; rw [eval₂_eq_sum, eval₂_eq_sum];
  -- ⊢ eval₂ (RingHom.id R) x f - eval₂ (RingHom.id R) y f = (sum f fun i r => r *  …
              -- ⊢ ((sum f fun e a => ↑(RingHom.id R) a * x ^ e) - sum f fun e a => ↑(RingHom.i …
  simp only [sum, ← Finset.sum_sub_distrib, Finset.sum_mul]
  -- ⊢ (Finset.sum (support f) fun x_1 => ↑(RingHom.id R) (coeff f x_1) * x ^ x_1 - …
  dsimp
  -- ⊢ (Finset.sum (support f) fun x_1 => coeff f x_1 * x ^ x_1 - coeff f x_1 * y ^ …
  congr with i
  -- ⊢ coeff f i * x ^ i - coeff f i * y ^ i = coeff f i * ↑(powSubPowFactor x y i) …
  rw [mul_assoc, ← (powSubPowFactor x y _).prop, mul_sub]
  -- 🎉 no goals
#align polynomial.eval_sub_factor Polynomial.evalSubFactor

end Identities

end Polynomial
