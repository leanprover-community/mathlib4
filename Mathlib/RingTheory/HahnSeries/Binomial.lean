/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.RingTheory.HahnSeries.PowerSeries
import Mathlib.RingTheory.HahnSeries.HEval
import Mathlib.RingTheory.PowerSeries.Binomial

/-!
# Hahn Series
We introduce generalized powers of certain binomials in Hahn series.

## Main Definitions
  * `HahnSeries.binomialPow` describes powers of a binomial of the form `single g 1 - single g' 1`,
  where the powers take values in a binomial ring.

## Main results
  *

## TODO
  * more about coefficients?

-/

open Finset BigOperators

suppress_compilation

variable {Γ R A : Type*}

namespace HahnSeries

section BinomialPow

variable [LinearOrder Γ] [AddCommGroup Γ] [IsOrderedAddMonoid Γ] [CommRing R] [BinomialRing R]
[Module R Γ] [CommRing A] [Algebra R A]

/-- A Hahn series formally expanding `(X g - X g') ^ r` where `r` is an element of a binomial ring.
-/
def binomialPow {g g' : Γ} (h : g < g') (r : R) : HahnSeries Γ A :=
  single (r • g) (1 : A) *
    (PowerSeries.heval (pos_orderTop_single_sub h (-1 : A)) (PowerSeries.binomialSeries A r))

theorem binomialPow_apply {g g' : Γ} (h : g < g') (r : R) :
    binomialPow h r = single (r • g) 1 *
      (PowerSeries.heval (pos_orderTop_single_sub h (-1 : A)) (PowerSeries.binomialSeries A r)) :=
  rfl

theorem binomialPow_add {g g' : Γ} (h : g < g') (r r' : R) :
    binomialPow h (r + r') = binomialPow (A := A) h r * binomialPow h r' := by
  simp only [binomialPow, add_smul, PowerSeries.binomialSeries_add, PowerSeries.heval_mul]
  rw [mul_left_comm _ ((single (r' • g)) 1), ← mul_assoc, ← mul_assoc, ← mul_assoc,
    single_mul_single, mul_one, add_comm, mul_assoc]

theorem binomialPow_one {g g' : Γ} (h : g < g') :
    binomialPow h (Nat.cast (R := R) 1) = ((single g) (1 : A) - (single g') 1) := by
  rw [binomialPow_apply, PowerSeries.binomialSeries_nat 1, pow_one, map_add,
        PowerSeries.heval_X (pos_orderTop_single_sub h (-1)),
        ← RingHom.map_one (f := PowerSeries.C A),
        PowerSeries.heval_C (pos_orderTop_single_sub h (-1)), one_smul, mul_add, mul_one,
        single_mul_single, one_mul, single_neg, Nat.cast_one, one_smul, add_sub_cancel,
        sub_eq_add_neg]

@[simp]
theorem binomialPow_nat {g g' : Γ} (h : g < g') (n : ℕ) :
    binomialPow h (n : R) = ((single g (1 : A)) - single g' 1) ^ n := by
  induction n with
  | zero => simp [PowerSeries.binomialSeries_zero, map_one, binomialPow_apply]
  | succ n ih =>
    rw [Nat.cast_add, binomialPow_add, pow_add, ih, binomialPow_one h, pow_one]

theorem binomialPow_one_add {g₀ g₁ g₂ : Γ} (h₀₁ : g₀ < g₁) (h₁₂ : g₁ < g₂) :
    binomialPow (A := A) h₀₁ (Nat.cast (R := R) 1) + binomialPow h₁₂ (Nat.cast (R := R) 1) =
      binomialPow (h₀₁.trans h₁₂) (Nat.cast (R := R) 1) := by
  rw [binomialPow_one h₀₁, binomialPow_one h₁₂, binomialPow_one (h₀₁.trans h₁₂), sub_add_sub_cancel]

end BinomialPow

end HahnSeries
