/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
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

variable {Γ R : Type*} (A : Type*)

namespace HahnSeries

section BinomialPow

variable [LinearOrder Γ] [AddCommGroup Γ] [IsOrderedAddMonoid Γ] [CommRing R] [BinomialRing R]
[Module R Γ] [CommRing A] [Algebra R A]

/-- A Hahn series formally expanding `(X g - X g') ^ r` where `r` is an element of a binomial ring.
-/
def binomialPow (g g' : Γ) (r : R) : HahnSeries Γ A :=
  single (r • g) (1 : A) *
    (PowerSeries.heval ((single (g' - g)) (-1 : A)) (PowerSeries.binomialSeries A r))

@[simp]
theorem binomialPow_apply (g g' : Γ) (r : R) :
    binomialPow A g g' r = single (r • g) 1 *
      (PowerSeries.heval ((single (g' - g)) (-1 : A)) (PowerSeries.binomialSeries A r)) :=
  rfl

theorem binomialPow_apply_of_not_gt {g g' : Γ} (h : ¬ g < g') (r : R) :
    binomialPow A g g' r = single (r • g) (1 : A) := by
  cases subsingleton_or_nontrivial A
  · have _ : Subsingleton (HahnSeries Γ A) := instSubsingleton
    exact Subsingleton.elim _ _
  · have : ¬ 0 < (single (g' - g) (-1 : A)).orderTop := by
      rw [orderTop_single (neg_ne_zero.mpr one_ne_zero), WithTop.coe_pos, sub_pos]
      exact h
    rw [binomialPow_apply, PowerSeries.heval_of_orderTop_not_pos _ this]
    simp

theorem binomialPow_add {g g' : Γ} (r r' : R) :
    binomialPow A g g' r * binomialPow A g g' r' =
      binomialPow A g g' (r + r') := by
  simp only [binomialPow, PowerSeries.binomialSeries_add, PowerSeries.heval_mul, add_smul]
  rw [mul_left_comm, ← mul_assoc, ← mul_assoc, single_mul_single, mul_one, add_comm, ← mul_assoc]

theorem binomialPow_one {g g' : Γ} (h : g < g') :
    binomialPow A g g' (Nat.cast (R := R) 1) = ((single g) (1 : A) - (single g') 1) := by
  rw [binomialPow_apply, PowerSeries.binomialSeries_nat 1, pow_one, map_add,
    PowerSeries.heval_X _ (pos_orderTop_single_sub h (-1)),
    ← RingHom.map_one (f := PowerSeries.C A), PowerSeries.heval_C _, one_smul, mul_add, mul_one,
    single_mul_single, one_mul, single_neg, Nat.cast_one, one_smul, add_sub_cancel,
    sub_eq_add_neg]

theorem binomialPow_nat {g g' : Γ} (h : g < g') (n : ℕ) :
    binomialPow A g g' (n : R) = ((single g (1 : A)) - single g' 1) ^ n := by
  induction n with
  | zero => simp [PowerSeries.binomialSeries_zero, map_one]
  | succ n ih =>
    rw [Nat.cast_add, ← binomialPow_add, pow_add, ih, binomialPow_one A h, pow_one]

theorem binomialPow_one_add {g₀ g₁ g₂ : Γ} (h₀₁ : g₀ < g₁) (h₁₂ : g₁ < g₂) :
    binomialPow A g₀ g₁ (Nat.cast (R := R) 1) + binomialPow A g₁ g₂ (Nat.cast (R := R) 1) =
      binomialPow A g₀ g₂ (Nat.cast (R := R) 1) := by
  rw [binomialPow_one A h₀₁, binomialPow_one A h₁₂, binomialPow_one A (h₀₁.trans h₁₂),
    sub_add_sub_cancel]

end BinomialPow

end HahnSeries
