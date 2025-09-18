/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.RingTheory.HahnSeries.HEval
import Mathlib.RingTheory.PowerSeries.Binomial

/-!
# Hahn Series expansions of powers of binomials
We introduce generalized powers of certain binomials in Hahn series. Recall that
Hahn series are formal power series `Γ → A` where the exponent set `Γ` is partially ordered, and the
support is partially well-ordered. In this file, we consider the case where one has an action of a
binomial ring `R` on both `Γ` and `A`. Here, a binomial ring is a ring `R` that admits a uniquely
defined notion of binomial coefficient `Ring.choose r n` for all `r` in `R` and natural numbers `n`.
Using a binomial series expansion, this allows us to define generalized powers of the
form `(x - y)^r`, where `x` and `y` are Hahn series with singleton support.

One application of these binomial powers is to the theory of vertex algebras, where one often
encounters expressions in the abbreviated form `(x-y)^n A(x)B(y)`, where `n` is an integer,
`A : V → V((x))` and `B : V → V((y))` are linear maps to Laurent series spaces. This is expanded
as a linear map `V → V((x))((y))` once `(x-y)^n` is rewritten as `x^n(1 - y/x)^n` and `A(x)` is
extended to a map `V((y)) → V((x))((y))` by operating on coefficients.

## Main Definitions
  * `HahnSeries.binomialPow` describes powers of a binomial of the form `single g 1 - single g' 1`,
  where the powers take values in a binomial ring.

## Main results
  * `HahnSeries.binomialPow_add` asserts that adding exponents amounts to multiplying the
  corresponding formal powers of binomial series.
  * `HahnSeries.binomialPow_nat` asserts that natural number powers are given by the usual iterated
  multiplication of Hahn series.

## TODO
  * `HahnSeries.coeff_binomialPow_smul_add` :
    `(binomialPow A g g' r).coeff (r • g + n • (g' - g)) = Int.negOnePow n • Ring.choose r n • 1`
    (proved in a WIP PR)

-/

open Finset BigOperators

suppress_compilation

variable {Γ R : Type*} (A : Type*)

namespace HahnSeries

section BinomialPow

variable [LinearOrder Γ] [AddCommGroup Γ] [IsOrderedAddMonoid Γ] [CommRing R] [BinomialRing R]
[Module R Γ] [CommRing A] [Algebra R A]

/-- A Hahn series formally expanding `(X g + a X g') ^ r` where `r` is an element of a binomial ring
`R` and `a` is an element of an `R`-algebra. We require `g` and `g'` to lie in an ordered
`R`-module. -/
def binomialPow (g g' : Γ) (a : A) (r : R) : HahnSeries Γ A :=
  single (r • g) (1 : A) *
    (PowerSeries.heval ((single (g' - g)) (a : A)) (PowerSeries.binomialSeries A r))

theorem binomialPow_apply (g g' : Γ) (a : A) (r : R) :
    binomialPow A g g' a r = single (r • g) 1 *
      (PowerSeries.heval ((single (g' - g)) (a : A)) (PowerSeries.binomialSeries A r)) :=
  rfl

theorem binomialPow_apply_of_not_gt {g g' : Γ} (h : ¬ g < g') (a : A) (r : R) :
    binomialPow A g g' a r = single (r • g) (1 : A) := by
  by_cases ha : a = 0
  · simp [ha, binomialPow_apply]
  · have : ¬ 0 < (single (g' - g) (a : A)).orderTop := by
      rwa [orderTop_single ha, WithTop.coe_pos, sub_pos]
    simp [binomialPow_apply, PowerSeries.heval_of_orderTop_not_pos _ this]

@[simp]
theorem binomialPow_zero {g g' : Γ} (a : A) :
    binomialPow A g g' a (0 : R) = single 0 (1 : A) := by
  by_cases h : g < g'
  · simp [binomialPow_apply, OneHomClass.map_one]
  · simp [binomialPow_apply_of_not_gt A h a (0 : R)]

theorem binomialPow_add {g g' : Γ} (a : A) (r r' : R) :
    binomialPow A g g' a r * binomialPow A g g' a r' =
      binomialPow A g g' a (r + r') := by
  simp only [binomialPow, PowerSeries.binomialSeries_add, PowerSeries.heval_mul, add_smul]
  rw [mul_left_comm, ← mul_assoc, ← mul_assoc, single_mul_single, mul_one, add_comm, ← mul_assoc]

theorem binomialPow_one {g g' : Γ} (h : g < g') (a : A) :
    binomialPow A g g' a (Nat.cast (R := R) 1) = ((single g) (1 : A) + (single g') a) := by
  rw [binomialPow_apply, PowerSeries.binomialSeries_nat 1, pow_one, map_add,
    PowerSeries.heval_X _ (pos_orderTop_single_sub h a), ← RingHom.map_one PowerSeries.C,
    PowerSeries.heval_C _, one_smul, mul_add, mul_one, single_mul_single, one_mul,
    Nat.cast_one, one_smul, add_sub_cancel]

theorem binomialPow_nat {g g' : Γ} (h : g < g') (a : A) (n : ℕ) :
    binomialPow A g g' a (n : R) = ((single g (1 : A)) + single g' a) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add, ← binomialPow_add, pow_add, ih, binomialPow_one A h, pow_one]

theorem binomialPow_one_sub {g₀ g₁ g₂ : Γ} (h₀₁ : g₀ < g₁) (h₁₂ : g₁ < g₂) (a : A) :
    binomialPow A g₀ g₁ (a : A) (Nat.cast (R := R) 1) + (-a) •
      binomialPow A g₁ g₂ a (Nat.cast (R := R) 1) =
      binomialPow A g₀ g₂ (-a * a) (Nat.cast (R := R) 1) := by
  rw [binomialPow_one A h₀₁, binomialPow_one A h₁₂, binomialPow_one A (h₀₁.trans h₁₂), add_assoc,
    smul_add, ← add_assoc (single g₁ a), smul_single, ← single_add]
  simp

end BinomialPow

end HahnSeries
