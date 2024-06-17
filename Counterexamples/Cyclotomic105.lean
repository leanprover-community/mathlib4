/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Tactic.NormNum.Prime

#align_import cyclotomic_105 from "leanprover-community/mathlib"@"328375597f2c0dd00522d9c2e5a33b6a6128feeb"

/-!
# Not all coefficients of cyclotomic polynomials are -1, 0, or 1

We show that not all coefficients of cyclotomic polynomials are equal to `0`, `-1` or `1`, in the
theorem `not_forall_coeff_cyclotomic_neg_one_zero_one`. We prove this with the counterexample
`coeff_cyclotomic_105 : coeff (cyclotomic 105 ℤ) 7 = -2`.
-/


open Nat (properDivisors)

open Finset

namespace Counterexample

section Computation

instance Nat.fact_prime_five : Fact (Nat.Prime 5) :=
  ⟨by norm_num⟩
#align counterexample.nat.fact_prime_five Counterexample.Nat.fact_prime_five

instance Nat.fact_prime_seven : Fact (Nat.Prime 7) :=
  ⟨by norm_num⟩
#align counterexample.nat.fact_prime_seven Counterexample.Nat.fact_prime_seven

theorem properDivisors_15 : Nat.properDivisors 15 = {1, 3, 5} :=
  rfl
#align counterexample.proper_divisors_15 Counterexample.properDivisors_15

theorem properDivisors_21 : Nat.properDivisors 21 = {1, 3, 7} :=
  rfl
#align counterexample.proper_divisors_21 Counterexample.properDivisors_21

theorem properDivisors_35 : Nat.properDivisors 35 = {1, 5, 7} :=
  rfl
#align counterexample.proper_divisors_35 Counterexample.properDivisors_35

set_option maxRecDepth 1024 in
theorem properDivisors_105 : Nat.properDivisors 105 = {1, 3, 5, 7, 15, 21, 35} :=
  rfl
#align counterexample.proper_divisors_105 Counterexample.properDivisors_105

end Computation

open Polynomial

theorem cyclotomic_3 : cyclotomic 3 ℤ = 1 + X + X ^ 2 := by
  simp only [cyclotomic_prime, sum_range_succ, range_one, sum_singleton, pow_zero, pow_one]
#align counterexample.cyclotomic_3 Counterexample.cyclotomic_3

theorem cyclotomic_5 : cyclotomic 5 ℤ = 1 + X + X ^ 2 + X ^ 3 + X ^ 4 := by
  simp only [cyclotomic_prime, sum_range_succ, range_one, sum_singleton, pow_zero, pow_one]
#align counterexample.cyclotomic_5 Counterexample.cyclotomic_5

theorem cyclotomic_7 : cyclotomic 7 ℤ = 1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 := by
  simp only [cyclotomic_prime, sum_range_succ, range_one, sum_singleton, pow_zero, pow_one]
#align counterexample.cyclotomic_7 Counterexample.cyclotomic_7

theorem cyclotomic_15 : cyclotomic 15 ℤ = 1 - X + X ^ 3 - X ^ 4 + X ^ 5 - X ^ 7 + X ^ 8 := by
  refine ((eq_cyclotomic_iff (by norm_num) _).2 ?_).symm
  rw [properDivisors_15, Finset.prod_insert _, Finset.prod_insert _, Finset.prod_singleton,
    cyclotomic_one, cyclotomic_3, cyclotomic_5]
  · ring
  repeat' norm_num
#align counterexample.cyclotomic_15 Counterexample.cyclotomic_15

theorem cyclotomic_21 :
    cyclotomic 21 ℤ = 1 - X + X ^ 3 - X ^ 4 + X ^ 6 - X ^ 8 + X ^ 9 - X ^ 11 + X ^ 12 := by
  refine ((eq_cyclotomic_iff (by norm_num) _).2 ?_).symm
  rw [properDivisors_21, Finset.prod_insert _, Finset.prod_insert _, Finset.prod_singleton,
    cyclotomic_one, cyclotomic_3, cyclotomic_7]
  · ring
  repeat' norm_num
#align counterexample.cyclotomic_21 Counterexample.cyclotomic_21

theorem cyclotomic_35 :
    cyclotomic 35 ℤ =
      1 - X + X ^ 5 - X ^ 6 + X ^ 7 - X ^ 8 + X ^ 10 - X ^ 11 + X ^ 12 - X ^ 13 + X ^ 14 - X ^ 16 +
        X ^ 17 - X ^ 18 + X ^ 19 - X ^ 23 + X ^ 24 := by
  refine ((eq_cyclotomic_iff (by norm_num) _).2 ?_).symm
  rw [properDivisors_35, Finset.prod_insert _, Finset.prod_insert _, Finset.prod_singleton,
    cyclotomic_one, cyclotomic_5, cyclotomic_7]
  · ring
  repeat' norm_num
#align counterexample.cyclotomic_35 Counterexample.cyclotomic_35

theorem cyclotomic_105 :
    cyclotomic 105 ℤ =
      1 + X + X ^ 2 - X ^ 5 - X ^ 6 - 2 * X ^ 7 - X ^ 8 - X ^ 9 + X ^ 12 + X ^ 13 + X ^ 14 +
        X ^ 15 + X ^ 16 + X ^ 17 - X ^ 20 - X ^ 22 - X ^ 24 - X ^ 26 - X ^ 28 + X ^ 31 + X ^ 32 +
        X ^ 33 + X ^ 34 + X ^ 35 + X ^ 36 - X ^ 39 - X ^ 40 - 2 * X ^ 41 - X ^ 42 - X ^ 43 +
        X ^ 46 + X ^ 47 + X ^ 48 := by
  refine ((eq_cyclotomic_iff (by norm_num) _).2 ?_).symm
  rw [properDivisors_105]
  repeat rw [Finset.prod_insert (α := ℕ) (β := ℤ[X])]
  · rw [Finset.prod_singleton, cyclotomic_one, cyclotomic_3, cyclotomic_5, cyclotomic_7,
      cyclotomic_15, cyclotomic_21, cyclotomic_35]
    ring
  repeat' norm_num
#align counterexample.cyclotomic_105 Counterexample.cyclotomic_105

theorem coeff_cyclotomic_105 : coeff (cyclotomic 105 ℤ) 7 = -2 := by
  simp [cyclotomic_105, coeff_one, coeff_X_of_ne_one]
#align counterexample.coeff_cyclotomic_105 Counterexample.coeff_cyclotomic_105

theorem not_forall_coeff_cyclotomic_neg_one_zero_one :
    ¬∀ n i, coeff (cyclotomic n ℤ) i ∈ ({-1, 0, 1} : Set ℤ) := by
  intro h
  specialize h 105 7
  rw [coeff_cyclotomic_105] at h
  norm_num at h
#align counterexample.not_forall_coeff_cyclotomic_neg_one_zero_one Counterexample.not_forall_coeff_cyclotomic_neg_one_zero_one

end Counterexample
