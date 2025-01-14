/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module aux_results
-/
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.Harmonic.Bounds

noncomputable section

open scoped BigOperators

open Nat ArithmeticFunction Finset

namespace ArithmeticFunction.IsMultiplicative

variable {R : Type*}

end ArithmeticFunction.IsMultiplicative

--basic
theorem sum_over_dvd_ite {α : Type _} [Ring α] {P : ℕ} (hP : P ≠ 0) {n : ℕ} (hn : n ∣ P)
    {f : ℕ → α} : ∑ d in n.divisors, f d = ∑ d in P.divisors, if d ∣ n then f d else 0 := by
  rw [←Finset.sum_filter, Nat.divisors_filter_dvd_of_dvd hP hn]

--temp
@[to_additive]
theorem ite_prod_one {R ι : Type*} [CommMonoid R] {p : Prop} [Decidable p] (s : Finset ι)
    (f : ι → R) :
    (if p then (∏ x in s, f x) else 1) = ∏ x in s, if p then f x else 1 := by
  simp only [prod_ite_irrel, prod_const_one]

--basic
theorem conv_lambda_sq_larger_sum (f : ℕ → ℕ → ℕ → ℝ) (n : ℕ) :
    (∑ d in n.divisors,
        ∑ d1 in d.divisors,
          ∑ d2 in d.divisors, if d = Nat.lcm d1 d2 then f d1 d2 d else 0) =
      ∑ d in n.divisors,
        ∑ d1 in n.divisors,
          ∑ d2 in n.divisors, if d = Nat.lcm d1 d2 then f d1 d2 d else 0 := by
  apply sum_congr rfl; intro d hd
  rw [mem_divisors] at hd
  simp_rw [←Nat.divisors_filter_dvd_of_dvd hd.2 hd.1, sum_filter, ite_sum_zero, ← ite_and]
  congr with d1
  congr with d2
  congr
  simp +contextual [← and_assoc, eq_iff_iff, and_iff_right_iff_imp,
    Nat.dvd_lcm_left, Nat.dvd_lcm_right]


--selberg
theorem moebius_inv_dvd_lower_bound (l m : ℕ) (hm : Squarefree m) :
    (∑ d in m.divisors, if l ∣ d then μ d else 0) = if l = m then μ l else 0 := by
  have hm_pos : 0 < m := Nat.pos_of_ne_zero <| Squarefree.ne_zero hm
  revert hm
  revert m
  apply (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq_on {n | Squarefree n}
    (fun _ _ => Squarefree.squarefree_of_dvd)).mpr
  intro m hm_pos hm
  rw [sum_divisorsAntidiagonal' (f:= fun x y => μ x • if l=y then μ l else 0)]--
  by_cases hl : l ∣ m
  · rw [if_pos hl, sum_eq_single l]
    · have hmul : m / l * l = m := Nat.div_mul_cancel hl
      rw [if_pos rfl, smul_eq_mul, ←isMultiplicative_moebius.map_mul_of_coprime,
        hmul]
      apply coprime_of_squarefree_mul; rw [hmul]; exact hm
    · intro d _ hdl; rw[if_neg hdl.symm, smul_zero]
    · intro h; rw[mem_divisors] at h; exfalso; exact h ⟨hl, (Nat.ne_of_lt hm_pos).symm⟩
  · rw [if_neg hl, sum_eq_zero]; intro d hd
    rw [if_neg, smul_zero]
    by_contra h; rw [←h] at hd; exact hl (dvd_of_mem_divisors hd)

/-- Same as `moebius_inv_dvd_lower_bound` except we're summing over divisors of some
`P` divisible by `m` -/
theorem moebius_inv_dvd_lower_bound' {P : ℕ} (hP : Squarefree P) (l m : ℕ) (hm : m ∣ P) :
    (∑ d in P.divisors, if l ∣ d ∧ d ∣ m then μ d else 0) = if l = m then μ l else 0 := by
  rw [←moebius_inv_dvd_lower_bound _ _ (Squarefree.squarefree_of_dvd hm hP),
    sum_over_dvd_ite hP.ne_zero hm]
  simp_rw[ite_and, ←sum_filter, filter_comm]

theorem moebius_inv_dvd_lower_bound_real {P : ℕ} (hP : Squarefree P) (l m : ℕ) (hm : m ∣ P) :
    (∑ d in P.divisors, if l ∣ d ∧ d ∣ m then (μ d : ℝ) else 0) = if l = m then (μ l : ℝ) else 0
    := by
  norm_cast
  apply moebius_inv_dvd_lower_bound' hP l m hm

--basic
