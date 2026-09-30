/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Devon Tuma
-/
module
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Order.Filter.Polynomial

/-!
# Limits related to polynomial and rational functions

This file proves basic facts about limits of polynomial and rational functions.
The main result is `Polynomial.isEquivalent_atTop_lead`, which states that for
any polynomial `P` of degree `n` with leading coefficient `a`, the corresponding
polynomial function is equivalent to `a * x^n` as `x` goes to +∞.

We can then use this result to prove various limits for polynomial and rational
functions, depending on the degrees and leading coefficients of the considered
polynomials.
-/

public section

open Filter Finset Asymptotics

open scoped Topology

namespace Polynomial

variable {𝕜 : Type*} [NormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] (P Q : 𝕜[X])

variable [OrderTopology 𝕜]

theorem isEquivalent_atTop_lead :
    (fun x => eval x P) ~[atTop] fun x => P.leadingCoeff * x ^ P.natDegree := by
  by_cases h : P = 0
  · simp [h, IsEquivalent.refl]
  · simp only [Polynomial.eval_eq_sum_range, sum_range_succ]
    exact
      IsLittleO.add_isEquivalent
        (IsLittleO.fun_sum fun i hi =>
          IsLittleO.const_mul_left
            ((IsLittleO.const_mul_right fun hz => h <| leadingCoeff_eq_zero.mp hz) <|
              isLittleO_pow_pow_atTop_of_lt (mem_range.mp hi))
            _)
        IsEquivalent.refl

theorem isEquivalent_atBot_lead : P.eval ~[atBot] (P.leadingCoeff * · ^ P.natDegree) := by
  convert! (P.comp (-X)).isEquivalent_atTop_lead.comp_tendsto tendsto_neg_atBot_atTop using 2
  · simp
  · rw [Function.comp_apply, comp_neg_X_leadingCoeff_eq, ← mul_rotate]
    simp [natDegree_comp, ← mul_pow, mul_comm]

theorem isEquivalent_atTop_div :
    (fun x => eval x P / eval x Q) ~[atTop] fun x =>
      P.leadingCoeff / Q.leadingCoeff * x ^ (P.natDegree - Q.natDegree : ℤ) := by
  by_cases hP : P = 0
  · simp [hP, IsEquivalent.refl]
  by_cases hQ : Q = 0
  · simp [hQ, IsEquivalent.refl]
  refine
    (P.isEquivalent_atTop_lead.symm.div Q.isEquivalent_atTop_lead.symm).symm.trans
      (EventuallyEq.isEquivalent ((eventually_gt_atTop 0).mono fun x hx => ?_))
  simp [← div_mul_div_comm, zpow_sub₀ hx.ne.symm]

theorem isEquivalent_atBot_div :
    (fun x ↦ P.eval x / Q.eval x) ~[atBot] fun x ↦
      P.leadingCoeff / Q.leadingCoeff * x ^ (P.natDegree - Q.natDegree : ℤ) := by
  by_cases hP : P = 0
  · simp [hP, IsEquivalent.refl]
  by_cases hQ : Q = 0
  · simp [hQ, IsEquivalent.refl]
  refine
    (P.isEquivalent_atBot_lead.symm.div Q.isEquivalent_atBot_lead.symm).symm.trans
      (EventuallyEq.isEquivalent ((eventually_lt_atBot 0).mono fun x hx => ?_))
  simp [← div_mul_div_comm, zpow_sub₀ hx.ne]

theorem isLittleO_atTop_of_degree_lt (h : P.degree < Q.degree) : P.eval =o[atTop] Q.eval := by
  by_cases hp : P = 0
  · simp [hp]
  · have hq : Q ≠ 0 := ne_zero_of_degree_ge_degree h.le hp
    have hPQ : ∀ᶠ x in atTop, Q.eval x = 0 → P.eval x = 0 :=
      mem_of_superset (eventually_atTop_not_isRoot hq) fun x h h' ↦ absurd h' h
    exact isLittleO_of_tendsto' hPQ (div_tendsto_atTop_zero_of_degree_lt h)

theorem isLittleO_atBot_of_degree_lt (h : P.degree < Q.degree) : P.eval =o[atBot] Q.eval := by
  rw [← P.degree_comp_neg_X, ← Q.degree_comp_neg_X] at h
  convert! (isLittleO_atTop_of_degree_lt _ _ h).comp_tendsto tendsto_neg_atBot_atTop using 2
  all_goals simp

theorem isBigO_atTop_of_degree_le (h : P.degree ≤ Q.degree) : P.eval =O[atTop] Q.eval := by
  by_cases hp : P = 0
  · simpa [hp] using isBigO_zero Q.eval atTop
  · have hq : Q ≠ 0 := ne_zero_of_degree_ge_degree h hp
    have hPQ : ∀ᶠ x in atTop, Q.eval x = 0 → P.eval x = 0 :=
      mem_of_superset (eventually_atTop_not_isRoot hq) fun x h h' ↦ absurd h' h
    rcases le_iff_lt_or_eq.mp h with h | h
    · exact isBigO_of_div_tendsto_nhds hPQ 0 (div_tendsto_atTop_zero_of_degree_lt h)
    · exact isBigO_of_div_tendsto_nhds hPQ _ (div_tendsto_atTop_leadingCoeff_div_of_degree_eq h)

theorem isBigO_atBot_of_degree_le (h : P.degree ≤ Q.degree) : P.eval =O[atBot] Q.eval := by
  rw [← P.degree_comp_neg_X, ← Q.degree_comp_neg_X] at h
  convert! (isBigO_atTop_of_degree_le _ _ h).comp_tendsto tendsto_neg_atBot_atTop using 2
  all_goals simp

section Cobounded

open Bornology

variable {R : Type*} [NormedRing R] [NormMulClass R] {P Q : R[X]}

lemma isEquivalent_cobounded_leading_monomial :
    P.eval ~[cobounded R] (P.leadingCoeff * · ^ P.natDegree) := by
  by_cases h : P = 0
  · simp [h, IsEquivalent.refl]
  · simp only [eval_eq_sum_range, sum_range_succ]
    exact (IsLittleO.fun_sum fun i hi ↦
      ((isLittleO_pow_pow_cobounded_of_lt (mem_range.mp hi)).const_mul_right
        (leadingCoeff_ne_zero.mpr h)).const_mul_left _).add_isEquivalent .refl

theorem isLittleO_cobounded_of_degree_lt (h : P.degree < Q.degree) :
    P.eval =o[cobounded R] Q.eval := by
  by_cases hP : P = 0
  · simp [hP]
  · refine isEquivalent_cobounded_leading_monomial.trans_isLittleO <|
      ((IsLittleO.const_mul_right ?_ ?_).const_mul_left _).trans_isEquivalent
        isEquivalent_cobounded_leading_monomial.symm
    · exact leadingCoeff_ne_zero.mpr (ne_zero_of_degree_gt h)
    · exact isLittleO_pow_pow_cobounded_of_lt (natDegree_lt_natDegree hP h)

theorem isBigO_cobounded_of_degree_le (h : P.degree ≤ Q.degree) :
    P.eval =O[cobounded R] Q.eval := by
  by_cases hQ : Q.leadingCoeff = 0
  · aesop
  · refine isEquivalent_cobounded_leading_monomial.trans_isBigO <|
      ((IsBigO.const_mul_right hQ ?_).const_mul_left _).trans_isEquivalent
        isEquivalent_cobounded_leading_monomial.symm
    exact isBigO_pow_pow_cobounded_of_le (natDegree_le_natDegree h)

end Cobounded

/-- If `deg Q < deg P`, there are only finitely many integers `x` where `|P(x)| ≤ |Q(x)|`. -/
lemma finite_abs_eval_le_of_degree_lt {P Q : ℤ[X]} (h : Q.degree < P.degree) :
    {x | |P.eval x| ≤ |Q.eval x|}.Finite := by
  have o := isLittleO_cobounded_of_degree_lt h
  rw [IsOrderBornology.cobounded_eq, ← Int.cofinite_eq] at o
  have nr := eventually_cofinite_not_isRoot (ne_zero_of_degree_gt h)
  have key := o.eventuallyLT_norm_of_eventually_pos (nr.congr (.of_forall (by simp)))
  simp_rw [eventually_cofinite, not_lt, Int.norm_eq_abs] at key
  norm_cast at key

/-- If `Q(x) ∣ P(x)` at infinitely many integers `x` and `Q` is monic, `Q ∣ P`. -/
theorem dvd_of_infinite_eval_dvd_eval
    {P Q : ℤ[X]} (mQ : Q.Monic) (h : {a | Q.eval a ∣ P.eval a}.Infinite) : Q ∣ P := by
  have eqR := modByMonic_add_div P Q
  have degR := degree_modByMonic_lt P mQ
  rw [← modByMonic_eq_zero_iff_dvd mQ]
  set R := P %ₘ Q
  apply eq_zero_of_infinite_isRoot
  refine (h.sdiff (finite_abs_eval_le_of_degree_lt degR)).mono fun x mx ↦ ?_
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq, not_le] at mx
  rw [← eqR, eval_add, eval_mul, Int.dvd_add_self_mul, ← abs_dvd] at mx
  exact Int.eq_zero_of_abs_lt_dvd mx.1 mx.2

end Polynomial
