/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Devon Tuma

! This file was ported from Lean 3 source module analysis.special_functions.polynomials
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Asymptotics.AsymptoticEquivalent
import Mathbin.Analysis.Asymptotics.SpecificAsymptotics
import Mathbin.Data.Polynomial.RingDivision

/-!
# Limits related to polynomial and rational functions

This file proves basic facts about limits of polynomial and rationals functions.
The main result is `eval_is_equivalent_at_top_eval_lead`, which states that for
any polynomial `P` of degree `n` with leading coefficient `a`, the corresponding
polynomial function is equivalent to `a * x^n` as `x` goes to +∞.

We can then use this result to prove various limits for polynomial and rational
functions, depending on the degrees and leading coefficients of the considered
polynomials.
-/


open Filter Finset Asymptotics

open Asymptotics Polynomial Topology

namespace Polynomial

variable {𝕜 : Type _} [NormedLinearOrderedField 𝕜] (P Q : 𝕜[X])

theorem eventually_no_roots (hP : P ≠ 0) : ∀ᶠ x in atTop, ¬P.IsRoot x :=
  atTop_le_cofinite <| (finite_setOf_isRoot hP).compl_mem_cofinite
#align polynomial.eventually_no_roots Polynomial.eventually_no_roots

variable [OrderTopology 𝕜]

section PolynomialAtTop

theorem isEquivalent_atTop_lead :
    (fun x => eval x P) ~[atTop] fun x => P.leadingCoeff * x ^ P.natDegree :=
  by
  by_cases h : P = 0
  · simp [h]
  · simp only [Polynomial.eval_eq_sum_range, sum_range_succ]
    exact
      is_o.add_is_equivalent
        (is_o.sum fun i hi =>
          is_o.const_mul_left
            ((is_o.const_mul_right fun hz => h <| leading_coeff_eq_zero.mp hz) <|
              is_o_pow_pow_at_top_of_lt (mem_range.mp hi))
            _)
        is_equivalent.refl
#align polynomial.is_equivalent_at_top_lead Polynomial.isEquivalent_atTop_lead

theorem tendsto_atTop_of_leadingCoeff_nonneg (hdeg : 0 < P.degree) (hnng : 0 ≤ P.leadingCoeff) :
    Tendsto (fun x => eval x P) atTop atTop :=
  P.isEquivalent_atTop_lead.symm.tendsto_atTop <|
    tendsto_const_mul_pow_atTop (natDegree_pos_iff_degree_pos.2 hdeg).ne' <|
      hnng.lt_of_ne' <| leadingCoeff_ne_zero.mpr <| ne_zero_of_degree_gt hdeg
#align polynomial.tendsto_at_top_of_leading_coeff_nonneg Polynomial.tendsto_atTop_of_leadingCoeff_nonneg

theorem tendsto_atTop_iff_leadingCoeff_nonneg :
    Tendsto (fun x => eval x P) atTop atTop ↔ 0 < P.degree ∧ 0 ≤ P.leadingCoeff :=
  by
  refine' ⟨fun h => _, fun h => tendsto_at_top_of_leading_coeff_nonneg P h.1 h.2⟩
  have : tendsto (fun x => P.leading_coeff * x ^ P.nat_degree) at_top at_top :=
    (is_equivalent_at_top_lead P).tendsto_atTop h
  rw [tendsto_const_mul_pow_at_top_iff, ← pos_iff_ne_zero, nat_degree_pos_iff_degree_pos] at this
  exact ⟨this.1, this.2.le⟩
#align polynomial.tendsto_at_top_iff_leading_coeff_nonneg Polynomial.tendsto_atTop_iff_leadingCoeff_nonneg

theorem tendsto_atBot_iff_leadingCoeff_nonpos :
    Tendsto (fun x => eval x P) atTop atBot ↔ 0 < P.degree ∧ P.leadingCoeff ≤ 0 := by
  simp only [← tendsto_neg_at_top_iff, ← eval_neg, tendsto_at_top_iff_leading_coeff_nonneg,
    degree_neg, leading_coeff_neg, neg_nonneg]
#align polynomial.tendsto_at_bot_iff_leading_coeff_nonpos Polynomial.tendsto_atBot_iff_leadingCoeff_nonpos

theorem tendsto_atBot_of_leadingCoeff_nonpos (hdeg : 0 < P.degree) (hnps : P.leadingCoeff ≤ 0) :
    Tendsto (fun x => eval x P) atTop atBot :=
  P.tendsto_atBot_iff_leadingCoeff_nonpos.2 ⟨hdeg, hnps⟩
#align polynomial.tendsto_at_bot_of_leading_coeff_nonpos Polynomial.tendsto_atBot_of_leadingCoeff_nonpos

theorem abs_tendsto_atTop (hdeg : 0 < P.degree) : Tendsto (fun x => abs <| eval x P) atTop atTop :=
  by
  cases' le_total 0 P.leading_coeff with hP hP
  · exact tendsto_abs_at_top_at_top.comp (P.tendsto_at_top_of_leading_coeff_nonneg hdeg hP)
  · exact tendsto_abs_at_bot_at_top.comp (P.tendsto_at_bot_of_leading_coeff_nonpos hdeg hP)
#align polynomial.abs_tendsto_at_top Polynomial.abs_tendsto_atTop

theorem abs_isBoundedUnder_iff :
    (IsBoundedUnder (· ≤ ·) atTop fun x => |eval x P|) ↔ P.degree ≤ 0 :=
  by
  refine'
    ⟨fun h => _, fun h =>
      ⟨|P.coeff 0|,
        eventually_map.mpr
          (eventually_of_forall
            (forall_imp (fun _ => le_of_eq) fun x =>
              congr_arg abs <| trans (congr_arg (eval x) (eq_C_of_degree_le_zero h)) eval_C))⟩⟩
  contrapose! h
  exact not_is_bounded_under_of_tendsto_at_top (abs_tendsto_at_top P h)
#align polynomial.abs_is_bounded_under_iff Polynomial.abs_isBoundedUnder_iff

theorem abs_tendsto_atTop_iff : Tendsto (fun x => abs <| eval x P) atTop atTop ↔ 0 < P.degree :=
  ⟨fun h => not_le.mp (mt (abs_isBoundedUnder_iff P).mpr (not_isBoundedUnder_of_tendsto_atTop h)),
    abs_tendsto_atTop P⟩
#align polynomial.abs_tendsto_at_top_iff Polynomial.abs_tendsto_atTop_iff

theorem tendsto_nhds_iff {c : 𝕜} :
    Tendsto (fun x => eval x P) atTop (𝓝 c) ↔ P.leadingCoeff = c ∧ P.degree ≤ 0 :=
  by
  refine' ⟨fun h => _, fun h => _⟩
  · have := P.is_equivalent_at_top_lead.tendsto_nhds h
    by_cases hP : P.leading_coeff = 0
    · simp only [hP, MulZeroClass.zero_mul, tendsto_const_nhds_iff] at this
      refine' ⟨trans hP this, by simp [leading_coeff_eq_zero.1 hP]⟩
    · rw [tendsto_const_mul_pow_nhds_iff hP, nat_degree_eq_zero_iff_degree_le_zero] at this
      exact this.symm
  · refine' P.is_equivalent_at_top_lead.symm.tendsto_nhds _
    have : P.nat_degree = 0 := nat_degree_eq_zero_iff_degree_le_zero.2 h.2
    simp only [h.1, this, pow_zero, mul_one]
    exact tendsto_const_nhds
#align polynomial.tendsto_nhds_iff Polynomial.tendsto_nhds_iff

end PolynomialAtTop

section PolynomialDivAtTop

theorem isEquivalent_atTop_div :
    (fun x => eval x P / eval x Q) ~[atTop] fun x =>
      P.leadingCoeff / Q.leadingCoeff * x ^ (P.natDegree - Q.natDegree : ℤ) :=
  by
  by_cases hP : P = 0
  · simp [hP]
  by_cases hQ : Q = 0
  · simp [hQ]
  refine'
    (P.is_equivalent_at_top_lead.symm.div Q.is_equivalent_at_top_lead.symm).symm.trans
      (eventually_eq.is_equivalent ((eventually_gt_at_top 0).mono fun x hx => _))
  simp [← div_mul_div_comm, hP, hQ, zpow_sub₀ hx.ne.symm]
#align polynomial.is_equivalent_at_top_div Polynomial.isEquivalent_atTop_div

theorem div_tendsto_zero_of_degree_lt (hdeg : P.degree < Q.degree) :
    Tendsto (fun x => eval x P / eval x Q) atTop (𝓝 0) :=
  by
  by_cases hP : P = 0
  · simp [hP, tendsto_const_nhds]
  rw [← nat_degree_lt_nat_degree_iff hP] at hdeg
  refine' (is_equivalent_at_top_div P Q).symm.tendsto_nhds _
  rw [← MulZeroClass.mul_zero]
  refine' (tendsto_zpow_atTop_zero _).const_mul _
  linarith
#align polynomial.div_tendsto_zero_of_degree_lt Polynomial.div_tendsto_zero_of_degree_lt

theorem div_tendsto_zero_iff_degree_lt (hQ : Q ≠ 0) :
    Tendsto (fun x => eval x P / eval x Q) atTop (𝓝 0) ↔ P.degree < Q.degree :=
  by
  refine' ⟨fun h => _, div_tendsto_zero_of_degree_lt P Q⟩
  by_cases hPQ : P.leading_coeff / Q.leading_coeff = 0
  · simp only [div_eq_mul_inv, inv_eq_zero, mul_eq_zero] at hPQ
    cases' hPQ with hP0 hQ0
    · rw [leading_coeff_eq_zero.1 hP0, degree_zero]
      exact bot_lt_iff_ne_bot.2 fun hQ' => hQ (degree_eq_bot.1 hQ')
    · exact absurd (leading_coeff_eq_zero.1 hQ0) hQ
  · have := (is_equivalent_at_top_div P Q).tendsto_nhds h
    rw [tendsto_const_mul_zpow_atTop_nhds_iff hPQ] at this
    cases' this with h h
    · exact absurd h.2 hPQ
    · rw [sub_lt_iff_lt_add, zero_add, Int.ofNat_lt] at h
      exact degree_lt_degree h.1
#align polynomial.div_tendsto_zero_iff_degree_lt Polynomial.div_tendsto_zero_iff_degree_lt

theorem div_tendsto_leadingCoeff_div_of_degree_eq (hdeg : P.degree = Q.degree) :
    Tendsto (fun x => eval x P / eval x Q) atTop (𝓝 <| P.leadingCoeff / Q.leadingCoeff) :=
  by
  refine' (is_equivalent_at_top_div P Q).symm.tendsto_nhds _
  rw [show (P.nat_degree : ℤ) = Q.nat_degree by simp [hdeg, nat_degree]]
  simp [tendsto_const_nhds]
#align polynomial.div_tendsto_leading_coeff_div_of_degree_eq Polynomial.div_tendsto_leadingCoeff_div_of_degree_eq

theorem div_tendsto_atTop_of_degree_gt' (hdeg : Q.degree < P.degree)
    (hpos : 0 < P.leadingCoeff / Q.leadingCoeff) :
    Tendsto (fun x => eval x P / eval x Q) atTop atTop :=
  by
  have hQ : Q ≠ 0 := fun h =>
    by
    simp only [h, div_zero, leading_coeff_zero] at hpos
    linarith
  rw [← nat_degree_lt_nat_degree_iff hQ] at hdeg
  refine' (is_equivalent_at_top_div P Q).symm.tendsto_atTop _
  apply tendsto.const_mul_at_top hpos
  apply tendsto_zpow_atTop_atTop
  linarith
#align polynomial.div_tendsto_at_top_of_degree_gt' Polynomial.div_tendsto_atTop_of_degree_gt'

theorem div_tendsto_atTop_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q ≠ 0)
    (hnng : 0 ≤ P.leadingCoeff / Q.leadingCoeff) :
    Tendsto (fun x => eval x P / eval x Q) atTop atTop :=
  have ratio_pos : 0 < P.leadingCoeff / Q.leadingCoeff :=
    lt_of_le_of_ne hnng
      (div_ne_zero (fun h => ne_zero_of_degree_gt hdeg <| leadingCoeff_eq_zero.mp h) fun h =>
          hQ <| leadingCoeff_eq_zero.mp h).symm
  div_tendsto_atTop_of_degree_gt' P Q hdeg ratio_pos
#align polynomial.div_tendsto_at_top_of_degree_gt Polynomial.div_tendsto_atTop_of_degree_gt

theorem div_tendsto_atBot_of_degree_gt' (hdeg : Q.degree < P.degree)
    (hneg : P.leadingCoeff / Q.leadingCoeff < 0) :
    Tendsto (fun x => eval x P / eval x Q) atTop atBot :=
  by
  have hQ : Q ≠ 0 := fun h =>
    by
    simp only [h, div_zero, leading_coeff_zero] at hneg
    linarith
  rw [← nat_degree_lt_nat_degree_iff hQ] at hdeg
  refine' (is_equivalent_at_top_div P Q).symm.tendsto_atBot _
  apply tendsto.neg_const_mul_at_top hneg
  apply tendsto_zpow_atTop_atTop
  linarith
#align polynomial.div_tendsto_at_bot_of_degree_gt' Polynomial.div_tendsto_atBot_of_degree_gt'

theorem div_tendsto_atBot_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q ≠ 0)
    (hnps : P.leadingCoeff / Q.leadingCoeff ≤ 0) :
    Tendsto (fun x => eval x P / eval x Q) atTop atBot :=
  have ratio_neg : P.leadingCoeff / Q.leadingCoeff < 0 :=
    lt_of_le_of_ne hnps
      (div_ne_zero (fun h => ne_zero_of_degree_gt hdeg <| leadingCoeff_eq_zero.mp h) fun h =>
        hQ <| leadingCoeff_eq_zero.mp h)
  div_tendsto_atBot_of_degree_gt' P Q hdeg ratio_neg
#align polynomial.div_tendsto_at_bot_of_degree_gt Polynomial.div_tendsto_atBot_of_degree_gt

theorem abs_div_tendsto_atTop_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q ≠ 0) :
    Tendsto (fun x => |eval x P / eval x Q|) atTop atTop :=
  by
  by_cases h : 0 ≤ P.leading_coeff / Q.leading_coeff
  · exact tendsto_abs_at_top_at_top.comp (P.div_tendsto_at_top_of_degree_gt Q hdeg hQ h)
  · push_neg  at h
    exact tendsto_abs_at_bot_at_top.comp (P.div_tendsto_at_bot_of_degree_gt Q hdeg hQ h.le)
#align polynomial.abs_div_tendsto_at_top_of_degree_gt Polynomial.abs_div_tendsto_atTop_of_degree_gt

end PolynomialDivAtTop

theorem isBigO_of_degree_le (h : P.degree ≤ Q.degree) :
    (fun x => eval x P) =O[atTop] fun x => eval x Q :=
  by
  by_cases hp : P = 0
  · simpa [hp] using is_O_zero (fun x => eval x Q) at_top
  · have hq : Q ≠ 0 := ne_zero_of_degree_ge_degree h hp
    have hPQ : ∀ᶠ x : 𝕜 in at_top, eval x Q = 0 → eval x P = 0 :=
      Filter.mem_of_superset (Polynomial.eventually_no_roots Q hq) fun x h h' => absurd h' h
    cases' le_iff_lt_or_eq.mp h with h h
    · exact is_O_of_div_tendsto_nhds hPQ 0 (div_tendsto_zero_of_degree_lt P Q h)
    · exact is_O_of_div_tendsto_nhds hPQ _ (div_tendsto_leading_coeff_div_of_degree_eq P Q h)
#align polynomial.is_O_of_degree_le Polynomial.isBigO_of_degree_le

end Polynomial

