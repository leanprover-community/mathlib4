/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Devon Tuma
-/
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Data.Polynomial.RingDivision

#align_import analysis.special_functions.polynomials from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

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

variable {𝕜 : Type*} [NormedLinearOrderedField 𝕜] (P Q : 𝕜[X])

theorem eventually_no_roots (hP : P ≠ 0) : ∀ᶠ x in atTop, ¬P.IsRoot x :=
  atTop_le_cofinite <| (finite_setOf_isRoot hP).compl_mem_cofinite
#align polynomial.eventually_no_roots Polynomial.eventually_no_roots

variable [OrderTopology 𝕜]

section PolynomialAtTop

theorem isEquivalent_atTop_lead :
    (fun x => eval x P) ~[atTop] fun x => P.leadingCoeff * x ^ P.natDegree := by
  by_cases h : P = 0
  -- ⊢ (fun x => eval x P) ~[atTop] fun x => leadingCoeff P * x ^ natDegree P
  · simp [h, IsEquivalent.refl]
    -- 🎉 no goals
  · simp only [Polynomial.eval_eq_sum_range, sum_range_succ]
    -- ⊢ (fun x => (Finset.sum (range (natDegree P)) fun i => coeff P i * x ^ i) + co …
    exact
      IsLittleO.add_isEquivalent
        (IsLittleO.sum fun i hi =>
          IsLittleO.const_mul_left
            ((IsLittleO.const_mul_right fun hz => h <| leadingCoeff_eq_zero.mp hz) <|
              isLittleO_pow_pow_atTop_of_lt (mem_range.mp hi))
            _)
        IsEquivalent.refl
#align polynomial.is_equivalent_at_top_lead Polynomial.isEquivalent_atTop_lead

theorem tendsto_atTop_of_leadingCoeff_nonneg (hdeg : 0 < P.degree) (hnng : 0 ≤ P.leadingCoeff) :
    Tendsto (fun x => eval x P) atTop atTop :=
  P.isEquivalent_atTop_lead.symm.tendsto_atTop <|
    tendsto_const_mul_pow_atTop (natDegree_pos_iff_degree_pos.2 hdeg).ne' <|
      hnng.lt_of_ne' <| leadingCoeff_ne_zero.mpr <| ne_zero_of_degree_gt hdeg
#align polynomial.tendsto_at_top_of_leading_coeff_nonneg Polynomial.tendsto_atTop_of_leadingCoeff_nonneg

theorem tendsto_atTop_iff_leadingCoeff_nonneg :
    Tendsto (fun x => eval x P) atTop atTop ↔ 0 < P.degree ∧ 0 ≤ P.leadingCoeff := by
  refine' ⟨fun h => _, fun h => tendsto_atTop_of_leadingCoeff_nonneg P h.1 h.2⟩
  -- ⊢ 0 < degree P ∧ 0 ≤ leadingCoeff P
  have : Tendsto (fun x => P.leadingCoeff * x ^ P.natDegree) atTop atTop :=
    (isEquivalent_atTop_lead P).tendsto_atTop h
  rw [tendsto_const_mul_pow_atTop_iff, ← pos_iff_ne_zero, natDegree_pos_iff_degree_pos] at this
  -- ⊢ 0 < degree P ∧ 0 ≤ leadingCoeff P
  exact ⟨this.1, this.2.le⟩
  -- 🎉 no goals
#align polynomial.tendsto_at_top_iff_leading_coeff_nonneg Polynomial.tendsto_atTop_iff_leadingCoeff_nonneg

theorem tendsto_atBot_iff_leadingCoeff_nonpos :
    Tendsto (fun x => eval x P) atTop atBot ↔ 0 < P.degree ∧ P.leadingCoeff ≤ 0 := by
  simp only [← tendsto_neg_atTop_iff, ← eval_neg, tendsto_atTop_iff_leadingCoeff_nonneg,
    degree_neg, leadingCoeff_neg, neg_nonneg]
#align polynomial.tendsto_at_bot_iff_leading_coeff_nonpos Polynomial.tendsto_atBot_iff_leadingCoeff_nonpos

theorem tendsto_atBot_of_leadingCoeff_nonpos (hdeg : 0 < P.degree) (hnps : P.leadingCoeff ≤ 0) :
    Tendsto (fun x => eval x P) atTop atBot :=
  P.tendsto_atBot_iff_leadingCoeff_nonpos.2 ⟨hdeg, hnps⟩
#align polynomial.tendsto_at_bot_of_leading_coeff_nonpos Polynomial.tendsto_atBot_of_leadingCoeff_nonpos

theorem abs_tendsto_atTop (hdeg : 0 < P.degree) :
    Tendsto (fun x => abs <| eval x P) atTop atTop := by
  cases' le_total 0 P.leadingCoeff with hP hP
  -- ⊢ Tendsto (fun x => |eval x P|) atTop atTop
  · exact tendsto_abs_atTop_atTop.comp (P.tendsto_atTop_of_leadingCoeff_nonneg hdeg hP)
    -- 🎉 no goals
  · exact tendsto_abs_atBot_atTop.comp (P.tendsto_atBot_of_leadingCoeff_nonpos hdeg hP)
    -- 🎉 no goals
#align polynomial.abs_tendsto_at_top Polynomial.abs_tendsto_atTop

theorem abs_isBoundedUnder_iff :
    (IsBoundedUnder (· ≤ ·) atTop fun x => |eval x P|) ↔ P.degree ≤ 0 := by
  refine' ⟨fun h => _, fun h => ⟨|P.coeff 0|, eventually_map.mpr (eventually_of_forall
    (forall_imp (fun _ => le_of_eq) fun x => congr_arg abs <| _root_.trans (congr_arg (eval x)
    (eq_C_of_degree_le_zero h)) eval_C))⟩⟩
  contrapose! h
  -- ⊢ ¬IsBoundedUnder (fun x x_1 => x ≤ x_1) atTop fun x => |eval x P|
  exact not_isBoundedUnder_of_tendsto_atTop (abs_tendsto_atTop P h)
  -- 🎉 no goals
#align polynomial.abs_is_bounded_under_iff Polynomial.abs_isBoundedUnder_iff

theorem abs_tendsto_atTop_iff : Tendsto (fun x => abs <| eval x P) atTop atTop ↔ 0 < P.degree :=
  ⟨fun h => not_le.mp (mt (abs_isBoundedUnder_iff P).mpr (not_isBoundedUnder_of_tendsto_atTop h)),
    abs_tendsto_atTop P⟩
#align polynomial.abs_tendsto_at_top_iff Polynomial.abs_tendsto_atTop_iff

theorem tendsto_nhds_iff {c : 𝕜} :
    Tendsto (fun x => eval x P) atTop (𝓝 c) ↔ P.leadingCoeff = c ∧ P.degree ≤ 0 := by
  refine' ⟨fun h => _, fun h => _⟩
  -- ⊢ leadingCoeff P = c ∧ degree P ≤ 0
  · have := P.isEquivalent_atTop_lead.tendsto_nhds h
    -- ⊢ leadingCoeff P = c ∧ degree P ≤ 0
    by_cases hP : P.leadingCoeff = 0
    -- ⊢ leadingCoeff P = c ∧ degree P ≤ 0
    · simp only [hP, zero_mul, tendsto_const_nhds_iff] at this
      -- ⊢ leadingCoeff P = c ∧ degree P ≤ 0
      refine' ⟨_root_.trans hP this, by simp [leadingCoeff_eq_zero.1 hP]⟩
      -- 🎉 no goals
    · rw [tendsto_const_mul_pow_nhds_iff hP, natDegree_eq_zero_iff_degree_le_zero] at this
      -- ⊢ leadingCoeff P = c ∧ degree P ≤ 0
      exact this.symm
      -- 🎉 no goals
  · refine' P.isEquivalent_atTop_lead.symm.tendsto_nhds _
    -- ⊢ Tendsto (fun x => leadingCoeff P * x ^ natDegree P) atTop (𝓝 c)
    have : P.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.2 h.2
    -- ⊢ Tendsto (fun x => leadingCoeff P * x ^ natDegree P) atTop (𝓝 c)
    simp only [h.1, this, pow_zero, mul_one]
    -- ⊢ Tendsto (fun x => c) atTop (𝓝 c)
    exact tendsto_const_nhds
    -- 🎉 no goals
#align polynomial.tendsto_nhds_iff Polynomial.tendsto_nhds_iff

end PolynomialAtTop

section PolynomialDivAtTop

theorem isEquivalent_atTop_div :
    (fun x => eval x P / eval x Q) ~[atTop] fun x =>
      P.leadingCoeff / Q.leadingCoeff * x ^ (P.natDegree - Q.natDegree : ℤ) := by
  by_cases hP : P = 0
  -- ⊢ (fun x => eval x P / eval x Q) ~[atTop] fun x => leadingCoeff P / leadingCoe …
  · simp [hP, IsEquivalent.refl]
    -- 🎉 no goals
  by_cases hQ : Q = 0
  -- ⊢ (fun x => eval x P / eval x Q) ~[atTop] fun x => leadingCoeff P / leadingCoe …
  · simp [hQ, IsEquivalent.refl]
    -- 🎉 no goals
  refine'
    (P.isEquivalent_atTop_lead.symm.div Q.isEquivalent_atTop_lead.symm).symm.trans
      (EventuallyEq.isEquivalent ((eventually_gt_atTop 0).mono fun x hx => _))
  simp [← div_mul_div_comm, hP, hQ, zpow_sub₀ hx.ne.symm]
  -- 🎉 no goals
#align polynomial.is_equivalent_at_top_div Polynomial.isEquivalent_atTop_div

theorem div_tendsto_zero_of_degree_lt (hdeg : P.degree < Q.degree) :
    Tendsto (fun x => eval x P / eval x Q) atTop (𝓝 0) := by
  by_cases hP : P = 0
  -- ⊢ Tendsto (fun x => eval x P / eval x Q) atTop (𝓝 0)
  · simp [hP, tendsto_const_nhds]
    -- 🎉 no goals
  rw [← natDegree_lt_natDegree_iff hP] at hdeg
  -- ⊢ Tendsto (fun x => eval x P / eval x Q) atTop (𝓝 0)
  refine' (isEquivalent_atTop_div P Q).symm.tendsto_nhds _
  -- ⊢ Tendsto (fun x => leadingCoeff P / leadingCoeff Q * x ^ (↑(natDegree P) - ↑( …
  rw [← mul_zero]
  -- ⊢ Tendsto (fun x => leadingCoeff P / leadingCoeff Q * x ^ (↑(natDegree P) - ↑( …
  refine' (tendsto_zpow_atTop_zero _).const_mul _
  -- ⊢ ↑(natDegree P) - ↑(natDegree Q) < 0
  linarith
  -- 🎉 no goals
#align polynomial.div_tendsto_zero_of_degree_lt Polynomial.div_tendsto_zero_of_degree_lt

theorem div_tendsto_zero_iff_degree_lt (hQ : Q ≠ 0) :
    Tendsto (fun x => eval x P / eval x Q) atTop (𝓝 0) ↔ P.degree < Q.degree := by
  refine' ⟨fun h => _, div_tendsto_zero_of_degree_lt P Q⟩
  -- ⊢ degree P < degree Q
  by_cases hPQ : P.leadingCoeff / Q.leadingCoeff = 0
  -- ⊢ degree P < degree Q
  · simp only [div_eq_mul_inv, inv_eq_zero, mul_eq_zero] at hPQ
    -- ⊢ degree P < degree Q
    cases' hPQ with hP0 hQ0
    -- ⊢ degree P < degree Q
    · rw [leadingCoeff_eq_zero.1 hP0, degree_zero]
      -- ⊢ ⊥ < degree Q
      exact bot_lt_iff_ne_bot.2 fun hQ' => hQ (degree_eq_bot.1 hQ')
      -- 🎉 no goals
    · exact absurd (leadingCoeff_eq_zero.1 hQ0) hQ
      -- 🎉 no goals
  · have := (isEquivalent_atTop_div P Q).tendsto_nhds h
    -- ⊢ degree P < degree Q
    rw [tendsto_const_mul_zpow_atTop_nhds_iff hPQ] at this
    -- ⊢ degree P < degree Q
    cases' this with h h
    -- ⊢ degree P < degree Q
    · exact absurd h.2 hPQ
      -- 🎉 no goals
    · rw [sub_lt_iff_lt_add, zero_add, Int.ofNat_lt] at h
      -- ⊢ degree P < degree Q
      exact degree_lt_degree h.1
      -- 🎉 no goals
#align polynomial.div_tendsto_zero_iff_degree_lt Polynomial.div_tendsto_zero_iff_degree_lt

theorem div_tendsto_leadingCoeff_div_of_degree_eq (hdeg : P.degree = Q.degree) :
    Tendsto (fun x => eval x P / eval x Q) atTop (𝓝 <| P.leadingCoeff / Q.leadingCoeff) := by
  refine' (isEquivalent_atTop_div P Q).symm.tendsto_nhds _
  -- ⊢ Tendsto (fun x => leadingCoeff P / leadingCoeff Q * x ^ (↑(natDegree P) - ↑( …
  rw [show (P.natDegree : ℤ) = Q.natDegree by simp [hdeg, natDegree]]
  -- ⊢ Tendsto (fun x => leadingCoeff P / leadingCoeff Q * x ^ (↑(natDegree Q) - ↑( …
  simp [tendsto_const_nhds]
  -- 🎉 no goals
#align polynomial.div_tendsto_leading_coeff_div_of_degree_eq Polynomial.div_tendsto_leadingCoeff_div_of_degree_eq

theorem div_tendsto_atTop_of_degree_gt' (hdeg : Q.degree < P.degree)
    (hpos : 0 < P.leadingCoeff / Q.leadingCoeff) :
    Tendsto (fun x => eval x P / eval x Q) atTop atTop := by
  have hQ : Q ≠ 0 := fun h => by
    simp only [h, div_zero, leadingCoeff_zero] at hpos
    exact hpos.false
  rw [← natDegree_lt_natDegree_iff hQ] at hdeg
  -- ⊢ Tendsto (fun x => eval x P / eval x Q) atTop atTop
  refine' (isEquivalent_atTop_div P Q).symm.tendsto_atTop _
  -- ⊢ Tendsto (fun x => leadingCoeff P / leadingCoeff Q * x ^ (↑(natDegree P) - ↑( …
  apply Tendsto.const_mul_atTop hpos
  -- ⊢ Tendsto (fun x => x ^ (↑(natDegree P) - ↑(natDegree Q))) atTop atTop
  apply tendsto_zpow_atTop_atTop
  -- ⊢ 0 < ↑(natDegree P) - ↑(natDegree Q)
  linarith
  -- 🎉 no goals
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
    Tendsto (fun x => eval x P / eval x Q) atTop atBot := by
  have hQ : Q ≠ 0 := fun h => by
    simp only [h, div_zero, leadingCoeff_zero] at hneg
    exact hneg.false
  rw [← natDegree_lt_natDegree_iff hQ] at hdeg
  -- ⊢ Tendsto (fun x => eval x P / eval x Q) atTop atBot
  refine' (isEquivalent_atTop_div P Q).symm.tendsto_atBot _
  -- ⊢ Tendsto (fun x => leadingCoeff P / leadingCoeff Q * x ^ (↑(natDegree P) - ↑( …
  apply Tendsto.neg_const_mul_atTop hneg
  -- ⊢ Tendsto (fun x => x ^ (↑(natDegree P) - ↑(natDegree Q))) atTop atTop
  apply tendsto_zpow_atTop_atTop
  -- ⊢ 0 < ↑(natDegree P) - ↑(natDegree Q)
  linarith
  -- 🎉 no goals
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
    Tendsto (fun x => |eval x P / eval x Q|) atTop atTop := by
  by_cases h : 0 ≤ P.leadingCoeff / Q.leadingCoeff
  -- ⊢ Tendsto (fun x => |eval x P / eval x Q|) atTop atTop
  · exact tendsto_abs_atTop_atTop.comp (P.div_tendsto_atTop_of_degree_gt Q hdeg hQ h)
    -- 🎉 no goals
  · push_neg at h
    -- ⊢ Tendsto (fun x => |eval x P / eval x Q|) atTop atTop
    exact tendsto_abs_atBot_atTop.comp (P.div_tendsto_atBot_of_degree_gt Q hdeg hQ h.le)
    -- 🎉 no goals
#align polynomial.abs_div_tendsto_at_top_of_degree_gt Polynomial.abs_div_tendsto_atTop_of_degree_gt

end PolynomialDivAtTop

theorem isBigO_of_degree_le (h : P.degree ≤ Q.degree) :
    (fun x => eval x P) =O[atTop] fun x => eval x Q := by
  by_cases hp : P = 0
  -- ⊢ (fun x => eval x P) =O[atTop] fun x => eval x Q
  · simpa [hp] using isBigO_zero (fun x => eval x Q) atTop
    -- 🎉 no goals
  · have hq : Q ≠ 0 := ne_zero_of_degree_ge_degree h hp
    -- ⊢ (fun x => eval x P) =O[atTop] fun x => eval x Q
    have hPQ : ∀ᶠ x : 𝕜 in atTop, eval x Q = 0 → eval x P = 0 :=
      Filter.mem_of_superset (Polynomial.eventually_no_roots Q hq) fun x h h' => absurd h' h
    cases' le_iff_lt_or_eq.mp h with h h
    -- ⊢ (fun x => eval x P) =O[atTop] fun x => eval x Q
    · exact isBigO_of_div_tendsto_nhds hPQ 0 (div_tendsto_zero_of_degree_lt P Q h)
      -- 🎉 no goals
    · exact isBigO_of_div_tendsto_nhds hPQ _ (div_tendsto_leadingCoeff_div_of_degree_eq P Q h)
      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.is_O_of_degree_le Polynomial.isBigO_of_degree_le

end Polynomial
