/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Devon Tuma
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

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

open Asymptotics Polynomial Topology

namespace Polynomial

variable {𝕜 : Type*} [NormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] (P Q : 𝕜[X])

theorem eventually_atTop_no_roots (hP : P ≠ 0) : ∀ᶠ x in atTop, ¬P.IsRoot x :=
  atTop_le_cofinite <| (finite_setOf_isRoot hP).compl_mem_cofinite

@[deprecated (since := "2026-02-05")] alias eventually_no_roots := eventually_atTop_no_roots

theorem eventually_atBot_no_roots (hP : P ≠ 0) : ∀ᶠ x in atBot, ¬P.IsRoot x :=
  atBot_le_cofinite <| (finite_setOf_isRoot hP).compl_mem_cofinite

variable [OrderTopology 𝕜]

section PolynomialAtTop

theorem isEquivalent_atTop_lead :
    (fun x => eval x P) ~[atTop] fun x => P.leadingCoeff * x ^ P.natDegree := by
  by_cases h : P = 0
  · simp [h, IsEquivalent.refl]
  · simp only [Polynomial.eval_eq_sum_range, sum_range_succ]
    exact
      IsLittleO.add_isEquivalent
        (IsLittleO.sum fun i hi =>
          IsLittleO.const_mul_left
            ((IsLittleO.const_mul_right fun hz => h <| leadingCoeff_eq_zero.mp hz) <|
              isLittleO_pow_pow_atTop_of_lt (mem_range.mp hi))
            _)
        IsEquivalent.refl

theorem tendsto_atTop_of_leadingCoeff_nonneg (hdeg : 0 < P.degree) (hnng : 0 ≤ P.leadingCoeff) :
    Tendsto (fun x => eval x P) atTop atTop :=
  P.isEquivalent_atTop_lead.symm.tendsto_atTop <|
    tendsto_const_mul_pow_atTop (natDegree_pos_iff_degree_pos.2 hdeg).ne' <|
      hnng.lt_of_ne' <| leadingCoeff_ne_zero.mpr <| ne_zero_of_degree_gt hdeg

theorem tendsto_atTop_iff_leadingCoeff_nonneg :
    Tendsto (fun x => eval x P) atTop atTop ↔ 0 < P.degree ∧ 0 ≤ P.leadingCoeff := by
  refine ⟨fun h => ?_, fun h => tendsto_atTop_of_leadingCoeff_nonneg P h.1 h.2⟩
  have : Tendsto (fun x => P.leadingCoeff * x ^ P.natDegree) atTop atTop :=
    (isEquivalent_atTop_lead P).tendsto_atTop h
  rw [tendsto_const_mul_pow_atTop_iff, ← pos_iff_ne_zero, natDegree_pos_iff_degree_pos] at this
  exact ⟨this.1, this.2.le⟩

theorem tendsto_atBot_iff_leadingCoeff_nonpos :
    Tendsto (fun x => eval x P) atTop atBot ↔ 0 < P.degree ∧ P.leadingCoeff ≤ 0 := by
  simp only [← tendsto_neg_atTop_iff, ← eval_neg, tendsto_atTop_iff_leadingCoeff_nonneg,
    degree_neg, leadingCoeff_neg, neg_nonneg]

theorem tendsto_atBot_of_leadingCoeff_nonpos (hdeg : 0 < P.degree) (hnps : P.leadingCoeff ≤ 0) :
    Tendsto (fun x => eval x P) atTop atBot :=
  P.tendsto_atBot_iff_leadingCoeff_nonpos.2 ⟨hdeg, hnps⟩

theorem abs_tendsto_atTop (hdeg : 0 < P.degree) :
    Tendsto (fun x => abs <| eval x P) atTop atTop := by
  rcases le_total 0 P.leadingCoeff with hP | hP
  · exact tendsto_abs_atTop_atTop.comp (P.tendsto_atTop_of_leadingCoeff_nonneg hdeg hP)
  · exact tendsto_abs_atBot_atTop.comp (P.tendsto_atBot_of_leadingCoeff_nonpos hdeg hP)

theorem abs_isBoundedUnder_atTop_iff :
    (IsBoundedUnder (· ≤ ·) atTop fun x => |eval x P|) ↔ P.degree ≤ 0 := by
  refine ⟨fun h => ?_, fun h => ⟨|P.coeff 0|, eventually_map.mpr (Eventually.of_forall
    (forall_imp (fun _ => le_of_eq) fun x => congr_arg abs <| _root_.trans (congr_arg (eval x)
    (eq_C_of_degree_le_zero h)) eval_C))⟩⟩
  contrapose! h
  exact not_isBoundedUnder_of_tendsto_atTop (abs_tendsto_atTop P h)

@[deprecated (since := "2026-02-05")] alias abs_isBoundedUnder_iff := abs_isBoundedUnder_atTop_iff

theorem abs_tendsto_atTop_iff : Tendsto (fun x => abs <| eval x P) atTop atTop ↔ 0 < P.degree :=
  ⟨fun h ↦ not_le.mp (mt (abs_isBoundedUnder_atTop_iff P).mpr
    (not_isBoundedUnder_of_tendsto_atTop h)), abs_tendsto_atTop P⟩

theorem tendsto_nhds_iff {c : 𝕜} :
    Tendsto (fun x => eval x P) atTop (𝓝 c) ↔ P.leadingCoeff = c ∧ P.degree ≤ 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := P.isEquivalent_atTop_lead.tendsto_nhds h
    by_cases hP : P.leadingCoeff = 0
    · simp only [hP, zero_mul, tendsto_const_nhds_iff] at this
      exact ⟨_root_.trans hP this, by simp [leadingCoeff_eq_zero.1 hP]⟩
    · rw [tendsto_const_mul_pow_nhds_iff hP, natDegree_eq_zero_iff_degree_le_zero] at this
      exact this.symm
  · refine P.isEquivalent_atTop_lead.symm.tendsto_nhds ?_
    have : P.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.2 h.2
    simp only [h.1, this, pow_zero, mul_one]
    exact tendsto_const_nhds

end PolynomialAtTop

section PolynomialAtBot

theorem isEquivalent_atBot_lead : P.eval ~[atBot] (P.leadingCoeff * · ^ P.natDegree) := by
  convert (P.comp (-X)).isEquivalent_atTop_lead.comp_tendsto tendsto_neg_atBot_atTop using 2
  · simp
  · rw [Function.comp_apply, comp_neg_X_leadingCoeff_eq, ← mul_rotate]
    simp [natDegree_comp, ← mul_pow, mul_comm]

theorem abs_tendsto_atBot (hdeg : 0 < P.degree) : Tendsto (|P.eval ·|) atBot atTop := by
  convert ((P.comp (-X)).abs_tendsto_atTop (by simp [hdeg])).comp tendsto_neg_atBot_atTop using 2
  simp

theorem abs_isBoundedUnder_atBot_iff :
    (IsBoundedUnder (· ≤ ·) atBot (|P.eval ·|)) ↔ P.degree ≤ 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨|P.coeff 0|, eventually_map.mpr (Eventually.of_forall
    (forall_imp (fun _ ↦ le_of_eq) fun x ↦ congr_arg abs <| _root_.trans (congr_arg (eval x)
    (eq_C_of_degree_le_zero h)) eval_C))⟩⟩
  contrapose! h
  exact not_isBoundedUnder_of_tendsto_atTop (abs_tendsto_atBot P h)

theorem abs_tendsto_atBot_iff : Tendsto (|P.eval ·|) atBot atTop ↔ 0 < P.degree :=
  ⟨fun h ↦ not_le.mp (mt (abs_isBoundedUnder_atBot_iff P).mpr
    (not_isBoundedUnder_of_tendsto_atTop h)), abs_tendsto_atBot P⟩

end PolynomialAtBot

section PolynomialDivAtTop

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

theorem div_tendsto_atTop_zero_of_degree_lt (hdeg : P.degree < Q.degree) :
    Tendsto (fun x => eval x P / eval x Q) atTop (𝓝 0) := by
  by_cases hP : P = 0
  · simp [hP]
  rw [← natDegree_lt_natDegree_iff hP] at hdeg
  refine (isEquivalent_atTop_div P Q).symm.tendsto_nhds ?_
  rw [← mul_zero]
  refine (tendsto_zpow_atTop_zero ?_).const_mul _
  lia

@[deprecated (since := "2026-02-05")]
alias div_tendsto_zero_of_degree_lt := div_tendsto_atTop_zero_of_degree_lt

theorem div_tendsto_atTop_zero_iff_degree_lt (hQ : Q ≠ 0) :
    Tendsto (fun x => eval x P / eval x Q) atTop (𝓝 0) ↔ P.degree < Q.degree := by
  refine ⟨fun h => ?_, div_tendsto_atTop_zero_of_degree_lt P Q⟩
  by_cases hPQ : P.leadingCoeff / Q.leadingCoeff = 0
  · simp only [div_eq_mul_inv, inv_eq_zero, mul_eq_zero] at hPQ
    rcases hPQ with hP0 | hQ0
    · rw [leadingCoeff_eq_zero.1 hP0, degree_zero]
      exact bot_lt_iff_ne_bot.2 fun hQ' => hQ (degree_eq_bot.1 hQ')
    · exact absurd (leadingCoeff_eq_zero.1 hQ0) hQ
  · have := (isEquivalent_atTop_div P Q).tendsto_nhds h
    rw [tendsto_const_mul_zpow_atTop_nhds_iff hPQ] at this
    rcases this with h | h
    · exact absurd h.2 hPQ
    · rw [sub_lt_iff_lt_add, zero_add, Int.ofNat_lt] at h
      exact degree_lt_degree h.1

@[deprecated (since := "2026-02-05")]
alias div_tendsto_zero_iff_degree_lt := div_tendsto_atTop_zero_iff_degree_lt

theorem div_tendsto_atTop_leadingCoeff_div_of_degree_eq (hdeg : P.degree = Q.degree) :
    Tendsto (fun x => eval x P / eval x Q) atTop (𝓝 <| P.leadingCoeff / Q.leadingCoeff) := by
  refine (isEquivalent_atTop_div P Q).symm.tendsto_nhds ?_
  rw [show (P.natDegree : ℤ) = Q.natDegree by simp [hdeg, natDegree]]
  simp

@[deprecated (since := "2026-02-05")]
alias div_tendsto_leadingCoeff_div_of_degree_eq := div_tendsto_atTop_leadingCoeff_div_of_degree_eq

theorem div_tendsto_atTop_of_degree_gt' (hdeg : Q.degree < P.degree)
    (hpos : 0 < P.leadingCoeff / Q.leadingCoeff) :
    Tendsto (fun x => eval x P / eval x Q) atTop atTop := by
  have hQ : Q ≠ 0 := fun h => by
    simp only [h, div_zero, leadingCoeff_zero] at hpos
    exact hpos.false
  rw [← natDegree_lt_natDegree_iff hQ] at hdeg
  refine (isEquivalent_atTop_div P Q).symm.tendsto_atTop ?_
  apply Tendsto.const_mul_atTop hpos
  apply tendsto_zpow_atTop_atTop
  lia

theorem div_tendsto_atTop_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q ≠ 0)
    (hnng : 0 ≤ P.leadingCoeff / Q.leadingCoeff) :
    Tendsto (fun x => eval x P / eval x Q) atTop atTop :=
  have ratio_pos : 0 < P.leadingCoeff / Q.leadingCoeff :=
    lt_of_le_of_ne hnng
      (div_ne_zero (fun h => ne_zero_of_degree_gt hdeg <| leadingCoeff_eq_zero.mp h) fun h =>
          hQ <| leadingCoeff_eq_zero.mp h).symm
  div_tendsto_atTop_of_degree_gt' P Q hdeg ratio_pos

theorem div_tendsto_atBot_of_degree_gt' (hdeg : Q.degree < P.degree)
    (hneg : P.leadingCoeff / Q.leadingCoeff < 0) :
    Tendsto (fun x => eval x P / eval x Q) atTop atBot := by
  have hQ : Q ≠ 0 := fun h => by
    simp only [h, div_zero, leadingCoeff_zero] at hneg
    exact hneg.false
  rw [← natDegree_lt_natDegree_iff hQ] at hdeg
  refine (isEquivalent_atTop_div P Q).symm.tendsto_atBot ?_
  apply Tendsto.const_mul_atTop_of_neg hneg
  apply tendsto_zpow_atTop_atTop
  lia

theorem div_tendsto_atBot_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q ≠ 0)
    (hnps : P.leadingCoeff / Q.leadingCoeff ≤ 0) :
    Tendsto (fun x => eval x P / eval x Q) atTop atBot :=
  have ratio_neg : P.leadingCoeff / Q.leadingCoeff < 0 :=
    lt_of_le_of_ne hnps
      (div_ne_zero (fun h => ne_zero_of_degree_gt hdeg <| leadingCoeff_eq_zero.mp h) fun h =>
        hQ <| leadingCoeff_eq_zero.mp h)
  div_tendsto_atBot_of_degree_gt' P Q hdeg ratio_neg

theorem abs_div_tendsto_atTop_atTop_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q ≠ 0) :
    Tendsto (fun x => |eval x P / eval x Q|) atTop atTop := by
  by_cases! h : 0 ≤ P.leadingCoeff / Q.leadingCoeff
  · exact tendsto_abs_atTop_atTop.comp (P.div_tendsto_atTop_of_degree_gt Q hdeg hQ h)
  · exact tendsto_abs_atBot_atTop.comp (P.div_tendsto_atBot_of_degree_gt Q hdeg hQ h.le)

@[deprecated (since := "2026-02-05")]
alias abs_div_tendsto_atTop_of_degree_gt := abs_div_tendsto_atTop_atTop_of_degree_gt

end PolynomialDivAtTop

section PolynomialDivAtBot

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

theorem div_tendsto_atBot_zero_of_degree_lt (hdeg : P.degree < Q.degree) :
    Tendsto (fun x ↦ eval x P / eval x Q) atBot (𝓝 0) := by
  rw [← P.degree_comp_neg_X, ← Q.degree_comp_neg_X] at hdeg
  convert (div_tendsto_atTop_zero_of_degree_lt _ _ hdeg).comp tendsto_neg_atBot_atTop using 2
  simp

theorem div_tendsto_atBot_zero_iff_degree_lt (hQ : Q ≠ 0) :
    Tendsto (fun x ↦ eval x P / eval x Q) atBot (𝓝 0) ↔ P.degree < Q.degree := by
  refine ⟨fun h ↦ ?_, div_tendsto_atBot_zero_of_degree_lt P Q⟩
  rw [← P.degree_comp_neg_X, ← Q.degree_comp_neg_X]
  replace hQ : Q.comp (-X) ≠ 0 := by
    rw [Ne, comp_eq_zero_iff]
    simp [hQ]
  rw [← div_tendsto_atTop_zero_iff_degree_lt _ _ hQ]
  convert h.comp tendsto_neg_atTop_atBot using 2
  simp

theorem div_tendsto_atBot_leadingCoeff_div_of_degree_eq (hdeg : P.degree = Q.degree) :
    Tendsto (fun x ↦ eval x P / eval x Q) atBot (𝓝 (P.leadingCoeff / Q.leadingCoeff)) := by
  refine (isEquivalent_atBot_div P Q).symm.tendsto_nhds ?_
  simp [natDegree_eq_natDegree hdeg]

theorem abs_div_tendsto_atBot_atTop_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q ≠ 0) :
    Tendsto (fun x ↦ |eval x P / eval x Q|) atBot atTop := by
  rw [← P.degree_comp_neg_X, ← Q.degree_comp_neg_X] at hdeg
  replace hQ : Q.comp (-X) ≠ 0 := by
    rw [Ne, comp_eq_zero_iff]
    simp [hQ]
  convert (abs_div_tendsto_atTop_atTop_of_degree_gt _ _ hdeg hQ).comp
    tendsto_neg_atBot_atTop using 2
  simp

end PolynomialDivAtBot

theorem isLittleO_atTop_of_degree_lt (h : P.degree < Q.degree) : P.eval =o[atTop] Q.eval := by
  by_cases hp : P = 0
  · simp [hp]
  · have hq : Q ≠ 0 := ne_zero_of_degree_ge_degree h.le hp
    have hPQ : ∀ᶠ x in atTop, Q.eval x = 0 → P.eval x = 0 :=
      mem_of_superset (eventually_atTop_no_roots Q hq) fun x h h' ↦ absurd h' h
    exact isLittleO_of_tendsto' hPQ (div_tendsto_atTop_zero_of_degree_lt P Q h)

theorem isLittleO_atBot_of_degree_lt (h : P.degree < Q.degree) : P.eval =o[atBot] Q.eval := by
  rw [← P.degree_comp_neg_X, ← Q.degree_comp_neg_X] at h
  convert (isLittleO_atTop_of_degree_lt _ _ h).comp_tendsto tendsto_neg_atBot_atTop using 2
  all_goals simp

theorem isBigO_atTop_of_degree_le (h : P.degree ≤ Q.degree) : P.eval =O[atTop] Q.eval := by
  by_cases hp : P = 0
  · simpa [hp] using isBigO_zero Q.eval atTop
  · have hq : Q ≠ 0 := ne_zero_of_degree_ge_degree h hp
    have hPQ : ∀ᶠ x in atTop, Q.eval x = 0 → P.eval x = 0 :=
      mem_of_superset (eventually_atTop_no_roots Q hq) fun x h h' ↦ absurd h' h
    rcases le_iff_lt_or_eq.mp h with h | h
    · exact isBigO_of_div_tendsto_nhds hPQ 0 (div_tendsto_atTop_zero_of_degree_lt P Q h)
    · exact isBigO_of_div_tendsto_nhds hPQ _ (div_tendsto_atTop_leadingCoeff_div_of_degree_eq P Q h)

theorem isBigO_atBot_of_degree_le (h : P.degree ≤ Q.degree) : P.eval =O[atBot] Q.eval := by
  rw [← P.degree_comp_neg_X, ← Q.degree_comp_neg_X] at h
  convert (isBigO_atTop_of_degree_le _ _ h).comp_tendsto tendsto_neg_atBot_atTop using 2
  all_goals simp

@[deprecated (since := "2026-02-05")] alias isBigO_of_degree_le := isBigO_atTop_of_degree_le

end Polynomial
