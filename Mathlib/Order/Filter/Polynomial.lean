/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Devon Tuma, Artie Khovanov
-/
module
public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.Order.Filter.AtTopBot.Field
public import Mathlib.Order.Filter.IsBounded
public import Mathlib.Topology.Order.Basic

/-!
# Limits related to polynomial and rational functions

We prove various limits for polynomial and rational functions, depending on
the degrees and leading coefficients of the considered polynomials.
-/

namespace Polynomial

open Filter

open scoped Topology

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] {P Q : F[X]}

section PolynomialAtTop

theorem tendsto_atTop_of_leadingCoeff_nonneg (hdeg : 0 < P.degree) :
    0 ≤ P.leadingCoeff → Tendsto (eval · P) atTop atTop := by
  refine degree_pos_induction_on P hdeg
    (fun _ _ ↦ ?_) (fun _ ih hnnng ↦ ?_) (fun _ _ _ ↦ ?_)
  · simpa using tendsto_id.const_mul_atTop (by simp at *; grind)
  · simpa using (ih (by simpa using hnnng)).atTop_mul_atTop₀ tendsto_id
  · simpa using tendsto_atTop_add_const_right _ _
      (by grind [leadingCoeff_add_of_degree_lt', degree_C_le])

#find_home tendsto_atTop_of_leadingCoeff_nonneg

theorem tendsto_atBot_of_leadingCoeff_nonpos (hdeg : 0 < P.degree) (hnps : P.leadingCoeff ≤ 0) :
    Tendsto (fun x ↦ eval x P) atTop atBot := by
  simpa using tendsto_atTop_of_leadingCoeff_nonneg (P := -P)
    (by simpa using hdeg) (by simpa using hnps)

theorem tendsto_atTop_or_tendsto_atBot (hdeg : 0 < P.degree) :
    Tendsto (eval · P) atTop atTop ∨ Tendsto (eval · P) atTop atBot := by
  rcases lt_or_ge 0 P.leadingCoeff with pos | neg
  · exact Or.inl <| tendsto_atTop_of_leadingCoeff_nonneg hdeg pos.le
  · exact Or.inr <| tendsto_atBot_of_leadingCoeff_nonpos hdeg neg

theorem tendsto_pure_iff {c : F} :
    Tendsto (eval · P) atTop (pure c) ↔ P.leadingCoeff = c ∧ P.degree ≤ 0 := by
  have mp' : Tendsto (eval · P) atTop (pure c) → P.degree ≤ 0 := fun h ↦ by
    contrapose! h
    rcases tendsto_atTop_or_tendsto_atBot h with top | bot
    · exact top.not_tendsto (disjoint_pure_atTop _).symm
    · exact bot.not_tendsto (disjoint_pure_atBot _).symm
  have mpr' : P.degree ≤ 0 → Tendsto (eval · P) atTop (pure P.leadingCoeff) := fun h ↦ by
    rw! [Polynomial.eq_C_of_degree_le_zero h]
    simp
  grind [Filter.Tendsto.not_tendsto, disjoint_pure_pure]

theorem tendsto_nhds_iff [TopologicalSpace F] [OrderTopology F] {c : F} :
    Tendsto (eval · P) atTop (𝓝 c) ↔ P.leadingCoeff = c ∧ P.degree ≤ 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ (tendsto_pure_iff.mpr h).mono_right (by simp)⟩
  · have : P.degree ≤ 0 := by
      contrapose! h
      rcases tendsto_atTop_or_tendsto_atBot h with top | bot
      · exact top.not_tendsto (disjoint_nhds_atTop _).symm
      · exact bot.not_tendsto (disjoint_nhds_atBot _).symm
    refine ⟨?_, this⟩
    rw! [Polynomial.eq_C_of_degree_le_zero this] at h ⊢
    simp_all

theorem tendsto_atTop_iff_leadingCoeff_nonneg :
    Tendsto (eval · P) atTop atTop ↔ 0 < P.degree ∧ 0 ≤ P.leadingCoeff := by
  refine ⟨fun h ↦ ?_, fun h ↦ tendsto_atTop_of_leadingCoeff_nonneg h.1 h.2⟩
  have hdeg : 0 < P.degree := by
    contrapose! h
    rw! [Polynomial.eq_C_of_degree_le_zero h]
    simpa using tendsto_const_pure.not_tendsto (disjoint_pure_atTop _)
  refine ⟨hdeg, ?_⟩
  revert h
  refine degree_pos_induction_on P hdeg
    (fun ha h ↦ ?_) (fun hdeg ih h ↦ ?_) (fun {_ a} hdeg ih h ↦ ?_)
  · simpa using ((tendsto_const_mul_atTop_iff_pos tendsto_id).mp (by simpa using h)).le
  · simpa using ih <| by
      contrapose! h
      simpa using tendsto_atTop_or_tendsto_atBot hdeg |>.resolve_left h |>.atBot_mul_atTop₀
        tendsto_id |>.not_tendsto disjoint_atBot_atTop
  · rw [leadingCoeff_add_of_degree_lt' (degree_C_le.trans_lt hdeg)]
    exact ih (by simpa using tendsto_atTop_add_const_right _ (-a) h)

theorem tendsto_atBot_iff_leadingCoeff_nonpos :
    Tendsto (eval · P) atTop atBot ↔ 0 < P.degree ∧ P.leadingCoeff ≤ 0 := by
  simp only [← tendsto_neg_atTop_iff, ← eval_neg, tendsto_atTop_iff_leadingCoeff_nonneg,
    degree_neg, leadingCoeff_neg, neg_nonneg]

theorem abs_tendsto_atTop (hdeg : 0 < P.degree) :
    Tendsto (abs <| eval · P) atTop atTop := by
  rcases le_total 0 P.leadingCoeff with hP | hP
  · exact tendsto_abs_atTop_atTop.comp (P.tendsto_atTop_of_leadingCoeff_nonneg hdeg hP)
  · exact tendsto_abs_atBot_atTop.comp (P.tendsto_atBot_of_leadingCoeff_nonpos hdeg hP)

theorem isBoundedUnder_abs_atTop_iff :
    (IsBoundedUnder (· ≤ ·) atTop (|eval · P|)) ↔ P.degree ≤ 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨|P.coeff 0|, eventually_map.mpr (Eventually.of_forall
    (forall_imp (fun _ ↦ le_of_eq) fun x ↦ congr(abs $(_root_.trans (congr_arg (eval x)
    (eq_C_of_degree_le_zero h)) eval_C))))⟩⟩
  contrapose! h
  exact not_isBoundedUnder_of_tendsto_atTop (abs_tendsto_atTop h)

theorem abs_tendsto_atTop_iff : Tendsto (fun x ↦ abs <| eval x P) atTop atTop ↔ 0 < P.degree :=
  ⟨fun h ↦ not_le.mp (mt isBoundedUnder_abs_atTop_iff.mpr
    (not_isBoundedUnder_of_tendsto_atTop h)), abs_tendsto_atTop⟩

end PolynomialAtTop

section PolynomialAtBot

theorem abs_tendsto_atBot (hdeg : 0 < P.degree) : Tendsto (|P.eval ·|) atBot atTop := by
  convert! ((P.comp (-X)).abs_tendsto_atTop (by simp [hdeg])).comp tendsto_neg_atBot_atTop using 2
  simp

theorem isBoundedUnder_abs_atBot_iff :
    (IsBoundedUnder (· ≤ ·) atBot (|P.eval ·|)) ↔ P.degree ≤ 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨|P.coeff 0|, eventually_map.mpr (Eventually.of_forall
    (forall_imp (fun _ ↦ le_of_eq) fun x ↦ congr(abs $(_root_.trans (congr_arg (eval x)
    (eq_C_of_degree_le_zero h)) eval_C))))⟩⟩
  contrapose! h
  exact not_isBoundedUnder_of_tendsto_atTop (abs_tendsto_atBot h)

theorem abs_tendsto_atBot_iff : Tendsto (|P.eval ·|) atBot atTop ↔ 0 < P.degree :=
  ⟨fun h ↦ not_le.mp (mt isBoundedUnder_abs_atBot_iff.mpr
    (not_isBoundedUnder_of_tendsto_atTop h)), abs_tendsto_atBot⟩

end PolynomialAtBot


section PolynomialDivAtTop

theorem div_tendsto_atTop_zero_of_degree_lt [TopologicalSpace F] [OrderTopology F]
    (hdeg : P.degree < Q.degree) :
    Tendsto (fun x ↦ eval x P / eval x Q) atTop (𝓝 0) := by
  by_cases hP : P = 0
  · simp [hP]
  sorry

theorem div_tendsto_atTop_zero_iff_degree_lt [TopologicalSpace F] [OrderTopology F] (hQ : Q ≠ 0) :
    Tendsto (fun x ↦ eval x P / eval x Q) atTop (𝓝 0) ↔ P.degree < Q.degree := by
  refine ⟨fun h ↦ ?_, div_tendsto_atTop_zero_of_degree_lt⟩
  by_cases hPQ : P.leadingCoeff / Q.leadingCoeff = 0
  · simp only [div_eq_mul_inv, inv_eq_zero, mul_eq_zero] at hPQ
    rcases hPQ with hP0 | hQ0
    · rw [leadingCoeff_eq_zero.1 hP0, degree_zero]
      exact bot_lt_iff_ne_bot.2 fun hQ' ↦ hQ (degree_eq_bot.1 hQ')
    · exact absurd (leadingCoeff_eq_zero.1 hQ0) hQ
  · sorry

theorem div_tendsto_atTop_leadingCoeff_div_of_degree_eq [TopologicalSpace F] [OrderTopology F]
    (hdeg : P.degree = Q.degree) :
    Tendsto (fun x ↦ eval x P / eval x Q) atTop (𝓝 <| P.leadingCoeff / Q.leadingCoeff) := by
  sorry

theorem div_tendsto_atTop_of_degree_gt' (hdeg : Q.degree < P.degree)
    (hpos : 0 < P.leadingCoeff / Q.leadingCoeff) :
    Tendsto (fun x ↦ eval x P / eval x Q) atTop atTop := by
  have hQ : Q ≠ 0 := fun h ↦ by simp [h] at hpos
  rw [← natDegree_lt_natDegree_iff hQ] at hdeg
  sorry

theorem div_tendsto_atTop_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q ≠ 0)
    (hnng : 0 ≤ P.leadingCoeff / Q.leadingCoeff) :
    Tendsto (fun x ↦ eval x P / eval x Q) atTop atTop :=
  have ratio_pos : 0 < P.leadingCoeff / Q.leadingCoeff :=
    lt_of_le_of_ne hnng
      (div_ne_zero (fun h ↦ ne_zero_of_degree_gt hdeg <| leadingCoeff_eq_zero.mp h) fun h ↦
          hQ <| leadingCoeff_eq_zero.mp h).symm
  div_tendsto_atTop_of_degree_gt' hdeg ratio_pos

theorem div_tendsto_atBot_of_degree_gt' (hdeg : Q.degree < P.degree)
    (hneg : P.leadingCoeff / Q.leadingCoeff < 0) :
    Tendsto (fun x ↦ eval x P / eval x Q) atTop atBot := by
  have hQ : Q ≠ 0 := fun h ↦ by
    simp only [h, div_zero, leadingCoeff_zero] at hneg
    exact hneg.false
  rw [← natDegree_lt_natDegree_iff hQ] at hdeg
  sorry

theorem div_tendsto_atBot_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q ≠ 0)
    (hnps : P.leadingCoeff / Q.leadingCoeff ≤ 0) :
    Tendsto (fun x ↦ eval x P / eval x Q) atTop atBot :=
  have ratio_neg : P.leadingCoeff / Q.leadingCoeff < 0 :=
    lt_of_le_of_ne hnps
      (div_ne_zero (fun h ↦ ne_zero_of_degree_gt hdeg <| leadingCoeff_eq_zero.mp h) fun h ↦
        hQ <| leadingCoeff_eq_zero.mp h)
  div_tendsto_atBot_of_degree_gt' hdeg ratio_neg

theorem abs_div_tendsto_atTop_atTop_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q ≠ 0) :
    Tendsto (fun x ↦ |eval x P / eval x Q|) atTop atTop := by
  by_cases! h : 0 ≤ P.leadingCoeff / Q.leadingCoeff
  · exact tendsto_abs_atTop_atTop.comp (div_tendsto_atTop_of_degree_gt hdeg hQ h)
  · exact tendsto_abs_atBot_atTop.comp (div_tendsto_atBot_of_degree_gt hdeg hQ h.le)

end PolynomialDivAtTop

section PolynomialDivAtBot

theorem div_tendsto_atBot_zero_of_degree_lt [TopologicalSpace F] [OrderTopology F]
    (hdeg : P.degree < Q.degree) :
    Tendsto (fun x ↦ eval x P / eval x Q) atBot (𝓝 0) := by
  rw [← P.degree_comp_neg_X, ← Q.degree_comp_neg_X] at hdeg
  convert! (div_tendsto_atTop_zero_of_degree_lt hdeg).comp tendsto_neg_atBot_atTop using 2
  simp

theorem div_tendsto_atBot_zero_iff_degree_lt [TopologicalSpace F] [OrderTopology F] (hQ : Q ≠ 0) :
    Tendsto (fun x ↦ eval x P / eval x Q) atBot (𝓝 0) ↔ P.degree < Q.degree := by
  refine ⟨fun h ↦ ?_, div_tendsto_atBot_zero_of_degree_lt⟩
  rw [← P.degree_comp_neg_X, ← Q.degree_comp_neg_X]
  replace hQ : Q.comp (-X) ≠ 0 := by
    rw [Ne, comp_eq_zero_iff]
    simp [hQ]
  sorry

theorem div_tendsto_atBot_leadingCoeff_div_of_degree_eq [TopologicalSpace F] [OrderTopology F]
    (hdeg : P.degree = Q.degree) :
    Tendsto (fun x ↦ eval x P / eval x Q) atBot (𝓝 (P.leadingCoeff / Q.leadingCoeff)) := by
  sorry

theorem abs_div_tendsto_atBot_atTop_of_degree_gt [TopologicalSpace F] [OrderTopology F]
    (hdeg : Q.degree < P.degree) (hQ : Q ≠ 0) :
    Tendsto (fun x ↦ |eval x P / eval x Q|) atBot atTop := by
  rw [← P.degree_comp_neg_X, ← Q.degree_comp_neg_X] at hdeg
  replace hQ : Q.comp (-X) ≠ 0 := by
    rw [Ne, comp_eq_zero_iff]
    simp [hQ]
  convert! (abs_div_tendsto_atTop_atTop_of_degree_gt hdeg hQ).comp tendsto_neg_atBot_atTop
    using 2
  simp

end PolynomialDivAtBot

end Polynomial
