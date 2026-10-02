/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Devon Tuma, Artie Khovanov
-/
module
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Algebra.Group.Order

/-!
# Limits related to polynomial and rational functions

We prove various limits for polynomial and rational functions, depending on
the degrees and leading coefficients of the considered polynomials.
-/

public section

namespace Polynomial

open Filter

open scoped Topology

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] {P Q : F[X]}

section PolynomialDivAtTop

theorem div_tendsto_atTop_of_degree_gt' (hdeg : Q.degree < P.degree)
    (hpos : 0 < P.leadingCoeff / Q.leadingCoeff) :
    Tendsto (fun x ↦ P.eval x / Q.eval x) atTop atTop := by
  let := Preorder.topology F
  have : OrderTopology F := ⟨rfl⟩
  have : Q ≠ 0 := fun hc ↦ by simp [hc] at hpos
  rw [Filter.tendsto_iff_tendsto_inv_inv, inv_atTop₀,
    tendsto_congr' (f₂ := (fun x ↦
      P.reverse.eval x / Q.reverse.eval x * x⁻¹ ^ (P.natDegree - Q.natDegree)))]
  · refine Filter.Tendsto.pos_mul_atTop hpos ?_ (tendsto_inv_nhdsGT_zero.atTop_pow₀ ?_)
    · convert ContinuousWithinAt.tendsto _ using 2
      · simp
      · fun_prop (disch := simp [‹Q ≠ 0›])
    · simp_all [← natDegree_lt_natDegree_iff, Nat.sub_ne_zero_of_lt]
  filter_upwards [show {0}ᶜ ∈ _ from ⟨Set.univ, by simp⟩] with x hx
  simp_rw [pow_sub₀ x⁻¹ (by simpa) (natDegree_le_natDegree hdeg.le),
    ← eval_reverse_mul_pow₀ (x := x⁻¹) (by simpa)]
  field_simp

theorem div_tendsto_atTop_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q ≠ 0)
    (hnng : 0 ≤ P.leadingCoeff / Q.leadingCoeff) :
    Tendsto (fun x ↦ P.eval x / Q.eval x) atTop atTop :=
  have hpos : 0 < P.leadingCoeff / Q.leadingCoeff :=
    lt_of_le_of_ne' hnng (by grind [leadingCoeff_eq_zero, not_lt_bot])
  div_tendsto_atTop_of_degree_gt' hdeg hpos

theorem div_tendsto_atBot_of_degree_gt' (hdeg : Q.degree < P.degree)
    (hneg : P.leadingCoeff / Q.leadingCoeff < 0) :
    Tendsto (fun x ↦ P.eval x / Q.eval x) atTop atBot := by
  convert tendsto_neg_atTop_atBot.comp <| div_tendsto_atTop_of_degree_gt'
      (P := -P) (Q := Q) (by simpa) (by simp; grind)
  simp
  ring

theorem div_tendsto_atBot_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q ≠ 0)
    (hnps : P.leadingCoeff / Q.leadingCoeff ≤ 0) :
    Tendsto (fun x ↦ P.eval x / Q.eval x) atTop atBot :=
  have hneg : P.leadingCoeff / Q.leadingCoeff < 0 :=
    lt_of_le_of_ne' hnps (by grind [leadingCoeff_eq_zero, not_lt_bot])
  div_tendsto_atBot_of_degree_gt' hdeg hneg

theorem div_tendsto_atTop_of_degree_lt_of_leadingCoeff_div_pos
    [TopologicalSpace F] [OrderTopology F]
    (hdeg : P.degree < Q.degree) (hpos : 0 < P.leadingCoeff / Q.leadingCoeff) :
    Tendsto (fun x ↦ P.eval x / Q.eval x) atTop (𝓝[>] 0) := by
  convert tendsto_inv_atTop_nhdsGT_zero.comp <| div_tendsto_atTop_of_degree_gt'
    (P := Q) (Q := P) hdeg (by grind [div_pos_iff])
  simp

theorem div_tendsto_atTop_of_degree_lt_of_leadingCoeff_div_neg
    [TopologicalSpace F] [OrderTopology F]
    (hdeg : P.degree < Q.degree) (hpos : P.leadingCoeff / Q.leadingCoeff < 0) :
    Tendsto (fun x ↦ P.eval x / Q.eval x) atTop (𝓝[<] 0) := by
  convert tendsto_neg_nhdsGT.comp <| div_tendsto_atTop_of_degree_lt_of_leadingCoeff_div_pos
      (P := -P) (Q := Q) (by simpa) (by simp; grind) <;>
    simp; ring

theorem div_tendsto_atTop_zero_of_degree_lt [TopologicalSpace F] [OrderTopology F]
    (hdeg : P.degree < Q.degree) :
    Tendsto (fun x ↦ P.eval x / Q.eval x) atTop (𝓝 0) := by
  rcases lt_trichotomy (P.leadingCoeff / Q.leadingCoeff) 0 with neg | eq | pos
  · exact (div_tendsto_atTop_of_degree_lt_of_leadingCoeff_div_neg hdeg neg).mono_right
      nhdsWithin_le_nhds
  · rw [div_eq_zero_iff] at eq
    cases eq <;> simp_all
  · exact (div_tendsto_atTop_of_degree_lt_of_leadingCoeff_div_pos hdeg pos).mono_right
      nhdsWithin_le_nhds

theorem div_tendsto_atTop_leadingCoeff_div_of_degree_eq [TopologicalSpace F] [OrderTopology F]
    (hdeg : P.degree = Q.degree) :
    Tendsto (fun x ↦ P.eval x / Q.eval x) atTop (𝓝 (P.leadingCoeff / Q.leadingCoeff)) := by
  rcases eq_or_ne Q 0 with rfl | _
  · simp
  rw [Filter.tendsto_iff_tendsto_inv_inv, inv_atTop₀,
    tendsto_congr' (f₂ := (fun x ↦ P.reverse.eval x  / Q.reverse.eval x))]
  · convert (ContinuousAt.tendsto _).mono_left nhdsWithin_le_nhds using 2
    · simp
    · fun_prop (disch := simp [‹Q ≠ 0›])
  filter_upwards [show {0}ᶜ ∈ _ from ⟨Set.univ, by simp⟩] with x hx
  grind [eval_reverse_mul_pow₀ (x := x⁻¹), pow_ne_zero, natDegree_eq_natDegree]

-- TODO : bounded iff version (see non-quotient part)

theorem div_tendsto_atTop_zero_iff_degree_lt [TopologicalSpace F] [OrderTopology F] (hQ : Q ≠ 0) :
    Tendsto (fun x ↦ P.eval x / Q.eval x) atTop (𝓝 0) ↔ P.degree < Q.degree := by
  refine ⟨fun h ↦ ?_, div_tendsto_atTop_zero_of_degree_lt⟩
  contrapose! h
  rcases h.lt_or_eq' with lt | eq
  · grind [div_tendsto_atTop_of_degree_gt, div_tendsto_atBot_of_degree_gt, disjoint_nhds_atTop,
      disjoint_nhds_atBot, Tendsto.not_tendsto]
  · exact (div_tendsto_atTop_leadingCoeff_div_of_degree_eq eq).not_tendsto <| by
      grind [disjoint_nhds_nhds, div_eq_zero_iff, leadingCoeff_eq_zero, degree_zero,
        le_bot_iff, degree_eq_bot]

theorem abs_div_tendsto_atTop_atTop_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q ≠ 0) :
    Tendsto (fun x ↦ |P.eval x / Q.eval x|) atTop atTop := by
  by_cases! h : 0 ≤ P.leadingCoeff / Q.leadingCoeff
  · exact tendsto_abs_atTop_atTop.comp (div_tendsto_atTop_of_degree_gt hdeg hQ h)
  · exact tendsto_abs_atBot_atTop.comp (div_tendsto_atBot_of_degree_gt hdeg hQ h.le)

end PolynomialDivAtTop

section PolynomialDivAtBot

theorem div_tendsto_atBot_zero_iff_degree_lt [TopologicalSpace F] [OrderTopology F] (hQ : Q ≠ 0) :
    Tendsto (fun x ↦ P.eval x / Q.eval x) atBot (𝓝 0) ↔ P.degree < Q.degree := by
  refine ⟨fun ht ↦ ?_, fun hdeg ↦ ?_⟩
  · rw [← P.degree_comp_neg_X, ← Q.degree_comp_neg_X,
        ← div_tendsto_atTop_zero_iff_degree_lt (by simpa)]
    convert ht.comp tendsto_neg_atTop_atBot
    simp
  · rw [← P.degree_comp_neg_X, ← Q.degree_comp_neg_X] at hdeg
    convert (div_tendsto_atTop_zero_of_degree_lt hdeg).comp tendsto_neg_atBot_atTop
    simp

alias ⟨_, div_tendsto_atBot_zero_of_degree_lt⟩ := div_tendsto_atBot_zero_iff_degree_lt

theorem div_tendsto_atBot_leadingCoeff_div_of_degree_eq [TopologicalSpace F] [OrderTopology F]
    (hdeg : P.degree = Q.degree) :
    Tendsto (fun x ↦ P.eval x / Q.eval x) atBot (𝓝 (P.leadingCoeff / Q.leadingCoeff)) := by
  sorry
  -- degrees same so sign switch when going to -∞ same

theorem abs_div_tendsto_atBot_atTop_of_degree_gt [TopologicalSpace F] [OrderTopology F]
    (hdeg : Q.degree < P.degree) (hQ : Q ≠ 0) :
    Tendsto (fun x ↦ |P.eval x / Q.eval x|) atBot atTop := by
  rw [← P.degree_comp_neg_X, ← Q.degree_comp_neg_X] at hdeg
  convert (abs_div_tendsto_atTop_atTop_of_degree_gt hdeg (by simpa)).comp tendsto_neg_atBot_atTop
  simp

end PolynomialDivAtBot

section PolynomialAtTop

theorem tendsto_atTop_of_leadingCoeff_nonneg (hdeg : 0 < P.degree) (hlcf : 0 ≤ P.leadingCoeff) :
    Tendsto P.eval atTop atTop := by
  simpa using div_tendsto_atTop_of_degree_gt' (P := P) (Q := 1) (by simpa)
    (by simp; grind [leadingCoeff_eq_zero, not_lt_bot])

theorem tendsto_atBot_of_leadingCoeff_nonpos (hdeg : 0 < P.degree) (hnps : P.leadingCoeff ≤ 0) :
    Tendsto P.eval atTop atBot := by
  simpa using tendsto_atTop_of_leadingCoeff_nonneg (P := -P)
    (by simpa using hdeg) (by simpa using hnps)

-- TODO : TFAE for next two theorems?

theorem tendsto_pure_iff {c : F} :
    Tendsto P.eval atTop (pure c) ↔ P.leadingCoeff = c ∧ P.degree ≤ 0 := by
  have mp' : Tendsto P.eval atTop (pure c) → P.degree ≤ 0 := fun h ↦ by
    grind [tendsto_atTop_of_leadingCoeff_nonneg, tendsto_atBot_of_leadingCoeff_nonpos,
      Tendsto.not_tendsto, disjoint_pure_atTop, disjoint_pure_atBot]
  have mpr' : P.degree ≤ 0 → Tendsto P.eval atTop (pure P.leadingCoeff) := fun h ↦ by
    rw! [Polynomial.eq_C_of_degree_le_zero h]
    simp
  grind [Filter.Tendsto.not_tendsto, disjoint_pure_pure]

theorem tendsto_nhds_iff [TopologicalSpace F] [OrderTopology F] {c : F} :
    Tendsto P.eval atTop (𝓝 c) ↔ P.leadingCoeff = c ∧ P.degree ≤ 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ (tendsto_pure_iff.mpr h).mono_right (by simp)⟩
  have : P.degree ≤ 0 := by
    grind [tendsto_atTop_of_leadingCoeff_nonneg, tendsto_atBot_of_leadingCoeff_nonpos,
      Tendsto.not_tendsto, disjoint_nhds_atTop, disjoint_nhds_atBot]
  refine ⟨?_, this⟩
  rw! [Polynomial.eq_C_of_degree_le_zero this] at h ⊢
  simp_all

theorem tendsto_atTop_iff_leadingCoeff_nonneg :
    Tendsto P.eval atTop atTop ↔ 0 < P.degree ∧ 0 ≤ P.leadingCoeff := by
  refine ⟨fun h ↦ ?_, fun ⟨h₁, h₂⟩ ↦ tendsto_atTop_of_leadingCoeff_nonneg h₁ h₂⟩
  have hdeg : 0 < P.degree := by
    contrapose! h
    exact (tendsto_pure_iff.mpr ⟨rfl, h⟩).not_tendsto (disjoint_pure_atTop _)
  grind [tendsto_atBot_of_leadingCoeff_nonpos, Tendsto.not_tendsto, disjoint_atBot_atTop]

theorem tendsto_atBot_iff_leadingCoeff_nonpos :
    Tendsto P.eval atTop atBot ↔ 0 < P.degree ∧ P.leadingCoeff ≤ 0 := by
  simp [← tendsto_neg_atTop_iff, ← eval_neg, tendsto_atTop_iff_leadingCoeff_nonneg,
    degree_neg, leadingCoeff_neg]

theorem abs_tendsto_atTop (hdeg : 0 < P.degree) :
    Tendsto (abs <| eval · P) atTop atTop := by
  rcases le_total 0 P.leadingCoeff with hP | hP
  · exact tendsto_abs_atTop_atTop.comp (P.tendsto_atTop_of_leadingCoeff_nonneg hdeg hP)
  · exact tendsto_abs_atBot_atTop.comp (P.tendsto_atBot_of_leadingCoeff_nonpos hdeg hP)

-- TODO : generalise to without the |·| and use to simplify the const iff
theorem isBoundedUnder_abs_atTop_iff :
    (IsBoundedUnder (· ≤ ·) atTop (|eval · P|)) ↔ P.degree ≤ 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨|P.coeff 0|, eventually_map.mpr (Eventually.of_forall
    (forall_imp (fun _ ↦ le_of_eq) fun x ↦ congr(abs $(_root_.trans (congr_arg (eval x)
    (eq_C_of_degree_le_zero h)) eval_C))))⟩⟩
  contrapose! h
  exact not_isBoundedUnder_of_tendsto_atTop (abs_tendsto_atTop h)

theorem abs_tendsto_atTop_iff : Tendsto (fun x ↦ abs <| P.eval x) atTop atTop ↔ 0 < P.degree :=
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

end Polynomial
