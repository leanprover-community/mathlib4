/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Devon Tuma, Artie Khovanov
-/
module

public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.Order.Filter.IsBounded
public import Mathlib.Tactic.Field
public import Mathlib.Topology.Algebra.Order.Field

/-!
# Behaviour at infinity of polynomial and rational functions

We prove basic facts about the behavior of polynomial and rational functions at infinity.

The main result is `Polynomial.tendsTo_atTop_div_nhds_leadingCoeff`, which states that, for
any polynomial `P` of degree `n` with leading coefficient `a`, `P / x ^ n → a` as `x → +∞`.

We then use this result to characterise the behaviour at infinity of polynomials and rational
functions in terms of their degrees and leading coefficients.
-/

public section

open Filter

open scoped Topology

namespace Polynomial

-- TODO : better names

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] {P Q : F[X]}

section PolynomialAtTop

variable (P) in
theorem tendsTo_atTop_div_nhds_leadingCoeff [TopologicalSpace F] [OrderTopology F] :
    Tendsto (fun x ↦ P.eval x / x ^ P.natDegree) atTop (𝓝 P.leadingCoeff) := by
  induction P using horner_induction with
  | hC _ => simp
  | ha _ a _ hdeg _ ih =>
    convert ih.add ((tendsto_pow_neg_atTop hdeg.ne').const_mul a)
    · grind [eval_add, eval_C, zpow_neg, zpow_natCast]
    · simp_all [leadingCoeff_add_of_degree_lt' (degree_lt_degree _)]
  | hX _ _ ih =>
    convert ih.congr' _ using 2
    · simp
    · filter_upwards [eventually_ne_atTop 0]
      grind [eval_mul, eval_X,natDegree_mul_X, pow_succ]

theorem tendsTo_atTop_div_nhds_one [TopologicalSpace F] [OrderTopology F] (hP : P ≠ 0) :
    Tendsto (fun x ↦ P.eval x / (P.leadingCoeff * x ^ P.natDegree)) atTop (𝓝 1) := by
  convert (P.tendsTo_atTop_div_nhds_leadingCoeff.mul_const (1 / P.leadingCoeff)).congr' ?_
  · grind [leadingCoeff_eq_zero]
  · filter_upwards [eventually_ne_atTop 0]
    grind [leadingCoeff_eq_zero]

theorem tendsto_atTop_iff_leadingCoeff_nonneg :
    Tendsto P.eval atTop atTop ↔ 0 < P.degree ∧ 0 ≤ P.leadingCoeff := by
  let := Preorder.topology F
  have : OrderTopology F := ⟨rfl⟩
  by_cases hP : P = 0
  · suffices ¬ Tendsto (fun _ ↦ (0 : F)) (atTop : Filter F) atTop by simp_all
    exact tendsto_const_pure.not_tendsto (disjoint_pure_atTop 0)
  rw [tendsto_atTop_iff_of_tendsto_div_nhds_one (tendsTo_atTop_div_nhds_one hP),
    tendsto_const_mul_pow_atTop_iff]
  grind [natDegree_pos_iff_degree_pos, leadingCoeff_eq_zero]

theorem tendsto_atTop_of_leadingCoeff_nonneg (hdeg : 0 < P.degree) (hnng : 0 ≤ P.leadingCoeff) :
    Tendsto P.eval atTop atTop := tendsto_atTop_iff_leadingCoeff_nonneg.mpr ⟨hdeg, hnng⟩

theorem tendsto_atBot_iff_leadingCoeff_nonpos :
    Tendsto P.eval atTop atBot ↔ 0 < P.degree ∧ P.leadingCoeff ≤ 0 := by
  simp_rw [← tendsto_neg_atTop_iff, ← eval_neg, tendsto_atTop_iff_leadingCoeff_nonneg]
  simp

theorem tendsto_atBot_of_leadingCoeff_nonpos (hdeg : 0 < P.degree) (hnps : P.leadingCoeff ≤ 0) :
    Tendsto P.eval atTop atBot := tendsto_atBot_iff_leadingCoeff_nonpos.mpr ⟨hdeg, hnps⟩

theorem abs_tendsto_atTop (hdeg : 0 < P.degree) :
    Tendsto (|P.eval ·|) atTop atTop := by
  rcases le_total 0 P.leadingCoeff with hP | hP
  · exact tendsto_abs_atTop_atTop.comp (tendsto_atTop_of_leadingCoeff_nonneg hdeg hP)
  · exact tendsto_abs_atBot_atTop.comp (tendsto_atBot_of_leadingCoeff_nonpos hdeg hP)

theorem isBoundedUnder_abs_atTop_iff :
    (IsBoundedUnder (· ≤ ·) atTop (|P.eval ·|)) ↔ P.degree ≤ 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨|P.coeff 0|, ?_⟩⟩
  · contrapose! h
    exact not_isBoundedUnder_of_tendsto_atTop (abs_tendsto_atTop h)
  · rw! [eq_C_of_degree_le_zero h]
    simp

theorem abs_tendsto_atTop_iff : Tendsto (|P.eval ·|) atTop atTop ↔ 0 < P.degree :=
  ⟨fun h ↦ not_le.mp (mt isBoundedUnder_abs_atTop_iff.mpr
    (not_isBoundedUnder_of_tendsto_atTop h)), abs_tendsto_atTop⟩

theorem tendsto_nhds_iff [TopologicalSpace F] [OrderTopology F] {c : F} :
    Tendsto P.eval atTop (𝓝 c) ↔ P.leadingCoeff = c ∧ P.degree ≤ 0 := by
  by_cases hz : P = 0
  · simp [hz]
  rw [tendsto_nhds_iff_of_tendsto_div_nhds_one (tendsTo_atTop_div_nhds_one hz),
    tendsto_const_mul_pow_nhds_iff (by grind [leadingCoeff_eq_zero])]
  grind [natDegree_eq_zero_iff_degree_le_zero]

end PolynomialAtTop

section PolynomialAtBot

theorem tendsTo_atBot_div_nhds_one [TopologicalSpace F] [OrderTopology F] (hP : P ≠ 0) :
    Tendsto (fun x ↦ P.eval x / (P.leadingCoeff * x ^ P.natDegree)) atBot (𝓝 1) := by
  convert ((P.comp (-X)).tendsTo_atTop_div_nhds_one (by simpa)).comp
    tendsto_neg_atBot_atTop with x
  nth_rw 2 [show x = -1 * -x by simp]
  simp [↓mul_pow, natDegree_comp]
  ring

theorem abs_tendsto_atBot (hdeg : 0 < P.degree) : Tendsto (|P.eval ·|) atBot atTop := by
  simpa [← tendsto_comp_neg_atTop_iff] using ((P.comp (-X)).abs_tendsto_atTop (by simp [hdeg]))

theorem isBoundedUnder_abs_atBot_iff :
    (IsBoundedUnder (· ≤ ·) atBot (|P.eval ·|)) ↔ P.degree ≤ 0 := by
  rw [← Filter.map_neg_atTop, Filter.isBoundedUnder_map_iff]
  simpa [Function.comp_def] using (P.comp (-X)).isBoundedUnder_abs_atTop_iff

theorem abs_tendsto_atBot_iff : Tendsto (|P.eval ·|) atBot atTop ↔ 0 < P.degree := by
  simpa [← tendsto_comp_neg_atTop_iff] using (P.comp (-X)).abs_tendsto_atTop_iff

end PolynomialAtBot

section PolynomialDivAtTop

theorem div_tendsTo_atTop_div_nhds_one [TopologicalSpace F] [OrderTopology F]
    (hP : P ≠ 0) (hQ : Q ≠ 0) :
    Tendsto (fun x ↦ (P.eval x / Q.eval x) /
      (P.leadingCoeff / Q.leadingCoeff * x ^ (P.natDegree - Q.natDegree : ℤ))) atTop (𝓝 1) := by
  convert ((tendsTo_atTop_div_nhds_one hP).div (tendsTo_atTop_div_nhds_one hQ) (by simp)).congr' ?_
  · simp
  · filter_upwards [eventually_ne_atTop 0]
    grind [Pi.div_apply, zpow_sub₀, zpow_natCast]

theorem div_tendsto_atTop_zero_iff_degree_lt [TopologicalSpace F] [OrderTopology F] (hQ : Q ≠ 0) :
    Tendsto (fun x ↦ P.eval x / Q.eval x) atTop (𝓝 0) ↔ P.degree < Q.degree := by
  by_cases hP : P = 0
  · simp_all [bot_lt_iff_ne_bot]
  rw [tendsto_nhds_iff_of_tendsto_div_nhds_one (div_tendsTo_atTop_div_nhds_one hP hQ),
    tendsto_const_mul_zpow_atTop_nhds_iff (by grind [leadingCoeff_eq_zero])]
  simp_all [natDegree_lt_natDegree_iff]

theorem div_tendsto_atTop_zero_of_degree_lt [TopologicalSpace F] [OrderTopology F]
    (hdeg : P.degree < Q.degree) :
    Tendsto (fun x ↦ P.eval x / Q.eval x) atTop (𝓝 0) :=
  (div_tendsto_atTop_zero_iff_degree_lt (by grind [degree_eq_bot])).mpr hdeg

theorem div_tendsto_atTop_leadingCoeff_div_iff_degree_eq [TopologicalSpace F] [OrderTopology F]
    (hP : P ≠ 0) (hQ : Q ≠ 0) :
    Tendsto (fun x ↦ P.eval x / Q.eval x) atTop (𝓝 (P.leadingCoeff / Q.leadingCoeff)) ↔
    P.degree = Q.degree := by
  rw [tendsto_nhds_iff_of_tendsto_div_nhds_one
    (div_tendsTo_atTop_div_nhds_one hP (by grind [degree_eq_bot])),
    tendsto_const_mul_zpow_atTop_nhds_iff (by grind [leadingCoeff_eq_zero])]
  grind [leadingCoeff_eq_zero, degree_eq_natDegree, Nat.cast_inj]

theorem div_tendsto_atTop_leadingCoeff_div_of_degree_eq [TopologicalSpace F] [OrderTopology F]
    (hdeg : P.degree = Q.degree) :
    Tendsto (fun x ↦ P.eval x / Q.eval x) atTop (𝓝 (P.leadingCoeff / Q.leadingCoeff)) := by
  by_cases hP : P = 0
  · simp [hP]
  exact (div_tendsto_atTop_leadingCoeff_div_iff_degree_eq hP (by grind [degree_eq_bot])).mpr hdeg

theorem div_tendsto_atTop_iff_degree_gt (hQ : Q ≠ 0) :
    Tendsto (fun x ↦ P.eval x / Q.eval x) atTop atTop ↔
    Q.degree < P.degree ∧ 0 ≤ P.leadingCoeff / Q.leadingCoeff := by
  let := Preorder.topology F
  have : OrderTopology F := ⟨rfl⟩
  by_cases hP : P = 0
  · suffices ¬ Tendsto (fun _ ↦ (0 : F)) (atTop : Filter F) atTop by simp_all
    exact tendsto_const_pure.not_tendsto (disjoint_pure_atTop 0)
  rw [tendsto_atTop_iff_of_tendsto_div_nhds_one
    (div_tendsTo_atTop_div_nhds_one hP hQ),
    tendsto_const_mul_zpow_atTop_atTop_iff]
  simp_all [natDegree_lt_natDegree_iff, le_iff_lt_or_eq']

theorem div_tendsto_atTop_of_degree_gt' (hdeg : Q.degree < P.degree)
    (hpos : 0 < P.leadingCoeff / Q.leadingCoeff) :
    Tendsto (fun x ↦ P.eval x / Q.eval x) atTop atTop :=
  (div_tendsto_atTop_iff_degree_gt (fun _ ↦ by simp_all)).mpr ⟨hdeg, hpos.le⟩

theorem div_tendsto_atTop_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q ≠ 0)
    (hnng : 0 ≤ P.leadingCoeff / Q.leadingCoeff) :
    Tendsto (fun x ↦ P.eval x / Q.eval x) atTop atTop :=
  div_tendsto_atTop_of_degree_gt' hdeg
    (by grind [leadingCoeff_eq_zero, mul_eq_zero, degree_eq_bot])

theorem div_tendsto_atBot_iff_degree_gt (hQ : Q ≠ 0) :
    Tendsto (fun x ↦ P.eval x / Q.eval x) atTop atBot ↔
    Q.degree < P.degree ∧ P.leadingCoeff / Q.leadingCoeff ≤ 0 := by
  simp_rw [← tendsto_neg_atTop_iff, ← neg_div, ← eval_neg, div_tendsto_atTop_iff_degree_gt hQ]
  simp [neg_div]

theorem div_tendsto_atBot_of_degree_gt' (hdeg : Q.degree < P.degree)
    (hneg : P.leadingCoeff / Q.leadingCoeff < 0) :
    Tendsto (fun x ↦ P.eval x / Q.eval x) atTop atBot :=
  (div_tendsto_atBot_iff_degree_gt (fun _ ↦ by simp_all)).mpr ⟨hdeg, hneg.le⟩

theorem div_tendsto_atBot_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q ≠ 0)
    (hnps : P.leadingCoeff / Q.leadingCoeff ≤ 0) :
    Tendsto (fun x ↦ P.eval x / Q.eval x) atTop atBot :=
  div_tendsto_atBot_of_degree_gt' hdeg
    (by grind [leadingCoeff_eq_zero, mul_eq_zero, degree_eq_bot])

theorem abs_div_tendsto_atTop_atTop_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q ≠ 0) :
    Tendsto (fun x ↦ |P.eval x / Q.eval x|) atTop atTop := by
  by_cases! h : 0 ≤ P.leadingCoeff / Q.leadingCoeff
  · exact tendsto_abs_atTop_atTop.comp (div_tendsto_atTop_of_degree_gt hdeg hQ h)
  · exact tendsto_abs_atBot_atTop.comp (div_tendsto_atBot_of_degree_gt hdeg hQ h.le)

end PolynomialDivAtTop

section PolynomialDivAtBot

theorem div_tendsTo_atBot_div_nhds_one [TopologicalSpace F] [OrderTopology F]
    (hP : P ≠ 0) (hQ : Q ≠ 0) :
    Tendsto (fun x ↦ (P.eval x / Q.eval x) /
      (P.leadingCoeff / Q.leadingCoeff * x ^ (P.natDegree - Q.natDegree : ℤ))) atBot (nhds 1) := by
  convert ((P.comp (-X)).div_tendsTo_atTop_div_nhds_one (Q := Q.comp (-X))
    (by simpa) (by simpa)).comp tendsto_neg_atBot_atTop with x
  nth_rw 3 [show x = -1 * -x by simp]
  simp [↓mul_zpow, natDegree_comp, zpow_sub₀]
  field

theorem div_tendsto_atBot_zero_iff_degree_lt [TopologicalSpace F] [OrderTopology F] (hQ : Q ≠ 0) :
    Tendsto (fun x ↦ P.eval x / Q.eval x) atBot (𝓝 0) ↔ P.degree < Q.degree := by
  simpa [← tendsto_comp_neg_atTop_iff] using
    ((P.comp (-X)).div_tendsto_atTop_zero_iff_degree_lt (show Q.comp (-X) ≠ 0 by simpa))

theorem div_tendsto_atBot_zero_of_degree_lt [TopologicalSpace F] [OrderTopology F]
    (hdeg : P.degree < Q.degree) :
    Tendsto (fun x ↦ P.eval x / Q.eval x) atBot (𝓝 0) := by
  simpa [← tendsto_comp_neg_atTop_iff] using
    ((P.comp (-X)).div_tendsto_atTop_zero_of_degree_lt (Q := Q.comp (-X)) (by simpa))

theorem div_tendsto_atBot_leadingCoeff_div_of_degree_eq [TopologicalSpace F] [OrderTopology F]
    (hdeg : P.degree = Q.degree) :
    Tendsto (fun x ↦ P.eval x / Q.eval x) atBot (𝓝 (P.leadingCoeff / Q.leadingCoeff)) := by
  convert ((P.comp (-X)).div_tendsto_atTop_leadingCoeff_div_of_degree_eq (Q := Q.comp (-X))
      (by simpa)).comp tendsto_neg_atBot_atTop using 2 with x
  · simp
  · grind [comp_neg_X_leadingCoeff_eq, natDegree_eq_natDegree, pow_eq_zero_iff']

theorem abs_div_tendsto_atBot_atTop_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q ≠ 0) :
    Tendsto (fun x ↦ |P.eval x / Q.eval x|) atBot atTop := by
  simpa [← tendsto_comp_neg_atTop_iff] using
    (P.comp (-X)).abs_div_tendsto_atTop_atTop_of_degree_gt
      (by simpa) (show Q.comp (-X) ≠ 0 by simpa)

end PolynomialDivAtBot

end Polynomial
