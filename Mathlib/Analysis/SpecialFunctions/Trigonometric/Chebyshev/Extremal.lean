/-
Copyright (c) 2025 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuval Filmus
-/
module

public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Chebyshev polynomials over the reals: some extremal properties

Chebyshev polynomials have largest leading coefficient,
following proof in https://math.stackexchange.com/a/978145/1277

## Main statements

* leadingCoeff_le_of_forall_abs_le_one: If `P` is a real polynomial of degree at most `n` and
  `|P (x)| ≤ 1` for all `x ∈ [-1, 1]` then the leading coefficient of `P` is at most `2 ^ (n - 1)`
* leadingCoeff_eq_iff_of_forall_abs_le_one: When `n ≥ 2`, equality holds iff `P = T_n`

## Implementation

By monotonicity of `2 ^ (n - 1)`, we can assume that `P` has degree exactly `n`.
Using Lagrange interpolation, we can give a formula for the leading coefficient of `P`
as a linear combination of the values of `P` on the Chebyshev nodes (sumNodes_eq_coeff).
The Chebyshev polynomial `T_n` has value `±1` on the nodes, with the same signs as the
coefficients of the linear combination (negOnePow_mul_leadingCoeffC_pos).
Since `|P (x)| ≤ 1` on the nodes, this implies that the leading coefficient of `P` is bounded
by that of `T_n`, which is known to equal `2 ^ (n - 1)`.
Moreover, equality holds iff `P` and `T_n` agree on the nodes, which implies that they coincide.
-/
@[expose] public section
namespace Polynomial.Chebyshev

open Polynomial Real

/-- For `n ≠ 0` and `i ≤ n`, `node n i` is one of the extremal points of the Chebyhsev `T`
polynomial over the interval `[-1, 1]`. -/
noncomputable def node (n i : ℕ) : ℝ := cos (i * π / n)

lemma node_eq_one {n : ℕ} : node n 0 = 1 := by simp [node]

lemma node_eq_neg_one {n : ℕ} (hn : n ≠ 0) : node n n = -1 := by
  have : n * π / n = π := by aesop
  simp [node, this]

lemma node_mem_Icc {n i : ℕ} : node n i ∈ Set.Icc (-1) 1 :=
  Set.mem_Icc.mpr ⟨neg_one_le_cos _, cos_le_one _⟩

lemma eval_T_real_node {n i : ℕ} (hi : i ∈ Finset.Iic n) :
    (T ℝ n).eval (node n i) = (-1) ^ i := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [show i = 0 by grind]
  have : (n : ℤ) * (i * π / n) = i * π := by norm_cast; field
  rw [node, T_real_cos, this, cos_nat_mul_pi]

lemma strictAntiOn_node (n : ℕ) :
    StrictAntiOn (node n ·) (Finset.range (n + 1)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  refine strictAntiOn_cos.comp_strictMonoOn ?_ (fun x hx => Set.mem_Icc.mpr ⟨by positivity, ?_⟩)
  · apply StrictMono.strictMonoOn
    exact StrictMono.mul_const
      (StrictMono.mul_const Nat.strictMono_cast (by positivity)) (by positivity)
  rw [Finset.mem_coe, Finset.mem_range_succ_iff] at hx
  rw [mul_div_assoc]
  nth_rewrite 2 [← mul_div_cancel₀ π (Nat.cast_ne_zero.mpr hn)]
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hx) (by positivity)

lemma node_lt {n i j : ℕ} (hj : j ≤ n) (hij : i < j) :
    node n j < node n i :=
  strictAntiOn_node n (Finset.mem_coe.mpr (Finset.mem_range_succ_iff.mpr (by grind)))
    (Finset.mem_coe.mpr (Finset.mem_range_succ_iff.mpr hj)) hij

lemma zero_lt_prod_node_sub_node {n i : ℕ} (hi : i ≤ n) :
    0 < (-1) ^ i * ∏ j ∈ (Finset.range (n + 1)).erase i, (node n i - node n j) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Nat.le_zero.mp hi]
  have h₁ : 0 < ∏ j ∈ Finset.range i, ((-1) * (node n i - node n j)) :=
    Finset.prod_pos (fun j hj => mul_pos_of_neg_of_neg neg_one_lt_zero <| sub_neg.mpr <|
    node_lt hi (Finset.mem_range.mp hj))
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range] at h₁
  have h₂ : 0 < ∏ j ∈ Finset.Ioc i n, (node n i - node n j) :=
    Finset.prod_pos (fun j hj => sub_pos.mpr <|
      node_lt (Finset.mem_Ioc.mp hj).2 (Finset.mem_Ioc.mp hj).1)
  have union : (Finset.range (n + 1)).erase i = (Finset.range i) ∪ Finset.Ioc i n := by grind
  have disjoint : Disjoint (Finset.range i) (Finset.Ioc i n) := by grind [Finset.disjoint_iff_ne]
  rw [union, Finset.prod_union disjoint, ← mul_assoc]
  exact mul_pos h₁ h₂

private lemma negOnePow_mul_le {α : ℝ} {i : ℕ} (hα : |α| ≤ 1) : (-1) ^ i * α ≤ 1 := by
  apply le_of_abs_le
  rwa [abs_mul, abs_neg_one_pow, one_mul]

private lemma negOnePow_mul_negOnePow_mul_cancel {α β : ℝ} {i : ℕ} :
    ((-1) ^ i * α) * ((-1) ^ i * β) = α * β := calc
  _ = ((-1) ^ i * (-1) ^ i) * α * β := by ring
  _ = α * β := by simp [← mul_pow]

/-- For a polynomial `P` and coefficient function `c`, `sumNodes n c P` is a linear combination
of `P` evaluated at the `n`'th order Chebyshev nodes, with coefficients taken from `c`. -/
noncomputable def sumNodes (n : ℕ) (c : ℕ → ℝ) (P : ℝ[X]) := ∑ i ≤ n, P.eval (node n i) * (c i)

theorem sumNodes_le_sumNodes_T {n : ℕ} {c : ℕ → ℝ}
    (hcnonneg : ∀ i ≤ n, 0 ≤ (-1) ^ i * (c i))
    {P : ℝ[X]} (hPbnd : ∀ x ∈ Set.Icc (-1) 1, |P.eval x| ≤ 1) :
    sumNodes n c P ≤ sumNodes n c (T ℝ n) := by
  rw [sumNodes, sumNodes]
  refine Finset.sum_le_sum (fun i hi => ?_)
  calc
    P.eval (node n i) * (c i) =
      ((-1) ^ i * P.eval (node n i)) * ((-1) ^ i * (c i)) :=
      negOnePow_mul_negOnePow_mul_cancel.symm
    _ ≤ 1 * ((-1) ^ i * (c i)) :=
      mul_le_mul_of_nonneg_right (negOnePow_mul_le (hPbnd _ node_mem_Icc))
      (hcnonneg i (Finset.mem_Iic.mp hi))
    _ = (T ℝ n).eval (node n i) * (c i) := by
      rw [eval_T_real_node hi, one_mul]

theorem sumNodes_eq_sumNodes_T_iff {n : ℕ} {c : ℕ → ℝ}
    (hcpos : ∀ i ≤ n, 0 < (-1) ^ i * (c i))
    {P : ℝ[X]} (hPdeg : P.degree ≤ n) (hPbnd : ∀ x ∈ Set.Icc (-1) 1, |P.eval x| ≤ 1) :
    (sumNodes n c P = sumNodes n c (T ℝ n)) ↔ P = T ℝ n := by
  refine ⟨fun h => ?_, by intro h; rw [h]⟩
  rw [sumNodes, sumNodes] at h
  apply eq_of_degrees_lt_of_eval_finset_eq ((Finset.range (n + 1)).image (node n ·))
  · apply lt_of_le_of_lt hPdeg
    rw [Nat.cast_lt, Finset.card_image_of_injOn (strictAntiOn_node n).injOn,
      Finset.card_range, Nat.lt_succ_iff]
  · rw [degree_T, Int.natAbs_natCast, Nat.cast_lt,
      Finset.card_image_of_injOn (strictAntiOn_node n).injOn,
      Finset.card_range, Nat.lt_succ_iff]
  replace h := ge_of_eq h
  contrapose! h
  obtain ⟨x, hx, hPx⟩ := h
  obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
  replace hi := Finset.mem_Iic.mpr (Finset.mem_range_succ_iff.mp hi)
  suffices ∑ i ≤ n, ((-1) ^ i * P.eval (node n i)) * ((-1) ^ i * c i) <
      ∑ i ≤ n, ((-1) ^ i * (T ℝ n).eval (node n i)) * ((-1) ^ i * c i) by
    simpa [negOnePow_mul_negOnePow_mul_cancel]
  have h_le {i : ℕ} (hi : i ∈ Finset.Iic n) :
    (-1) ^ i * P.eval (node n i) * ((-1) ^ i * c i) ≤
    (-1) ^ i * (T ℝ n).eval (node n i)  * ((-1) ^ i * c i) := by
    refine mul_le_mul_of_nonneg_right ?_ (le_of_lt (hcpos i (Finset.mem_Iic.mp hi)))
    rw [eval_T_real_node hi, ← neg_pow', neg_neg, one_pow]
    exact negOnePow_mul_le (hPbnd _ node_mem_Icc)
  refine Finset.sum_lt_sum (fun i hi => h_le hi) ⟨i, hi, lt_of_le_of_ne (h_le hi) ?_⟩
  have := ne_of_lt (hcpos i (Finset.mem_Iic.mp hi))
  grind => ring

/-- Coefficients use to reproduce the leading coefficient of a polynomial given its values on the
Chebyshev nodes. -/
private noncomputable def leadingCoeffC (n i : ℕ) :=
  (∏ j ∈ (Finset.range (n + 1)).erase i, (node n i - node n j))⁻¹

private theorem sumNodes_eq_coeff {n : ℕ} {P : ℝ[X]} (hP : P.degree ≤ n) :
    sumNodes n (leadingCoeffC n) P = P.coeff n := by
  simp_rw [sumNodes, leadingCoeffC]
  have : P.degree < (Finset.range (n + 1)).card := by
    rw [Finset.card_range]
    grw [hP]
    norm_cast
    simp
  convert (Lagrange.coeff_eq_sum (strictAntiOn_node n).injOn this).symm using 2
  · exact Eq.symm (Nat.range_succ_eq_Iic n)
  · simp

private theorem sumNodes_T_eq (n : ℕ) :
    sumNodes n (leadingCoeffC n) (T ℝ n) = 2 ^ (n - 1) := by
  rw [sumNodes_eq_coeff (by simp)]
  trans (T ℝ n).leadingCoeff
  · simp [leadingCoeff]
  · simp

private theorem negOnePow_mul_leadingCoeffC_pos {n i : ℕ} (hi : i ≤ n) :
    0 < (-1) ^ i * leadingCoeffC n i := by
  have := inv_pos_of_pos <| zero_lt_prod_node_sub_node hi
  rwa [mul_inv, ← inv_pow, inv_neg_one] at this

theorem coeff_le_of_forall_abs_le_one {n : ℕ} {P : ℝ[X]}
    (hPdeg : P.degree ≤ n) (hPbnd : ∀ x ∈ Set.Icc (-1) 1, |P.eval x| ≤ 1) :
    P.coeff n ≤ 2 ^ (n - 1) := by
  convert sumNodes_le_sumNodes_T
      (fun i hi => le_of_lt <| negOnePow_mul_leadingCoeffC_pos hi) hPbnd
  · rw [sumNodes_eq_coeff hPdeg]
  · rw [sumNodes_T_eq]

theorem leadingCoeff_le_of_forall_abs_le_one {n : ℕ} {P : ℝ[X]}
    (hPdeg : P.degree ≤ n) (hPbnd : ∀ x ∈ Set.Icc (-1) 1, |P.eval x| ≤ 1) :
    P.leadingCoeff ≤ 2 ^ (n - 1) := by
  by_cases P = 0
  case pos hP => simp [hP]
  case neg hP =>
    lift P.degree to ℕ using degree_ne_bot.mpr hP with d hd
    replace hPdeg : d ≤ n := (WithBot.coe_le rfl).mp hPdeg
    rw [leadingCoeff, natDegree_eq_of_degree_eq_some hd.symm]
    grw [coeff_le_of_forall_abs_le_one (le_of_eq hd.symm) hPbnd, hPdeg]
    norm_num

theorem coeff_eq_iff_of_forall_abs_le_one {n : ℕ} {P : ℝ[X]}
    (hPdeg : P.degree ≤ n) (hPbnd : ∀ x ∈ Set.Icc (-1) 1, |P.eval x| ≤ 1) :
    P.coeff n = 2 ^ (n - 1) ↔ P = T ℝ n := by
  convert sumNodes_eq_sumNodes_T_iff
      (fun i hi => negOnePow_mul_leadingCoeffC_pos hi) hPdeg hPbnd
  · rw [sumNodes_eq_coeff hPdeg]
  · rw [sumNodes_T_eq]

theorem leadingCoeff_eq_iff_of_forall_abs_le_one {n : ℕ} {P : ℝ[X]} (hn : 2 ≤ n)
    (hPdeg : P.degree ≤ n) (hPbnd : ∀ x ∈ Set.Icc (-1) 1, |P.eval x| ≤ 1) :
    P.leadingCoeff = 2 ^ (n - 1) ↔ P = T ℝ n := by
  refine ⟨fun hP => ?_, fun hP => by simp [hP]⟩
  apply (coeff_eq_iff_of_forall_abs_le_one hPdeg hPbnd).mp
  suffices hPdeg' : n ≤ P.degree by
    replace hPdeg' : P.degree = n := eq_of_le_of_ge hPdeg hPdeg'
    rwa [leadingCoeff, natDegree_eq_of_degree_eq_some hPdeg'] at hP
  lift P.degree to ℕ with d hd
  · contrapose! hP
    rw [degree_eq_bot.mp hP, leadingCoeff_zero]
    positivity
  replace hP := ge_of_eq hP
  contrapose! hP
  have : d - 1 < n - 1 := by grind [Nat.cast_withBot, WithBot.coe_le_coe, WithBot.coe_lt_coe]
  calc P.leadingCoeff ≤ 2 ^ (d - 1) := leadingCoeff_le_of_forall_abs_le_one (le_of_eq hd.symm) hPbnd
  _ < 2 ^ (n - 1) := by gcongr; norm_num

end Polynomial.Chebyshev
