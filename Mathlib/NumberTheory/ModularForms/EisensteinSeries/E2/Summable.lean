/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Defs
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-!
# Summability of E2

We collect here lemmas about the summability of the Eisenstein series `E2` that will be used to
prove how it transforms under the slash action.

-/

open UpperHalfPlane hiding I σ

open ModularForm EisensteinSeries TopologicalSpace intervalIntegral
  Metric Filter Function Complex MatrixGroups Finset ArithmeticFunction Set SummationFilter

open scoped Interval Real Topology BigOperators Nat ArithmeticFunction.sigma

noncomputable section

namespace EisensteinSeries

variable (z : ℍ)

private lemma G2_partial_sum_eq (N : ℕ) : ∑ m ∈ Icc (-N : ℤ) N, e2Summand m z =
    (2 * riemannZeta 2) + (∑ m ∈ range N, -8 * π ^ 2 *
    ∑' n : ℕ+, n * cexp (2 * π * I * z) ^ ((m + 1) * n : ℕ)) := by
  rw [sum_Icc_of_even_eq_range (e2Summand_even z), Finset.sum_range_succ', smul_add, two_mul]
  ring_nf
  have H (a : ℕ) := EisensteinSeries.qExpansion_identity_pnat (k := 1) (by grind)
    ⟨(a + 1) * z, by simpa [show 0 < a + (1 : ℝ) by positivity] using z.2⟩
  simp only [coe_mk_subtype, add_comm, Nat.reduceAdd, one_div, mul_comm, mul_neg, even_two,
    Even.neg_pow, Nat.factorial_one, Nat.cast_one, div_one, pow_one, e2Summand, eisSummand,
    Nat.cast_add, Fin.isValue, Matrix.cons_val_zero, Int.cast_add, Int.cast_natCast, Int.cast_one,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Int.reduceNeg, zpow_neg, mul_sum, Int.cast_zero,
    zero_mul, add_zero] at *
  congr
  · simpa using (two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even (by grind) even_two).symm
  · ext a
    norm_cast at *
    simp_rw [H a, ← tsum_mul_left, ← tsum_neg,ofReal_mul, ofReal_ofNat, mul_pow, I_sq, neg_mul,
      one_mul, Nat.cast_add, Nat.cast_one, mul_neg, ofReal_pow, ← exp_nsmul, nsmul_eq_mul,
      Nat.cast_mul]
    apply tsum_congr (fun b ↦ ?_)
    ring_nf
    grind [exp_add, neg_inj, mul_eq_mul_right_iff, OfNat.ofNat_ne_zero]

private lemma aux_G2_tendsto : Tendsto (fun N ↦ ∑ m ∈ range N, -8 * π ^ 2 *
    ∑' (n : ℕ+), n * cexp (2 * π * I * z) ^ ((m + 1) * n : ℕ)) atTop
    (𝓝 (-8 * π ^ 2 * ∑' (n : ℕ+), (σ 1 n) * cexp (2 * π * I * z) ^ (n : ℕ))) := by
  have : -8 * π ^ 2 * ∑' (n : ℕ+), (σ 1 n) * cexp (2 * π * I * z) ^ (n : ℕ) =
    ∑' m : ℕ, (-8 * π ^ 2 * ∑' n : ℕ+, n * cexp (2 * π * I * z) ^ ((m + 1) * n)) := by
    have := tsum_prod_pow_eq_tsum_sigma 1 (norm_exp_two_pi_I_lt_one z)
    rw [tsum_pnat_eq_tsum_succ (f := fun d ↦
      ∑' (c : ℕ+), (c ^ 1 : ℂ) * cexp (2 * π * I * z) ^ (d * c : ℕ))] at this
    simp [← tsum_mul_left, ← this]
  rw [this]
  have hf : Summable fun m : ℕ ↦ (-8 * π ^ 2 *
      ∑' n : ℕ+, n * cexp (2 * π * I * z) ^ ((m + 1) * n : ℕ)) := by
    apply Summable.mul_left
    rw [← summable_pnat_iff_summable_succ
      (f := fun b ↦ ∑' (c : ℕ+), c * cexp (2 * π * I * z) ^ (b * c : ℕ))]
    apply ((summable_prod_mul_pow 1 (UpperHalfPlane.norm_exp_two_pi_I_lt_one z)).prod).congr
    simp [← exp_nsmul]
  simpa using (hf.hasSum).comp tendsto_finset_range

/-- The sum defining `G2` is Cauchy. -/
lemma G2_cauchySeq : CauchySeq (fun N : ℕ ↦ ∑ m ∈ Icc (-N : ℤ) N, e2Summand m z) := by
  simp_rw [G2_partial_sum_eq]
  apply CauchySeq.const_add
  apply Tendsto.cauchySeq (x := -8 * π ^ 2 * ∑' (n : ℕ+), (σ 1 n) * cexp (2 * π * I * z) ^ (n : ℕ))
  simpa using aux_G2_tendsto z

lemma summable_e2Summand_symmetricIcc : Summable (fun m ↦ e2Summand m z) (symmetricIcc ℤ ) := by
  simpa only [Summable, HasSum, symmetricIcc_eq_map_Icc_nat] using
    cauchySeq_tendsto_of_complete (G2_cauchySeq z)

/-Do we want this and the next not to be private?
I made it more general in case we want them elsewhere. -/
private lemma tendsto_zero_of_cauchySeq_sum_Icc {F : Type*} [NormedRing F] [NormSMulClass ℤ F]
    {f : ℤ → F} (hc : CauchySeq fun N : ℕ ↦ ∑ m ∈ Icc (-N : ℤ) N, f m) (hs : f.Even) :
    Tendsto f atTop (𝓝 0) := by
  simp only [cauchySeq_iff_le_tendsto_0, Metric.tendsto_atTop, gt_iff_lt, ge_iff_le,
    dist_zero_right, Real.norm_eq_abs] at *
  obtain ⟨g, hg, H, Hg⟩ := hc
  intro ε hε
  obtain ⟨N, hN⟩ := (Hg (2 * ε) (by positivity))
  refine ⟨N + 1, fun n hn ↦ ?_⟩
  have H2 := (H n.natAbs (n -1).natAbs N (by omega) (by omega))
  have H22 := sum_Icc_succ_eq_add_endpoints f (N := n.natAbs - 1)
  have H3 : ((n.natAbs - 1 : ℕ) : ℤ) = n - 1 := by
    omega
  rw [H3] at H22
  simp only [Nat.cast_natAbs, Int.cast_abs, Int.cast_eq, Int.cast_sub, Int.cast_one, sub_add_cancel,
    neg_sub, gt_iff_lt] at *
  have h1 : |n| = n := by
    rw [abs_eq_self]
    omega
  have h2 : |n - 1| = n - 1 := by
    rw [abs_eq_self, Int.sub_nonneg]
    omega
  rw [h1, h2, H22] at H2
  have := norm_smul (2 : ℤ) (f n)
  simp only [hs n, (two_mul (f n)).symm, neg_sub, dist_add_self_left, h1, h2, zsmul_eq_mul,
    Int.cast_ofNat, gt_iff_lt] at *
  simpa [this, Int.norm_eq_abs] using lt_of_le_of_lt (le_trans H2 (le_abs_self (g N)))
    (hN N (by rfl))

private lemma tendsto_zero_of_even_summable_symmetricIcc {F : Type*} [NormedRing F]
    [NormSMulClass ℤ F] {f : ℤ → F} (hs : f.Even) (hc : Summable f (symmetricIcc ℤ)) :
    Tendsto f atTop (𝓝 0) := by
  apply tendsto_zero_of_cauchySeq_sum_Icc ?_ hs
  have H := hc.hasSum
  apply Filter.Tendsto.cauchySeq (x := ∑'[symmetricIcc ℤ] (b : ℤ), f b)
  rw [HasSum, symmetricIcc_eq_map_Icc_nat] at H
  exact H

lemma summable_e2Summand_symmetricIco : Summable (fun m : ℤ ↦ e2Summand m z) (symmetricIco ℤ) := by
  apply summable_symmetricIco_of_multiplible_symmetricIcc (summable_e2Summand_symmetricIcc z)
  have h0 := tendsto_zero_of_cauchySeq_sum_Icc (G2_cauchySeq z) (e2Summand_even z)
  simpa using (Filter.Tendsto.neg h0).comp tendsto_natCast_atTop_atTop

lemma G2_eq_tsum_symmetricIco : G2 z = ∑'[symmetricIco ℤ] m, e2Summand m z := by
  rw [G2, tsum_symmetricIcc_eq_tsum_symmetricIco (summable_e2Summand_symmetricIcc z) ?_]
  have h0 := tendsto_zero_of_cauchySeq_sum_Icc (G2_cauchySeq z) (e2Summand_even z)
  simpa using (Filter.Tendsto.neg h0).comp tendsto_natCast_atTop_atTop

lemma cauchySeq_sum_Ico_e2Summand : CauchySeq fun N : ℕ ↦ ∑ m ∈ Ico (-N : ℤ) N, e2Summand m z := by
  apply Filter.Tendsto.cauchySeq (x := G2 z)
  obtain ⟨a, ha⟩ := summable_e2Summand_symmetricIco z
  rw [G2_eq_tsum_symmetricIco z, (Summable.hasSum_iff (summable_e2Summand_symmetricIco z)).mp ha]
  simp only [symmetricIco, ← Nat.map_cast_int_atTop, Filter.map_map, HasSum, tendsto_map'_iff] at *
  exact ha.congr (by simp)

lemma G2_eq_tsum_cexp : G2 z =
    (2 * riemannZeta 2) - 8 * π ^ 2 * ∑' n : ℕ+, σ 1 n * cexp (2 * π * I * z) ^ (n : ℕ) := by
  apply HasSum.tsum_eq
  simp only [sub_eq_add_neg, HasSum, symmetricIcc_eq_map_Icc_nat, tendsto_map'_iff]
  conv =>
    enter [1, N]
    simp [G2_partial_sum_eq z N]
  exact Filter.Tendsto.add (by simp) (by simpa using aux_G2_tendsto z)

end EisensteinSeries
