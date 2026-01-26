/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/

module

public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Defs
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-!
# Summability of E2

We collect here lemmas about the summability of the Eisenstein series `E2` that will be used to
prove how it transforms under the slash action.

-/

open UpperHalfPlane hiding I σ

open Filter Complex Finset SummationFilter

open scoped Interval Real Topology BigOperators Nat ArithmeticFunction.sigma

@[expose] public noncomputable section

namespace EisensteinSeries

variable (z : ℍ)

local notation "𝕢" z:100 => cexp (2 * π * I * z)

private lemma G2_partial_sum_eq (N : ℕ) : ∑ m ∈ Icc (-N : ℤ) N, e2Summand m z =
    2 * riemannZeta 2 + ∑ m ∈ range N, -8 * π ^ 2 *
      ∑' n : ℕ+, n * 𝕢 z ^ ((m + 1) * n) := by
  rw [sum_Icc_of_even_eq_range (e2Summand_even z), Finset.sum_range_succ', smul_add,
    nsmul_eq_mul, Nat.cast_zero, e2Summand_zero_eq_two_riemannZeta_two]
  ring_nf
  simp only [e2Summand, eisSummand, add_comm, Nat.cast_add, Nat.cast_one, Fin.isValue,
    Matrix.cons_val_zero, Int.cast_add, Int.cast_natCast, Int.cast_one, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Int.reduceNeg, zpow_neg, mul_comm, mul_sum]
  congr with a
  have H2 := qExpansion_identity_pnat (k := 1) (by grind)
    ⟨(a + 1) * z, by simpa [show 0 < ((a + 1) : ℝ) by positivity] using z.2⟩
  simp only [coe_mk_subtype, add_comm, Nat.reduceAdd, one_div, mul_comm, mul_neg, even_two,
    Even.neg_pow, Nat.factorial_one, Nat.cast_one, div_one, pow_one] at H2
  simp_rw [zpow_ofNat, H2, ← tsum_mul_left, ← tsum_neg, ← exp_nsmul]
  refine tsum_congr fun b ↦ ?_
  ring_nf
  grind [I_sq, exp_add]

private lemma aux_G2_tendsto : Tendsto
    (fun N ↦ ∑ m ∈ range N, -8 * π ^ 2 * ∑' n : ℕ+, n * 𝕢 z ^ ((m + 1) * n)) atTop
    (𝓝 (-8 * π ^ 2 * ∑' n : ℕ+, σ 1 n * 𝕢 z ^ (n : ℕ))) := by
  have : -8 * π ^ 2 * ∑' n : ℕ+, σ 1 n * 𝕢 z ^ (n : ℕ) =
      ∑' m : ℕ, (-8 * π ^ 2 * ∑' n : ℕ+, n * 𝕢 z ^ ((m + 1) * n)) := by
    have := tsum_prod_pow_eq_tsum_sigma 1 (norm_exp_two_pi_I_lt_one z)
    rw [tsum_pnat_eq_tsum_succ (f := fun d ↦ ∑' c : ℕ+, c ^ 1 * 𝕢 z ^ (d * c : ℕ))] at this
    simp [← tsum_mul_left, ← this]
  rw [this]
  refine (Summable.mul_left _ ?_).hasSum.comp tendsto_finset_range
  rw [← summable_pnat_iff_summable_succ (f := fun b ↦ ∑' c : ℕ+, c * 𝕢 z ^ (b * c : ℕ))]
  apply (summable_prod_mul_pow 1 (norm_exp_two_pi_I_lt_one z)).prod.congr
  simp [← exp_nsmul]

lemma hasSum_e2Summand_symmetricIcc : HasSum (e2Summand · z)
    (2 * riemannZeta 2 - 8 * π ^ 2 * ∑' n : ℕ+, σ 1 n * 𝕢 z ^ (n : ℕ)) (symmetricIcc ℤ) := by
  simpa [HasSum, -symmetricIcc_filter, symmetricIcc_eq_map_Icc_nat, Function.comp_def,
    G2_partial_sum_eq] using (aux_G2_tendsto z).const_add _

lemma summable_e2Summand_symmetricIcc : Summable (e2Summand · z) (symmetricIcc ℤ) :=
  (hasSum_e2Summand_symmetricIcc z).summable

lemma G2_eq_tsum_cexp : G2 z = 2 * riemannZeta 2 - 8 * π ^ 2 * ∑' n : ℕ+, σ 1 n * 𝕢 z ^ (n : ℕ) :=
  (hasSum_e2Summand_symmetricIcc z).tsum_eq

lemma tendsto_e2Summand_atTop_nhds_zero : Tendsto (e2Summand · z) atTop (𝓝 0) :=
  (summable_e2Summand_symmetricIcc z).tendsto_zero_of_even_summable_symmetricIcc (e2Summand_even _)

lemma hasSum_e2Summand_symmetricIco : HasSum (e2Summand · z)
    (2 * riemannZeta 2 - 8 * π ^ 2 * ∑' n : ℕ+, σ 1 n * 𝕢 z ^ (n : ℕ)) (symmetricIco ℤ) := by
  apply (hasSum_e2Summand_symmetricIcc z).hasSum_symmetricIco_of_hasSum_symmetricIcc
  simpa using (tendsto_e2Summand_atTop_nhds_zero z).neg.comp tendsto_natCast_atTop_atTop

lemma summable_e2Summand_symmetricIco : Summable (e2Summand · z) (symmetricIco ℤ) :=
  (hasSum_e2Summand_symmetricIco z).summable

lemma G2_eq_tsum_symmetricIco : G2 z = ∑'[symmetricIco ℤ] m, e2Summand m z := by
  rw [G2, tsum_symmetricIcc_eq_tsum_symmetricIco (summable_e2Summand_symmetricIcc z)]
  simpa using (tendsto_e2Summand_atTop_nhds_zero z).neg.comp tendsto_natCast_atTop_atTop

end EisensteinSeries
