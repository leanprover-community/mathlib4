/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.UniformConvergence
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.Order.Interval.Finset.IccSums

/-!
# Eisenstein Series E2

We define the Eisenstein series `E2` of weight `2` and level `1` as a limit of partial sums
over non-symmetric intervals.

-/

open UpperHalfPlane hiding I

open ModularForm EisensteinSeries  TopologicalSpace  intervalIntegral
  Metric Filter Function Complex MatrixGroups Finset ArithmeticFunction Set

open scoped Interval Real Topology BigOperators Nat

noncomputable section


/-- This is an auxilary summand used to define the Eisenstein serires `G2`. -/
def e2Summand (m : ℤ) (z : ℍ) : ℂ := ∑' (n : ℤ), eisSummand 2 ![m, n] z

lemma e2Summand_summable (m : ℤ) (z : ℍ) : Summable (fun n => eisSummand 2 ![m, n] z) := by
  apply (linear_right_summable z m (k := 2) (by omega)).congr
  simp [eisSummand]

@[simp]
lemma e2Summand_zero_eq_riemannZeta_two (z : ℍ) : e2Summand 0 z = 2 * riemannZeta 2 := by
  simpa [e2Summand, eisSummand] using
    (two_riemannZeta_eq_tsum_int_inv_even_pow (k := 2) (by omega) (by simp)).symm

theorem e2Summand_even (z : ℍ) (n : ℤ) : e2Summand n z = e2Summand (-n) z := by
  simp only [e2Summand, ← tsum_int_eq_tsum_neg (fun a => eisSummand 2 ![-n, a] z)]
  congr
  ext b
  simp only [eisSummand, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Int.reduceNeg, zpow_neg, Int.cast_neg, neg_mul, inv_inj]
  rw_mod_cast [Int.cast_neg]
  ring

/-- The Eisenstein series of weight `2` and level `1` defined as the limit as `N` tends to
infinity of the partial sum of `m` in `[N,N)` of `e2Summand m`. This sum over symmetric
intervals is handy in showing it is Cauchy. -/
def G2 : ℍ → ℂ := fun z => limUnder atTop (fun N : ℕ => ∑ m ∈ Icc (-N : ℤ) N, e2Summand m z)

/-- The normalised Eisenstein series of weight `2` and level `1`. -/
def E2 : ℍ → ℂ := (1 / (2 * riemannZeta 2)) •  G2

/-- This function measures the defect in `E2` being a modular form. -/
def D2 (γ : SL(2, ℤ)) : ℍ → ℂ := fun z => (2 * π * I * γ 1 0) / (denom γ z)

lemma G2_partial_sum_eq (z : ℍ) (N : ℕ) : ∑ m ∈ Icc (-N : ℤ) N, e2Summand m z =
    (2 * riemannZeta 2) + (∑ m ∈ range N, 2 * (-2 * π * I) ^ 2  *
    ∑' n : ℕ+, n  * cexp (2 * π * I * (m + 1) * z) ^ (n : ℕ)) := by
  rw [sum_Icc_of_even_eq_range (e2Summand_even z), Finset.sum_range_succ', mul_add]
  nth_rw 2 [two_mul]
  ring_nf
  have (a : ℕ) := EisensteinSeries.qExpansion_identity_pnat (k := 1) (by omega)
    ⟨(a + 1) * z, by simpa [show  0 < a + (1 : ℝ) by positivity] using z.2⟩
  simp only [coe_mk_subtype, add_comm, Nat.reduceAdd, one_div, mul_comm, mul_neg, even_two,
    Even.neg_pow, Nat.factorial_one, Nat.cast_one, div_one, pow_one, e2Summand, eisSummand,
    Nat.cast_add, Fin.isValue, Matrix.cons_val_zero, Int.cast_add, Int.cast_natCast, Int.cast_one,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Int.reduceNeg, zpow_neg, mul_sum, Int.cast_zero,
    zero_mul, add_zero, I_sq, neg_mul, one_mul] at *
  congr
  · simpa using (two_riemannZeta_eq_tsum_int_inv_even_pow (k := 2) (by omega) (by simp)).symm
  · ext a
    norm_cast at *
    simp_rw [this a, ← tsum_mul_left, ← tsum_neg,ofReal_mul, ofReal_ofNat, mul_pow, I_sq, neg_mul,
      one_mul, Nat.cast_add, Nat.cast_one, mul_neg, ofReal_pow]
    grind

private lemma aux_tsum_identity (z : ℍ) : ∑' m : ℕ, (2 * (-2 * ↑π * I) ^ 2  *
    ∑' n : ℕ+, n * cexp (2 * ↑π * I * (m + 1) * z) ^ (n : ℕ))  =
    -8 * π ^ 2 * ∑' (n : ℕ+), (sigma 1 n) * cexp (2 * π * I * z) ^ (n : ℕ) := by
  have := tsum_prod_pow_cexp_eq_tsum_sigma 1 z
  rw [tsum_pnat_eq_tsum_succ (fun d =>
    ∑' (c : ℕ+), (c ^ 1 : ℂ) * cexp (2 * ↑π * I * d * z) ^ (c : ℕ))] at this
  simp only [neg_mul, even_two, Even.neg_pow, ← tsum_mul_left, ← this, Nat.cast_add, Nat.cast_one]
  apply tsum_congr
  intro b
  apply tsum_congr
  intro c
  simp only [mul_pow, I_sq, mul_neg, mul_one, neg_mul, neg_inj]
  ring

theorem G2_tendsto (z : ℍ) : Tendsto (fun N ↦ ∑ x ∈ range N, 2 * (2 * ↑π * I) ^ 2 *
    ∑' (n : ℕ+), n * cexp (2 * ↑π * I * (↑x + 1) * ↑z) ^ (n : ℕ)) atTop
    (𝓝 (-8 * ↑π ^ 2 * ∑' (n : ℕ+), ↑((σ 1) ↑n) * cexp (2 * ↑π * I * ↑z) ^ (n : ℕ))) := by
  rw [← aux_tsum_identity]
  have hf : Summable fun m : ℕ => ( 2 * (-2 * ↑π * I) ^ 2 *
      ∑' n : ℕ+, n ^ ((2 - 1)) * Complex.exp (2 * ↑π * I * (m + 1) * z) ^ (n : ℕ)) := by
    apply Summable.mul_left
    have := (summable_prod_aux 1 z).prod_symm.prod
    have h0 := pnat_summable_iff_summable_succ
      (f := fun b ↦ ∑' (c : ℕ+), c * cexp (2 * ↑π * I * ↑↑b * ↑z) ^ (c : ℕ))
    simp at *
    rw [← h0]
    apply this
  simpa using (hf.hasSum).comp tendsto_finset_range

lemma G2_cauchy (z : ℍ) : CauchySeq (fun N : ℕ ↦ ∑ m ∈ Icc (-N : ℤ) N, e2Summand m z) := by
  conv =>
    enter [1]
    ext n
    rw [G2_partial_sum_eq]
  apply CauchySeq.const_add
  apply Tendsto.cauchySeq (x := -8 * π ^ 2 * ∑' (n : ℕ+), (σ 1 n) * cexp (2 * π * I * z) ^ (n : ℕ))
  simpa using G2_tendsto z

lemma G2_q_exp (z : ℍ) : G2 z = (2 * riemannZeta 2) - 8 * π ^ 2 *
    ∑' n : ℕ+, σ 1 n * cexp (2 * π * I * z) ^ (n : ℕ) := by
  rw [G2, Filter.Tendsto.limUnder_eq, sub_eq_add_neg]
  conv =>
    enter [1]
    ext N
    rw [G2_partial_sum_eq z N]
  apply Filter.Tendsto.add (by simp) (by simpa using G2_tendsto z)

section transform

lemma tendsto_zero_of_cauchySeq_sum_Icc {F : Type*} [NormedRing F] [NormSMulClass ℤ F] {f : ℤ → F}
    (hc : CauchySeq fun N : ℕ ↦ ∑ m ∈ Icc (-N : ℤ) N, f m) (hs : ∀ n , f n = f (-n)) :
    Tendsto f atTop (𝓝 0) := by
  simp only [cauchySeq_iff_le_tendsto_0, Metric.tendsto_atTop, gt_iff_lt, ge_iff_le,
    dist_zero_right, Real.norm_eq_abs] at *
  obtain ⟨g, hg, H, Hg⟩ := hc
  intro ε hε
  obtain ⟨N, hN⟩ := (Hg (2 * ε) (by positivity))
  refine ⟨N + 1, fun n hn => ?_⟩
  have H3 := (H n.natAbs (n -1).natAbs N (by omega) (by omega))
  rw [sum_Icc_add_endpoints f (by omega)] at H3
  have h1 : |n| = n := by
    rw [abs_eq_self]
    omega
  have h2 : |n - 1| = n - 1 := by
    rw [abs_eq_self, Int.sub_nonneg]
    omega
  have := norm_smul (2 : ℤ) (f n)
  simp only [Nat.cast_natAbs, h1, Int.cast_eq, ← hs n, (two_mul (f n)).symm, neg_sub, h2,
    Int.cast_sub, Int.cast_one, dist_add_self_left, zsmul_eq_mul, Int.cast_ofNat] at *
  simpa [this, Int.norm_eq_abs] using lt_of_le_of_lt (le_trans H3 (le_abs_self (g N)))
    (hN N (by rfl))

lemma aux_tendsto_Ico (z : ℍ) : Tendsto (fun (N : ℕ) ↦ ∑ m ∈ Ico (-(N : ℤ)) N, e2Summand m z) atTop
    (𝓝 (G2 z)) := by
  apply Tendsto_of_sub_tendsto_zero _ (CauchySeq.tendsto_limUnder (G2_cauchy z))
  have h0 := tendsto_zero_of_cauchySeq_sum_Icc (G2_cauchy z) (by apply e2Summand_even)
  conv =>
    enter [1]
    ext N
    rw [Pi.sub_apply, sum_Icc_eq_sum_Ico_succ _ (by omega), sub_add_cancel_left]
  simpa using  (Filter.Tendsto.neg h0).comp tendsto_natCast_atTop_atTop

lemma G2_Ico (z : ℍ) : G2 z = limUnder atTop (fun N : ℕ ↦ ∑ m ∈ Ico (-N : ℤ) N, e2Summand m z) := by
  apply symm
  rw [G2, Filter.Tendsto.limUnder_eq]
  apply Tendsto_of_sub_tendsto_zero _ (CauchySeq.tendsto_limUnder (G2_cauchy z))
  have h0 := tendsto_zero_of_cauchySeq_sum_Icc (G2_cauchy z) (by apply e2Summand_even)
  conv =>
    enter [1]
    ext N
    rw [Pi.sub_apply, sum_Icc_eq_sum_Ico_succ _ (by omega), sub_add_cancel_left]
  simpa using  (Filter.Tendsto.neg h0).comp tendsto_natCast_atTop_atTop

lemma aux_cauchySeq_Ico (z : ℍ) :
  CauchySeq fun N : ℕ ↦ ∑ m ∈ Finset.Ico (-N : ℤ) N, e2Summand m z := by
    apply Filter.Tendsto.cauchySeq
    apply ((Filter.limUnder_eq_iff (Exists.intro _ (aux_tendsto_Ico z))).mp (G2_Ico z).symm).congr
    simp

lemma limUnder_mul_const {α : Type*} [Preorder α] [(atTop : Filter α).NeBot] (f : α → ℂ)
    (hf : CauchySeq f) (c : ℂ) : c * (limUnder atTop f)= limUnder atTop (c • f) := by
  nth_rw 2 [Filter.Tendsto.limUnder_eq]
  apply Filter.Tendsto.const_mul
  refine CauchySeq.tendsto_limUnder hf

theorem aux_sum_Ico_S_indentity (z : ℍ) (N : ℕ) :
    ((z : ℂ) ^ 2)⁻¹ * (∑ x ∈ Ico (-N : ℤ) N, ∑' (n : ℤ), (((x : ℂ) * (-↑z)⁻¹ + n) ^ 2)⁻¹) =
    ∑' (n : ℤ), ∑ x ∈ Ico (-N : ℤ) N, (((n : ℂ) * z + x) ^ 2)⁻¹ := by
  simp_rw [inv_neg, mul_neg]
  rw [Finset.mul_sum, Summable.tsum_finsetSum]
  · congr
    ext n
    rw [← tsum_mul_left, ← tsum_int_eq_tsum_neg]
    apply tsum_congr
    intro d
    rw [← mul_inv]
    congr 1
    rw [show ((d : ℂ) * ↑z + ↑n) ^ 2 = (-↑d * ↑z - ↑n) ^ 2 by ring, ← mul_pow]
    simp only [Int.cast_neg, neg_mul]
    field_simp [mul_add, ne_zero z]
    ring
  · exact fun i hi =>
      EisensteinSeries.linear_left_summable (ne_zero z) (i : ℤ) (k := 2) (by omega)

lemma G2_S_act (z : ℍ) : (z.1 ^ 2)⁻¹ * G2 (ModularGroup.S • z) = limUnder (atTop)
    fun N : ℕ => (∑' (n : ℤ), ∑ m ∈ Ico (-N : ℤ) N, (1 / ((n : ℂ) * z + m) ^ 2)) := by
  rw [modular_S_smul, G2_Ico, limUnder_mul_const _ (aux_cauchySeq_Ico _)]
  congr
  ext N
  simpa [UpperHalfPlane.coe, e2Summand, eisSummand, UpperHalfPlane.mk] using
    (aux_sum_Ico_S_indentity z N)

end transform
