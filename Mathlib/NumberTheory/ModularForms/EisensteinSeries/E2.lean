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
import Mathlib.NumberTheory.IccSums
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Normed.Group.Tannery

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

private lemma tendsto_zero_of_cauchySeq_sum_Icc {F : Type*} [NormedRing F] [NormSMulClass ℤ F]
    {f : ℤ → F} (hc : CauchySeq fun N : ℕ ↦ ∑ m ∈ Icc (-N : ℤ) N, f m) (hs : ∀ n , f n = f (-n)) :
    Tendsto f atTop (𝓝 0) := by
  simp only [cauchySeq_iff_le_tendsto_0, Metric.tendsto_atTop, gt_iff_lt, ge_iff_le,
    dist_zero_right, Real.norm_eq_abs] at *
  obtain ⟨g, hg, H, Hg⟩ := hc
  intro ε hε
  obtain ⟨N, hN⟩ := (Hg (2 * ε) (by positivity))
  refine ⟨N + 1, fun n hn => ?_⟩
  have H2 := (H n.natAbs (n -1).natAbs N (by omega) (by omega))
  rw [sum_Icc_add_endpoints f (by omega)] at H2
  have h1 : |n| = n := by
    rw [abs_eq_self]
    omega
  have h2 : |n - 1| = n - 1 := by
    rw [abs_eq_self, Int.sub_nonneg]
    omega
  have := norm_smul (2 : ℤ) (f n)
  simp only [Nat.cast_natAbs, h1, Int.cast_eq, ← hs n, (two_mul (f n)).symm, neg_sub, h2,
    Int.cast_sub, Int.cast_one, dist_add_self_left, zsmul_eq_mul, Int.cast_ofNat] at *
  simpa [this, Int.norm_eq_abs] using lt_of_le_of_lt (le_trans H2 (le_abs_self (g N)))
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

lemma aux_cauchySeq_Ico (z : ℍ) : CauchySeq fun N : ℕ ↦ ∑ m ∈ Ico (-N : ℤ) N, e2Summand m z := by
  apply Filter.Tendsto.cauchySeq
  apply ((Filter.limUnder_eq_iff (Exists.intro _ (aux_tendsto_Ico z))).mp (G2_Ico z).symm).congr
  simp


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
    rw [← mul_inv,  ← mul_pow, ← neg_pow_two]
    congr
    field_simp [ne_zero z]
    simp
  · exact fun i hi =>
      EisensteinSeries.linear_left_summable (ne_zero z) (i : ℤ) (k := 2) (by omega)

lemma G2_S_act (z : ℍ) : (z.1 ^ 2)⁻¹ * G2 (ModularGroup.S • z) = limUnder atTop
    fun N : ℕ => (∑' (n : ℤ), ∑ m ∈ Ico (-N : ℤ) N, (1 / ((n : ℂ) * z + m) ^ 2)) := by
  rw [modular_S_smul, G2_Ico, limUnder.mul_const (aux_cauchySeq_Ico _)]
  congr
  ext N
  simpa [UpperHalfPlane.coe, e2Summand, eisSummand, UpperHalfPlane.mk] using
    (aux_sum_Ico_S_indentity z N)

lemma Ico_succ_eq (b : ℕ) : Finset.Ico (-(b+1) : ℤ) (b+1) = Finset.Ico (-(b : ℤ)) (b) ∪
    {-((b+1) : ℤ), (b : ℤ)} :=  by
  ext n
  simp
  omega

theorem telescope_aux (z : ℂ) (m : ℤ) (b : ℕ) :
  ∑ n ∈ Finset.Ico (-b : ℤ) b, (1 / ((m : ℂ) * ↑z + ↑n) - 1 / (↑m * ↑z + ↑n + 1)) =
    1 / (↑m * ↑z - ↑b) - 1 / (↑m * ↑z + ↑b) := by
  induction' b  with b ihb
  · aesop
  · simp only [Nat.cast_add, Nat.cast_one, one_div, Finset.sum_sub_distrib] at *
    rw [Ico_succ_eq, Finset.sum_union (by simp), Finset.sum_union (by simp),
      Finset.sum_pair (by omega), Finset.sum_pair (by omega), add_sub_add_comm, ihb]
    · simp only [neg_add_rev, Int.reduceNeg, Int.cast_add, Int.cast_neg, Int.cast_one,
        Int.cast_natCast]
      ring

theorem tendstozero_inv_linear (z : ℂ) (b : ℤ) :
    Tendsto (fun d : ℕ ↦ 1 / ((b : ℂ) * ↑z + ↑d)) atTop (𝓝 0) := by
  apply Asymptotics.IsBigO.trans_tendsto ?_ tendsto_inverse_atTop_nhds_zero_nat
  have := (Asymptotics.isBigO_sup.mp (Int.cofinite_eq ▸ linear_inv_isBigO_right b z)).2
  simpa [← Nat.map_cast_int_atTop, Asymptotics.isBigO_map] using this


theorem tendstozero_inv_linear_neg (z : ℍ) (b : ℤ) :
    Tendsto (fun d : ℕ ↦ 1 / ((b : ℂ) * ↑z - ↑d)) atTop (𝓝 0) := by
  have := (tendstozero_inv_linear z (-b)).neg
  simp only [Int.cast_neg, neg_mul, one_div, neg_zero, ← inv_neg] at *
  apply this.congr
  intro a
  ring

lemma limUnder_sum_eq_zero (z : ℍ) (m : ℤ) : limUnder atTop (fun N : ℕ =>
    ∑ n ∈ (Finset.Ico (-(N : ℤ)) (N : ℤ)), (1 / ((m : ℂ) * z + n) -  1 / (m * z + n + 1))) = 0 := by
  apply Filter.Tendsto.limUnder_eq
  conv =>
    enter [1]
    ext N
    rw [telescope_aux z m N]
  simpa using Filter.Tendsto.sub (tendstozero_inv_linear_neg z m) (tendstozero_inv_linear z m)


theorem int_tsum_pNat {α : Type*} [UniformSpace α] [CommRing α] [IsUniformAddGroup α]
  [CompleteSpace α] [T2Space α] (f : ℤ → α) (hf2 : Summable f) :
  ∑' n, f n = f 0 + ∑' n : ℕ+, f n + ∑' m : ℕ+, f (-m) := by
  rw [summable_int_iff_summable_nat_and_neg_add_zero] at hf2
  rw [tsum_of_add_one_of_neg_add_one]
  · simp [tsum_pnat_eq_tsum_succ (fun n => f n), tsum_pnat_eq_tsum_succ (fun n => f (-n))]
    ring
  · have hf21 := hf2.1
    rw [← summable_nat_add_iff (k := 1)] at hf21
    simpa using hf21
  · simpa using hf2.2


lemma summable_pnat_iff_summable_nat {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] {f : ℕ → G} : Summable (fun n : ℕ+ => f n) ↔ Summable f := by
  rw [pnat_summable_iff_summable_succ , summable_nat_add_iff]

private lemma linear_sub_linear_eq (z : ℍ) (a b m : ℤ) (hm : m ≠ 0) :
    1 / ((m : ℂ) * z + a) - 1 / (m * z + b) = (b - a) * (1 / ((m * z + a) * (m * z + b))) := by
  rw [← one_div_mul_sub_mul_one_div_eq_one_div_add_one_div]
  · simp
    ring
  · simpa using UpperHalfPlane.linear_ne_zero z (cd := ![m, a]) (by simp [hm])
  · simpa using UpperHalfPlane.linear_ne_zero z (cd := ![m, b]) (by simp [hm])

lemma summable_linear_sub_mul_linear_add' {z : ℂ} (hz : z ≠ 0) (c₁ c₂ : ℤ) :
    Summable fun n : ℤ ↦ ((n * z + c₁) * (n * z + c₂))⁻¹  := by
  apply summable_inv_of_isBigO_rpow_inv (a := 2) (by norm_cast)
  simp only [Real.rpow_two, abs_mul_abs_self, pow_two]
  simpa using (linear_inv_isBigO_left c₂ hz).mul (linear_inv_isBigO_left c₁ hz)

lemma summable_one_div_linear_sub_one_div_linear (z : ℍ) (a b : ℤ) :
    Summable fun m : ℤ ↦ 1 / (m * (z : ℂ) + a) - 1 / (m * z + b) := by
  have := Summable.mul_left  (b - a : ℂ) (summable_linear_sub_mul_linear_add' (ne_zero z) a b)
  rw [← Finset.summable_compl_iff (s := {0})] at *
  apply this.congr
  intro m
  rw [linear_sub_linear_eq z a b m (by grind)]
  simp

example (a b c : ℂ) : a + b = c ↔  b = -a + c := by
  exact Iff.symm eq_neg_add_iff_add_eq

private lemma aux_tsum_identity_2 (z : ℍ) (d : ℕ+) :
    ∑' (m : ℤ), (1 / ((m : ℂ) * z - d) - 1 / (m * z + d)) = -(2 / d) +
    ∑' m : ℕ+, (1 / ((m : ℂ) * z - d) + 1 / (-m * z + -d) - 1 / ((m : ℂ) * z + d) -
    1 / (-m * z + d)) := by
  rw [eq_neg_add_iff_add_eq (b := 2 / (d : ℂ))]
  rw [int_tsum_pNat]
  · simp only [Int.cast_zero, zero_mul, zero_sub, one_div, zero_add, Int.cast_natCast, Int.cast_neg,
      neg_mul]
    ring_nf
    rw [←  Summable.tsum_add]
    · grind
    · apply (summable_pnat_iff_summable_nat.mpr ((summable_int_iff_summable_nat_and_neg.mp
        (summable_one_div_linear_sub_one_div_linear z (-d) d)).1)).congr
      grind [Int.cast_natCast, Int.cast_neg, one_div]
    · apply (summable_pnat_iff_summable_nat.mpr ((summable_int_iff_summable_nat_and_neg.mp
        (summable_one_div_linear_sub_one_div_linear z (-d) d)).2)).congr
      grind [Int.cast_neg, Int.cast_natCast, neg_mul, one_div]
  · apply (summable_one_div_linear_sub_one_div_linear z (-d) d).congr
    grind [Int.cast_neg, Int.cast_natCast, one_div, sub_left_inj, inv_inj]

lemma nat_tendsto_pnat (f : ℕ → ℂ) (x : ℂ) (hf : Tendsto f atTop (𝓝 x)) :
  Tendsto (fun n : ℕ+ => f n) atTop (𝓝 x) := tendsto_comp_val_Ioi_atTop.mpr hf

private lemma aux_tsum_identity_3 (z : ℍ) (d : ℕ+) :
    ∑' m : ℕ+, ((1 / ((m : ℂ) * z - d) + 1 / (-m * z + -d)) - (1 / (m * z + d)) -
    1 / (-m * z + d)) = (2 / z) * ∑' m : ℕ+, ((1 / (-(d : ℂ) / z - m) + 1 / (-d / z + m))) := by
  rw [← Summable.tsum_mul_left]
  · congr
    funext m
    simp_rw [sub_eq_add_neg, ← div_neg]
    ring_nf
    rw [add_comm]
    field_simp [ne_zero z]
  · have := (Summable_cotTerm (x := -d / (z : ℂ))
      (by simpa using int_div_upperHalfPlane_mem_integerComplement z (-d) (by simp at *)))
    simp only [cotTerm, one_div] at *
    conv at this =>
      enter [1]
      ext n
      rw [show ((n : ℂ) + 1) = (n + 1 : ℕ) by simp]
    rw [summable_nat_add_iff (k := 1)
      (f := fun n => (-↑d / (z : ℂ) - ↑(n))⁻¹ + (-↑d / (z : ℂ) + ↑(n))⁻¹)] at this
    apply this.subtype

lemma pnat_div_upper (n : ℕ+) (z : ℍ) : 0 < (-(n : ℂ) / z).im := by
  simp only [div_im, neg_im, natCast_im, neg_zero, coe_re, zero_mul,
    zero_div, neg_re, natCast_re, coe_im, neg_mul, zero_sub, Left.neg_pos_iff, div_neg_iff]
  right
  simpa using ⟨z.2, ne_zero z⟩

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

lemma tendsto_zero_geometric_tsum {r : 𝕜} (hr : ‖r‖ < 1) :
    Tendsto (fun m : ℕ+ => ∑' (n : ℕ+), r ^ (n * m : ℕ)) atTop (𝓝 0) := by
  have := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (g := fun (n : ℕ+) => 0)
    (f := fun d n : ℕ+ => r ^ (n * d : ℕ)) (bound := fun n : ℕ+ => (‖r ^ (n : ℕ)‖))
  simp only [tsum_zero] at this
  apply this
  · have hs : Summable fun n : ℕ ↦ ‖r ^ n‖ := by simp [hr]
    apply hs.subtype
  · intro k
    have ht : Tendsto (fun x : ℕ ↦ r ^ (k * x)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simp [pow_mul, tendsto_pow_atTop_nhds_zero_iff, pow_lt_one_iff_of_nonneg, hr]
    exact tendsto_comp_val_Ioi_atTop.mpr ht
  · simp only [eventually_atTop, ge_iff_le, norm_pow]
    exact ⟨1, fun b hb k =>
      pow_le_pow_of_le_one (norm_nonneg _) hr.le (Nat.le_mul_of_pos_right k hb)⟩

lemma aux_tendsto_tsum_cexp_pnat (z : ℍ) :
    Tendsto (fun N : ℕ+ => ∑' (n : ℕ+), cexp (2 * π * I * (-N / z)) ^ (n : ℕ)) atTop (𝓝 0) := by
  have := tendsto_zero_geometric_tsum (UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨-1 / z,
    by simpa using (pnat_div_upper 1 z)⟩)
  simp only [← exp_nsmul, mul_neg, neg_div] at *
  apply this.congr
  intro n
  congr
  grind [one_div, coe_mk_subtype, mul_neg, smul_neg, nsmul_eq_mul, Nat.cast_mul, neg_inj]

private theorem aux_tendsto_tsum (z : ℍ) : Tendsto (fun n : ℕ => (2 / (z : ℂ) * ∑' (m : ℕ+),
    (1 / (-(n : ℂ) / z - m) + 1 / (-n / z + m)))) atTop (𝓝 (-2 * ↑π *I / z)) := by
  suffices Tendsto (fun n : ℕ+ => (2 / (z : ℂ) * ∑' (m : ℕ+),
      (1 / (-(n : ℂ) / z - m) + 1 / (-n / z + m)))) atTop (𝓝 (-2 * π * I / z)) by
    rw [← tendsto_comp_val_Ioi_atTop]
    exact this
  have H0 : (fun n : ℕ+ => (2 / z * ∑' (m : ℕ+), (1 / (-(n : ℂ) / z - m) + 1 / (-n / z + m)))) =
      (fun N : ℕ+ => (-2 * π * I / z) - (2 / z * (2 * π * I)) *
      (∑' n : ℕ+, cexp (2 * π * I * (-N / z)) ^ (n : ℕ)) + 2 / N) := by
    ext N
    let Z : ℍ := ⟨-N / z, pnat_div_upper N z⟩
    have h2 := cot_series_rep (UpperHalfPlane.coe_mem_integerComplement Z)
    rw [pi_mul_cot_pi_q_exp, ← sub_eq_iff_eq_add'] at h2
    simp only [coe_mk_subtype, one_div, inv_div, neg_mul, Z] at *
    rw [← h2, ← tsum_zero_pnat_eq_tsum_nat _
      (by simpa using norm_exp_two_pi_I_lt_one ⟨-N / z, pnat_div_upper N z⟩), mul_sub]
    field_simp [ne_zero z]
    ring
  rw [H0]
  nth_rw 2 [show -2 * π * I / z = (-2 * π * I / z) - (2 / z * (2 * π * I)) * 0 + 2 * 0 by ring]
  apply Tendsto.add (Tendsto.sub (by simp) ((aux_tendsto_tsum_cexp_pnat z).const_mul _))
  apply Tendsto.const_mul
  have H4 : Tendsto (fun x : ℕ ↦ 1 / (x : ℂ)) atTop (𝓝 0) := by
    simpa using tendstozero_inv_linear z 0
  rw [← tendsto_comp_val_Ioi_atTop] at H4
  simpa using H4


--PS3
lemma limUnder_tsum_eq (z : ℍ) : limUnder atTop (fun N : ℕ => ∑ n ∈ (Ico (-N : ℤ) N),
    ∑' m : ℤ , (1 / ((m : ℂ) * z + n) -  1 / (m * z + n + 1))) = -2 * π * I / z := by
  suffices Tendsto (fun N : ℕ+ ↦ ∑ n ∈ Ico (-N : ℤ) N,
    ∑' m : ℤ, (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1))) atTop (𝓝 (-2 * π * I / z)) by
    apply Filter.Tendsto.limUnder_eq
    exact tendsto_comp_val_Ioi_atTop.mp this
  have : (fun N : ℕ+ => ∑ n ∈ (Ico (-N : ℤ) N),
      ∑' m : ℤ , (1 / ((m : ℂ) * z + n) -  1 / (m * z + n + 1))) = (fun N : ℕ+ =>
      ∑' m : ℤ ,  ∑ n ∈ Ico (-N : ℤ) N, (1 / ((m : ℂ) * z + n) -  1 / (m * z + n + 1))) := by
    ext n
    rw [Summable.tsum_finsetSum]
    intro i hi
    apply (summable_one_div_linear_sub_one_div_linear z ((i : ℤ)) (i + 1 : ℤ)).congr
    grind [one_div, Int.cast_add, Int.cast_one, sub_right_inj, inv_inj]
  conv at this =>
    enter [2]
    ext n
    conv =>
      enter [1]
      ext m
      rw [telescope_aux z]
    rw [show (n : ℂ) = (n : ℕ+) by simp, aux_tsum_identity_2 z]
  rw [this, show -2 * π * Complex.I / z = 0 + -2 * π * I / z by ring]
  apply Tendsto.add
  · have : Tendsto (fun x : ℕ ↦ -(2 / (x : ℂ))) atTop (𝓝 0) := by
      simpa [tendsto_zero_iff_norm_tendsto_zero] using Filter.Tendsto.const_div_atTop
        (g := fun n : ℕ => ‖(n : ℂ)‖) (r := 2) (by simpa using tendsto_natCast_atTop_atTop)
    exact tendsto_comp_val_Ioi_atTop.mpr this
  · conv =>
      enter [1]
      ext n
      rw [aux_tsum_identity_3]
    exact nat_tendsto_pnat _ _ (aux_tendsto_tsum z)

lemma tsum_limUnder_eq (z : ℍ) : ∑' m : ℤ, (limUnder atTop (fun N : ℕ => ∑ n ∈ (Ico (-N : ℤ) N),
    (1 / ((m : ℂ) * z + n) -  1 / (m * z + n + 1)))) = 0 := by
  convert tsum_zero
  next m =>
  apply limUnder_sum_eq_zero

@[grind]
def δ (a b : ℤ) : ℂ := if a = 0 ∧ b = 0 then 1 else if a = 0 ∧ b = -1 then 2 else 0

@[simp, grind]
lemma δ_eq : δ 0 0 = 1 := by simp [δ]

@[simp, grind]
lemma δ_eq2 : δ 0 (-1) = 2 := by simp [δ]

@[grind]
lemma δ_neq (a b : ℤ) (h : a ≠ 0) : δ a b = 0 := by
  simp [δ, h]

lemma isBigO_linear' (z : ℍ) (a : ℕ) :
    (fun (m : Fin 2 → ℤ) => (((m 0 : ℂ) * z + m 1 + a))⁻¹) =O[cofinite]
    (fun m : (Fin 2 → ℤ) => ‖![m 0, m 1 + a]‖⁻¹) := by
  rw [Asymptotics.isBigO_iff]
  have h0 : z ∈ verticalStrip |z.re| (z.im) := by
    rw [mem_verticalStrip_iff]
    simp
  use ‖r ⟨⟨|z.re|, z.im⟩, z.2⟩‖⁻¹
  filter_upwards with m
  have := summand_bound_of_mem_verticalStrip (k := 1) (by simp) ![m 0, m 1 + a] z.2 h0
  simp [Real.rpow_neg_one] at *
  simp_rw [add_assoc]
  apply le_trans this
  nth_rw 2 [abs_eq_self.mpr]
  · apply le_of_eq
    simp
    left
    simp_rw [UpperHalfPlane.im]
    rfl
  · apply (r_pos _).le

lemma aux (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a⁻¹ ≤ c * b⁻¹ ↔ b ≤ c * a := by
  constructor
  intro h
  simp_rw [inv_eq_one_div] at h
  rw [mul_one_div, le_div_comm₀ _ hb] at h
  simp only [one_div, div_inv_eq_mul] at h
  apply h
  simp only [one_div, inv_pos]
  exact ha
  intro h
  simp_rw [inv_eq_one_div]
  rw [← div_le_comm₀ _ ha]
  simp only [one_div, mul_inv_rev, inv_inv]
  rw [propext (mul_inv_le_iff₀ hc), mul_comm]
  exact h
  simp only [one_div]
  apply mul_pos hc (inv_pos.mpr hb)

lemma norm_add_isBigO (a : ℤ) : (fun (m : Fin 2 → ℤ) => ‖![m 0, m 1 + a + 1]‖⁻¹) =O[cofinite]
    (fun m : (Fin 2 → ℤ) => ‖![m 0, m 1 + a]‖⁻¹) := by
  rw [Asymptotics.isBigO_iff]
  use 2
  rw [Filter.eventually_iff_exists_mem ]
  use { ![0,0], ![0,-(a + 1)],  ![0,-a]}ᶜ
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, mem_cofinite, compl_compl, finite_singleton,
    Finite.insert, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or, Fin.isValue, norm_inv,
    norm_norm, Nat.cast_natAbs, Int.cast_abs, and_imp, true_and]
  intro b HB1 HB2 HB3
  have ht : b = ![b 0, b 1] := by
    ext i
    fin_cases i <;> rfl
  rw [aux]
  · simp only [norm_eq_max_natAbs, Nat.cast_max, Matrix.cons_val_zero, Matrix.cons_val_one,
    max_le_iff]
    have : 2 * max ↑(b 0).natAbs ↑(b 1 + a + 1).natAbs =
        max (2 *(b 0)).natAbs (2 *(b 1 + a + 1)).natAbs := by
      simp_rw [Int.natAbs_mul]
      norm_cast
      simp
    refine ⟨?_ , ?_⟩
    · norm_cast at *
      rw [this]
      simp
      left
      norm_cast
      simp only [Int.natAbs_mul, Int.reduceAbs]
      apply Nat.le_mul_of_pos_left _ Nat.zero_lt_two
    norm_cast
    rcases eq_or_ne (b 1) (-(a + 1)) with hr | hr
    · norm_cast at *
      rw [this]
      simp only [Fin.isValue, le_sup_iff]
      left
      simp only [Fin.isValue, hr, neg_add_rev, Int.reduceNeg, neg_add_cancel_right, IsUnit.neg_iff,
        isUnit_one, Int.natAbs_of_isUnit, Int.natAbs_mul, Int.reduceAbs]
      have hb0 : b 0 ≠ 0 := by
        rw [ht, hr] at HB2
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, neg_add_rev, Int.reduceNeg,
          Matrix.vecCons_inj, and_true] at HB2
        by_contra hh
        simp only [Fin.isValue, hh, not_true_eq_false] at HB2
      norm_cast at *
      simp
      omega
    · norm_cast at *
      rw [this]
      simp only [Fin.isValue, le_sup_iff]
      right
      norm_cast
      omega
  · simp only [Fin.isValue, norm_pos_iff, ne_eq, Matrix.cons_eq_zero_iff, Matrix.zero_empty,
    and_true, not_and]
    intro h
    by_contra H
    rw [add_assoc] at H
    rw [@add_eq_zero_iff_eq_neg] at H
    rw [ht, h, H] at HB2
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, not_true_eq_false] at HB2
  · simp
    intro h H
    rw [@add_eq_zero_iff_eq_neg] at H
    rw [ht, h, H] at HB3
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, not_true_eq_false] at HB3
  · simp only [Nat.ofNat_pos]


lemma norm_add_isBigO2 (a : ℕ) : (fun (m : Fin 2 → ℤ) => ‖![m 0, m 1 + a]‖⁻¹) =O[cofinite]
    (fun m : (Fin 2 → ℤ) => ‖m‖⁻¹) := by
  induction' a with a ih
  · simp
    rw [show  (fun (m : Fin 2 → ℤ) ↦ ‖![m 0, m 1]‖⁻¹) = (fun m ↦ ‖m‖⁻¹) by ext n; rfl]
    exact Asymptotics.isBigO_refl (fun m ↦ ‖m‖⁻¹) cofinite
  · simp
    apply Asymptotics.IsBigO.trans _ ih
    have := norm_add_isBigO (a : ℤ)
    simp_rw [← add_assoc]
    apply this

lemma isBigO_linear (z : ℍ) (a : ℕ) :
    (fun (m : Fin 2 → ℤ) => (((m 0 : ℂ) * z + m 1 + a))⁻¹) =O[cofinite]
    (fun m : (Fin 2 → ℤ) => ‖m‖⁻¹) := by
  apply (isBigO_linear' z a ).trans (norm_add_isBigO2 a )

/-- If the inverse of a function `isBigO` to `(|(n : ℝ)| ^ a)⁻¹` for `1 < a`, then the function is
Summable. -/
lemma summable_inv_of_isBigO_rpow_norm_inv {f : (Fin 2 → ℤ) → ℂ} {a : ℝ} (hab : 2 < a)
    (hf : (fun n ↦ (f n)⁻¹) =O[cofinite] fun n ↦ (‖n‖ ^ a)⁻¹) : Summable fun n ↦ (f n)⁻¹ :=
  summable_of_isBigO
    ((summable_one_div_norm_rpow hab).congr fun b ↦ Real.rpow_neg (norm_nonneg b) a) hf

lemma G_2_alt_summable (z : ℍ) : Summable fun (m : Fin 2 → ℤ) =>
    (((m 0 : ℂ) * z + m 1) ^ 2 * (m 0 * z + m 1 + 1))⁻¹ := by
  have hk' : 2 < (3 : ℝ) := by linarith
  apply summable_inv_of_isBigO_rpow_norm_inv hk'
  simpa [pow_three, pow_two, ← mul_assoc] using ((isBigO_linear z 1).mul (isBigO_linear z 0)).mul
    (isBigO_linear z 0)


lemma G_2_alt_summable_δ (z : ℍ) : Summable fun (m : Fin 2 → ℤ) =>
    (1 / (((m 0 : ℂ) * z + m 1) ^ 2 * (m 0 * z + m 1 + 1)) + δ (m 0) (m 1)):= by
  let s : Finset (Fin 2 → ℤ) := { ![0,0], ![0,-1]}
  rw [← Finset.summable_compl_iff s]
  have := (G_2_alt_summable z).subtype sᶜ
  simp at *
  apply this.congr
  intro b
  simp at *
  have hb1 : b.1 ≠ ![0, 0] := by aesop
  have hb2 : b.1 ≠ ![0, -1] := by aesop
  simp [δ]
  split_ifs with h1 h2
  exfalso
  have hb : b.1 = ![0, 0] := by
    nth_rw 1 [← h1.1, ← h1.2]
    simp
    exact List.ofFn_inj.mp rfl
  exact hb1 hb
  exfalso
  have hb : b.1 = ![0, -1] := by
    nth_rw 1 [← h2.1, ← h2.2]
    simp
    exact List.ofFn_inj.mp rfl
  exact hb2 hb
  rfl

theorem G2_prod_summable1_δ (z : ℍ) (b : ℤ) :
    Summable fun c : ℤ ↦ ((b : ℂ) * ↑z + ↑c + 1)⁻¹ * (((b : ℂ) * ↑z + ↑c) ^ 2)⁻¹ + δ b c := by
  have := G_2_alt_summable_δ z
  simp only [Fin.isValue, one_div, mul_inv_rev] at this
  rw [← (finTwoArrowEquiv _).symm.summable_iff] at this
  apply this.prod_factor b


theorem extracted_2_δ (z : ℍ) (b : ℤ) : CauchySeq fun N : ℕ ↦
  ∑ n ∈ Finset.Ico (-↑N : ℤ) ↑N, (1 / (((b : ℂ) * ↑z + ↑n) ^ 2 * (↑b * ↑z + ↑n + 1)) + δ b n) := by
  apply Filter.Tendsto.cauchySeq (x := ∑' (x : ℤ),
        (((b  : ℂ) * ↑z + ↑x + 1)⁻¹ * (((b : ℂ) * ↑z + ↑x) ^ 2)⁻¹  + δ b x))
  have hA:= (G2_prod_summable1_δ z b).hasSum
  have ht := hA.comp tendsto_Ico_atTop_atTop
  simp at *
  apply ht

theorem extracted_3 (z : ℍ) (b : ℤ) : CauchySeq fun N : ℕ ↦
  ∑ n ∈ Finset.Ico (-↑N : ℤ) ↑N, (1 / ((b : ℂ) * ↑z + ↑n) - 1 / (↑b * ↑z + ↑n + 1)) := by sorry

theorem extracted_4 (z : ℍ) (b : ℤ) :
  CauchySeq fun N : ℕ ↦ ∑ n ∈ Finset.Ico (-↑N : ℤ) ↑N, (1 / ((b : ℂ) * ↑z + ↑n) ^ 2 ) := by
  apply Filter.Tendsto.cauchySeq (x := ∑' (x : ℤ), ((((b : ℂ) * ↑z + ↑x) ^ 2)⁻¹))
  sorry
  /- have hA:= (G2_summable_aux b z 2 (by norm_num)).hasSum
  have ht := hA.comp verga
  simp at *
  apply ht -/

theorem poly_id (z : ℍ) (b n : ℤ) :
  ((b : ℂ) * ↑z + ↑n + 1)⁻¹ * (((b : ℂ) * ↑z + ↑n) ^ 2)⁻¹ + (δ b n) +
    (((b : ℂ) * ↑z + ↑n)⁻¹ - ((b : ℂ) * ↑z + ↑n + 1)⁻¹) =
    (((b : ℂ) * ↑z + ↑n) ^ 2)⁻¹ := by
  by_cases h : b = 0 ∧ n = 0
  rw [h.1, h.2]
  simp
  simp at h
  by_cases hb : b = 0
  by_cases hn : n = -1
  simp [hb, hn]
  ring
  have hj := h hb
  have hd : δ 0 n = 0 := by
    simp [δ, hj, hn]
  simp [hd, hb]
  have hn0 : (n : ℂ) ≠ 0 := by aesop
  have hn1 : (n : ℂ) + 1 ≠ 0 := by
    norm_cast
    omega
  field_simp
  ring
  have : δ b n = 0 := by simp [δ, hb]
  rw [this]
  simp
  have h : ![(b : ℝ), n + 1] ≠ 0 := by
    aesop
  have hh : ![(b : ℝ), n ] ≠ 0 := by
    aesop
  have h0 : ((b : ℂ) * ↑z + ↑n + 1) ≠ 0 := by
    have := linear_ne_zero (cd := ![b, n + 1]) z h
    simp at this
    norm_cast at this
    rw [@AddSemigroup.add_assoc]
    aesop
  have h1 : ((b : ℂ) * ↑z + ↑n) ≠ 0 := by
    have := linear_ne_zero (cd := ![b, n]) z hh
    simpa using this
  field_simp [h0, h1]
  ring

lemma auxr (z : ℍ) (b : ℤ):
    ((limUnder atTop fun N : ℕ ↦
    ∑ n ∈ Finset.Ico (-N : ℤ) N, (1 / (((b : ℂ) * ↑z + ↑n) ^ 2 * (↑b * ↑z + ↑n + 1)) + δ b n)) +
    limUnder atTop fun N : ℕ ↦
    ∑ n ∈ Finset.Ico (-N : ℤ) N, (1 / ((b : ℂ) * ↑z + ↑n) - 1 / (↑b * ↑z + ↑n + 1))) =
    limUnder atTop fun N : ℕ ↦
    ∑ n ∈ Finset.Ico (-N : ℤ) N, (1 / ((b : ℂ) * ↑z + ↑n) ^ 2) := by
  have := limUnder.add (f := fun N : ℕ ↦
    ∑ n ∈ Finset.Ico (-N : ℤ) N, (1 / (((b : ℂ) * ↑z + ↑n) ^ 2 * (↑b * ↑z + ↑n + 1))+ δ b n))
    (g := fun N : ℕ ↦
    ∑ n ∈ Finset.Ico (-N : ℤ) N, (1 / ((b : ℂ) * ↑z + ↑n) - 1 / (↑b * ↑z + ↑n + 1)))
      (extracted_2_δ z b) (by apply extracted_3 z b)
  rw [this]
  apply limUnder_congr_eventually _ _ _
    (by apply CauchySeq.add (extracted_2_δ z b) (extracted_3 z b)) (by apply extracted_4 z b)
  simp only [one_div, mul_inv_rev, Pi.add_apply, eventually_atTop,
    ge_iff_le]
  use 1
  intro c hc
  rw [← Finset.sum_add_distrib ]
  congr
  ext n
  apply poly_id z b n



--this sum is now abs convergent. Idea is to subtract limUnder_sum_eq_zero from the G₂ defn.
lemma G2_alt_eq (z : ℍ) : G2 z = ∑' m : ℤ, ∑' n : ℤ,
    (1 / (((m : ℂ)* z +n)^2 * (m * z + n +1)) + δ m n) := by
    rw [G2]
    have :=  tsum_limUnder_eq z
    set t :=  ∑' m : ℤ, ∑' n : ℤ, (1 / (((m : ℂ)* z +n)^2 * (m * z + n +1)) + δ m n)
    rw [show t = t + 0 by ring, ← this]
    simp only [t]
    rw [← Summable.tsum_add]
    · rw [int_tsum_limUnder_Icc_atTop]
      · congr
        ext n
        congr
        ext m
        rw [e2Summand,int_tsum_limUnder_Ico_atTop, int_tsum_limUnder_Ico_atTop, auxr z m]
        · simp [eisSummand]
          rfl
        · have H := G2_prod_summable1_δ z m
          simpa using H
        · apply e2Summand_summable
      · have H := G_2_alt_summable_δ z
        rw [← (finTwoArrowEquiv _).symm.summable_iff] at H
        have ha := H.prod
        apply ha.congr
        intro b
        simpa using limUnder_sum_eq_zero z b
    · have H := G_2_alt_summable_δ z
      rw [← (finTwoArrowEquiv _).symm.summable_iff] at H
      have ha := H.prod
      apply ha.congr
      intro b
      simp only [Fin.isValue, one_div, mul_inv_rev, finTwoArrowEquiv_symm_apply, comp_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one]
    · have HS : Summable fun m : ℤ => (0 : ℂ) := by apply summable_zero
      apply HS.congr
      intro b
      symm
      apply limUnder_sum_eq_zero z b

lemma G2_inde_lhs (z : ℍ) : (z.1 ^ 2)⁻¹ * G2 (ModularGroup.S • z) - -2 * π * Complex.I / z =
  ∑' n : ℤ, ∑' m : ℤ, (1 / (((m : ℂ)* z +n)^2 * (m * z + n +1)) + δ m n) := by
  sorry
  /- rw [G2_S_act, ← PS3 z, tsum_limUnder_atTop, limUnder_sub]
  congr
  ext N
  simp only [one_div, Pi.sub_apply, mul_inv_rev]
  rw [Summable.tsum_finsetSum, ← Finset.sum_sub_distrib ]
  congr
  ext n
  rw [← Summable.tsum_sub]
  congr
  ext m
  have := poly_id z m n
  nth_rw 1 [← this]
  simp only [add_sub_cancel_right]
  · exact extracted_77 z n
  · simpa only [one_div] using (summable_pain z n)
  · intro i hi
    exact extracted_77 z i
  · conv =>
      enter [1]
      ext N
      rw [Summable.tsum_finsetSum (by intro i hi; simp only [one_div]; exact extracted_77 z i)]
    apply CauchySeq_Icc_iff_CauchySeq_Ico
    intro n
    nth_rw 2 [int_sum_neg]
    congr
    ext m
    simp only [one_div, Int.cast_neg, neg_mul, inv_inj]
    ring
    conv =>
      enter [1]
      ext N
      rw [← Summable.tsum_finsetSum (by intro i hi; simp only [one_div]; exact extracted_77 z i)]
    have := G2_cauchy ⟨-1 / z, by simpa using pnat_div_upper 1 z⟩
    have  hC := cauchy_seq_mul_const _ ((z : ℂ) ^ 2)⁻¹ (by simp [ne_zero z]) this
    apply hC.congr
    have H := extracted_66c z
    simp at *
    rw [← H]
    ext N
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, mul_eq_mul_left_iff, inv_eq_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff]
    left
    congr
    ext n
    congr
    ext m
    congr
    ring
  · apply extracted_6
  · have := G_2_alt_summable_δ z
    simp only [Fin.isValue, one_div, mul_inv_rev] at this
    rw [← swap_equiv.summable_iff, ← (finTwoArrowEquiv _).symm.summable_iff] at this
    have ht := Summable.prod this
    simp only [Fin.isValue, swap_equiv, Equiv.coe_fn_mk, finTwoArrowEquiv_symm_apply, comp_apply,
      swap_apply, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.cons_val_one, Matrix.cons_val_zero,
      one_div, mul_inv_rev] at *
    exact ht -/


lemma G2_alt_indexing_δ (z : ℍ) : ∑' (m : Fin 2 → ℤ),
    (1 / (((m 0 : ℂ) * z + m 1)^2 * (m 0 * z + m 1 + 1)) + δ (m 0) (m 1))  =
    ∑' m : ℤ, ∑' n : ℤ, (1 / (((m : ℂ)* z + n)^2 * (m * z + n +1)) + (δ m n)) := by
  rw [ ← (finTwoArrowEquiv _).symm.tsum_eq]
  simp
  refine Summable.tsum_prod' ?h ?h₁
  have := G_2_alt_summable_δ z
  simp at this
  rw [← (finTwoArrowEquiv _).symm.summable_iff] at this
  apply this
  intro b
  simp
  have := G_2_alt_summable_δ z
  simp only [Fin.isValue, one_div, mul_inv_rev] at this
  rw [← (finTwoArrowEquiv _).symm.summable_iff] at this
  apply this.prod_factor

lemma G2_alt_indexing2_δ (z : ℍ) : ∑' (m : Fin 2 → ℤ),
    (1 / (((m 0 : ℂ) * z + m 1)^2 * (m 0 * z + m 1 + 1)) + δ (m 0) (m 1))  =
    ∑' n : ℤ, ∑' m : ℤ, (1 / (((m : ℂ)* z +n)^2 * (m * z + n +1)) + δ m n) := by
  have := (G_2_alt_summable_δ z)
  simp at this
  rw [← (finTwoArrowEquiv _).symm.summable_iff] at this
  rw [ Summable.tsum_comm']
  rw [G2_alt_indexing_δ]
  apply this.congr
  intro b
  simp
  rfl
  intro b
  simp
  apply this.prod_factor
  intro c
  simp
  have H := (G_2_alt_summable_δ z)
  simp at this
  sorry
  /- rw [← swap_equiv.summable_iff] at H
  rw [← (finTwoArrowEquiv _).symm.summable_iff] at H
  simp [Fin.isValue, one_div, mul_inv_rev, swap_equiv, Equiv.coe_fn_mk,
    finTwoArrowEquiv_symm_apply] at H
  have := H.prod_factor c
  simp at this
  apply this -/


lemma G2_transf_aux (z : ℍ) : (z.1 ^ 2)⁻¹ * G2 (ModularGroup.S • z) - -2 * π * Complex.I / z =
  G2 z := by
  rw [G2_inde_lhs, G2_alt_eq z , ← G2_alt_indexing2_δ , G2_alt_indexing_δ]

end transform
