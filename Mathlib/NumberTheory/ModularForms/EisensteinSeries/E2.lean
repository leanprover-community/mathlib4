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
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.IntervalSums

/-!
# Eisenstein Series E2

We define the Eisenstein series `E2` of weight `2` and level `1` as a limit of partial sums
over non-symmetric intervals.

-/

open UpperHalfPlane hiding I

open ModularForm EisensteinSeries  TopologicalSpace  intervalIntegral
  Metric Filter Function Complex MatrixGroups Finset ArithmeticFunction Set SummationFilter

open scoped Interval Real Topology BigOperators Nat

noncomputable section

/-- This is an auxilary summand used to define the Eisenstein serires `G2`. -/
def e2Summand (m : ℤ) (z : ℍ) : ℂ := ∑' n, eisSummand 2 ![m, n] z

lemma e2Summand_summable (m : ℤ) (z : ℍ) : Summable (fun n ↦ eisSummand 2 ![m, n] z) := by
  apply (linear_right_summable z m (k := 2) (by grind)).congr
  simp [eisSummand]

@[simp]
lemma e2Summand_zero_eq_riemannZeta_two (z : ℍ) : e2Summand 0 z = 2 * riemannZeta 2 := by
  simpa [e2Summand, eisSummand] using
    (two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even (k := 2) (by grind) (by simp)).symm

theorem e2Summand_even (z : ℍ) (n : ℤ) : e2Summand n z = e2Summand (-n) z := by
  simp only [e2Summand, ← tsum_comp_neg (fun a ↦ eisSummand 2 ![-n, a] z)]
  congr
  ext b
  simp only [eisSummand, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Int.reduceNeg, zpow_neg, Int.cast_neg, neg_mul, inv_inj]
  rw_mod_cast [Int.cast_neg]
  ring

/-- The Eisenstein series of weight `2` and level `1` defined as the limit as `N` tends to
infinity of the partial sum of `m` in `[N,N]` of `e2Summand m`. This sum over symmetric
intervals is handy in showing it is Cauchy. -/
def G2 : ℍ → ℂ := fun z ↦ ∑'[symCondInt] m, e2Summand m z

/-- The normalised Eisenstein series of weight `2` and level `1`. -/
def E2 : ℍ → ℂ := (1 / (2 * riemannZeta 2)) •  G2

/-- This function measures the defect in `E2` being a modular form. -/
def D2 (γ : SL(2, ℤ)) : ℍ → ℂ := fun z ↦ (2 * π * I * γ 1 0) / (denom γ z)

private lemma G2_partial_sum_eq (z : ℍ) (N : ℕ) : ∑ m ∈ Icc (-N : ℤ) N, e2Summand m z =
    (2 * riemannZeta 2) + (∑ m ∈ range N, -8 * π ^ 2  *
    ∑' n : ℕ+, n  * cexp (2 * π * I  * z) ^ ((m + 1) * n : ℕ)) := by
  rw [sum_Icc_of_even_eq_range (e2Summand_even z), Finset.sum_range_succ', mul_add]
  nth_rw 2 [two_mul]
  ring_nf
  have (a : ℕ) := EisensteinSeries.qExpansion_identity_pnat (k := 1) (by grind)
    ⟨(a + 1) * z, by simpa [show  0 < a + (1 : ℝ) by positivity] using z.2⟩
  simp only [coe_mk_subtype, add_comm, Nat.reduceAdd, one_div, mul_comm, mul_neg, even_two,
    Even.neg_pow, Nat.factorial_one, Nat.cast_one, div_one, pow_one, e2Summand, eisSummand,
    Nat.cast_add, Fin.isValue, Matrix.cons_val_zero, Int.cast_add, Int.cast_natCast, Int.cast_one,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Int.reduceNeg, zpow_neg, mul_sum, Int.cast_zero,
    zero_mul, add_zero] at *
  congr
  · simpa using (two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even (by grind) even_two).symm
  · ext a
    norm_cast at *
    simp_rw [this a, ← tsum_mul_left, ← tsum_neg,ofReal_mul, ofReal_ofNat, mul_pow, I_sq, neg_mul,
      one_mul, Nat.cast_add, Nat.cast_one, mul_neg, ofReal_pow, ← exp_nsmul, nsmul_eq_mul,
      Nat.cast_mul]
    exact tsum_congr fun b ↦ by grind [exp_add]

private lemma aux_tsum_identity (z : ℍ) :
    -8 * π ^ 2 * ∑' (n : ℕ+), (σ 1 n) * cexp (2 * π * I * z) ^ (n : ℕ) =
    ∑' m : ℕ, (-8 * π ^ 2  * ∑' n : ℕ+, n * cexp (2 * π * I * z) ^ ((m + 1) * n)) := by
  have := tsum_prod_pow_eq_tsum_sigma 1 (norm_exp_two_pi_I_lt_one z)
  rw [tsum_pnat_eq_tsum_succ (f := fun d ↦
    ∑' (c : ℕ+), (c ^ 1 : ℂ) * cexp (2 * π * I * z) ^ (d * c : ℕ))] at this
  simp [← tsum_mul_left, ← this]

private lemma aux_G2_tendsto (z : ℍ) : Tendsto (fun N ↦ ∑ m ∈ range N, -8 * π ^ 2 *
    ∑' (n : ℕ+), n * cexp (2 * π * I * z) ^ ((m + 1) * n : ℕ)) atTop
    (𝓝 (-8 * π ^ 2 * ∑' (n : ℕ+), ((σ 1) n) * cexp (2 * π * I * z) ^ (n : ℕ))) := by
  rw [ aux_tsum_identity]
  have hf : Summable fun m : ℕ ↦ (-8 * π ^ 2 *
      ∑' n : ℕ+, n * cexp (2 * π * I * z) ^ ((m + 1) * n : ℕ)) := by
    apply Summable.mul_left
    have := (summable_prod_mul_pow 1 (by apply UpperHalfPlane.norm_exp_two_pi_I_lt_one z)).prod
    have h0 := summable_pnat_iff_summable_succ
      (f := fun b ↦ ∑' (c : ℕ+), c * cexp (2 * π * I * z) ^ (b * c : ℕ))
    rw [← h0]
    apply this.congr
    simp [← exp_nsmul]
  simpa using (hf.hasSum).comp tendsto_finset_range

lemma G2_cauchy (z : ℍ) : CauchySeq (fun N : ℕ ↦ ∑ m ∈ Icc (-N : ℤ) N, e2Summand m z) := by
  conv =>
    enter [1, n]
    rw [G2_partial_sum_eq]
  apply CauchySeq.const_add
  apply Tendsto.cauchySeq (x := -8 * π ^ 2 * ∑' (n : ℕ+), (σ 1 n) * cexp (2 * π * I * z) ^ (n : ℕ))
  simpa using aux_G2_tendsto z

lemma Summable_symCondInt_G2 (z : ℍ) :
    Summable (fun m ↦ e2Summand m z) symCondInt := by
  simpa [Summable, HasSum, SymmetricConditional_eq_map_Icc_nat] using
    cauchySeq_tendsto_of_complete (G2_cauchy z)

lemma G2_q_exp (z : ℍ) :
    G2 z = (2 * riemannZeta 2) - 8 * π ^ 2 * ∑' n : ℕ+, σ 1 n * cexp (2 * π * I * z) ^ (n : ℕ) := by
  apply HasSum.tsum_eq
  simp only [sub_eq_add_neg, HasSum,SymmetricConditional_eq_map_Icc_nat, tendsto_map'_iff]
  conv =>
    enter [1, N]
    simp [G2_partial_sum_eq z N]
  exact Filter.Tendsto.add (by simp) (by simpa using aux_G2_tendsto z)

section transform

--Do we want this not to be private? I made it more general in case we want it elsewhere.
private lemma tendsto_zero_of_cauchySeq_sum_Icc {F : Type*} [NormedRing F] [NormSMulClass ℤ F]
    {f : ℤ → F} (hc : CauchySeq fun N : ℕ ↦ ∑ m ∈ Icc (-N : ℤ) N, f m) (hs : ∀ n , f n = f (-n)) :
    Tendsto f atTop (𝓝 0) := by
  simp only [cauchySeq_iff_le_tendsto_0, Metric.tendsto_atTop, gt_iff_lt, ge_iff_le,
    dist_zero_right, Real.norm_eq_abs] at *
  obtain ⟨g, hg, H, Hg⟩ := hc
  intro ε hε
  obtain ⟨N, hN⟩ := (Hg (2 * ε) (by positivity))
  refine ⟨N + 1, fun n hn ↦ ?_⟩
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

lemma Summable_IccFilter_G2_Ico (z : ℍ) : Summable (fun m : ℤ ↦ e2Summand m z) (IcoFilter ℤ) := by
  apply summable_IcoFilter_of_multiplible_symCondInt (Summable_symCondInt_G2 z)
  have h0 := tendsto_zero_of_cauchySeq_sum_Icc (G2_cauchy z) (by apply e2Summand_even)
  simpa using (Filter.Tendsto.neg h0).comp tendsto_natCast_atTop_atTop

lemma G2_eq_tsum_IcoFilter (z : ℍ) : G2 z = ∑'[IcoFilter ℤ] m, e2Summand m z := by
  rw [G2, tsum_symCondInt_eq_tsum_IcoFilter (Summable_symCondInt_G2 z) ?_]
  have h0 := tendsto_zero_of_cauchySeq_sum_Icc (G2_cauchy z) (by apply e2Summand_even)
  simpa using  (Filter.Tendsto.neg h0).comp tendsto_natCast_atTop_atTop

private lemma aux_tendsto_Ico (z : ℍ) :
    Tendsto (fun (N : ℕ) ↦ ∑ m ∈ Ico (-(N : ℤ)) N, e2Summand m z) atTop (𝓝 (G2 z)) := by
  have := Summable_IccFilter_G2_Ico z
  obtain ⟨a, ha⟩ := this
  have HA := ha
  rw [Summable.hasSum_iff] at ha
  · rw [G2_eq_tsum_IcoFilter z, ha]
    simp [HasSum, IcoFilter, ← Nat.map_cast_int_atTop, tendsto_map'_iff] at *
    apply HA.congr
    simp
  · exact Summable_IccFilter_G2_Ico z

private lemma aux_cauchySeq_Ico (z : ℍ) :
    CauchySeq fun N : ℕ ↦ ∑ m ∈ Ico (-N : ℤ) N, e2Summand m z :=
  Filter.Tendsto.cauchySeq (aux_tendsto_Ico z)

private lemma aux_sum_Ico_S_indentity (z : ℍ) (N : ℕ) :
    ((z : ℂ) ^ 2)⁻¹ * (∑ x ∈ Ico (-N : ℤ) N, ∑' (n : ℤ), (((x : ℂ) * (-↑z)⁻¹ + n) ^ 2)⁻¹) =
    ∑' (n : ℤ), ∑ x ∈ Ico (-N : ℤ) N, (((n : ℂ) * z + x) ^ 2)⁻¹ := by
  simp_rw [inv_neg, mul_neg]
  rw [Finset.mul_sum, Summable.tsum_finsetSum]
  · apply sum_congr rfl fun n hn ↦ ?_
    rw [← tsum_mul_left, ← tsum_comp_neg]
    apply tsum_congr fun d ↦ ?_
    rw [← mul_inv,  ← mul_pow, ← neg_pow_two]
    congr
    field_simp [ne_zero z]
    simp
  · exact fun i hi ↦ linear_left_summable (ne_zero z) (i : ℤ) (k := 2) (by omega)

lemma G2_S_act (z : ℍ) :
    Tendsto (fun N : ℕ ↦ (∑' (n : ℤ), ∑ m ∈ Ico (-N : ℤ) N, (1 / ((n : ℂ) * z + m) ^ 2))) atTop
    (𝓝 ((z.1 ^ 2)⁻¹ * G2 (ModularGroup.S • z))) := by
  rw [G2_eq_tsum_IcoFilter, ← tsum_mul_left]
  have : Summable (fun m : ℤ ↦ (z.1 ^ 2)⁻¹ * e2Summand m (ModularGroup.S • z)) (IcoFilter ℤ) := by
    apply Summable.mul_left
    apply Summable_IccFilter_G2_Ico (ModularGroup.S • z)
  have := (this.hasSum)
  simp only [HasSum, IcoFilter, tendsto_map'_iff, modular_S_smul, ← Nat.map_cast_int_atTop] at *
  apply this.congr
  intro N
  simpa [UpperHalfPlane.coe, e2Summand, eisSummand, UpperHalfPlane.mk, ← mul_sum]
    using (aux_sum_Ico_S_indentity z N)

lemma Ico_succ_eq (b : ℕ) : Finset.Ico (-(b+1) : ℤ) (b+1) = Finset.Ico (-(b : ℤ)) (b) ∪
    {-((b+1) : ℤ), (b : ℤ)} :=  by
  ext n
  simp only [neg_add_rev, Int.reduceNeg, Finset.mem_Ico, add_neg_le_iff_le_add, Finset.union_insert,
    Finset.union_singleton, neg_le_self_iff, Nat.cast_nonneg, Finset.Ico_insert_right,
    Finset.mem_insert, Finset.mem_Icc]
  omega

theorem telescope_aux (z : ℂ) (m : ℤ) (b : ℕ) :
    ∑ n ∈ Ico (-b : ℤ) b, (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1)) =
    1 / (m * z - b) - 1 / (m * z + b) := by
  induction b with
  | zero => aesop
  | succ b ihb =>
    simp only [Nat.cast_add, Nat.cast_one, one_div, Finset.sum_sub_distrib] at *
    rw [Ico_succ_eq, Finset.sum_union (by simp), Finset.sum_union (by simp),
      Finset.sum_pair (by omega), Finset.sum_pair (by omega), add_sub_add_comm]
    simp only [ihb, neg_add_rev, Int.reduceNeg, Int.cast_add, Int.cast_neg, Int.cast_one,
      Int.cast_natCast]
    ring

theorem tendstozero_inv_linear (z : ℂ) (b : ℤ) :
    Tendsto (fun d : ℕ ↦ 1 / ((b : ℂ) * z + d)) atTop (𝓝 0) := by
  apply Asymptotics.IsBigO.trans_tendsto ?_ tendsto_inverse_atTop_nhds_zero_nat
  have := (Asymptotics.isBigO_sup.mp (Int.cofinite_eq ▸ linear_inv_isBigO_right b z)).2
  simpa [← Nat.map_cast_int_atTop, Asymptotics.isBigO_map] using this

theorem tendstozero_inv_linear_sub (z : ℍ) (b : ℤ) :
    Tendsto (fun d : ℕ ↦ 1 / ((b : ℂ) * z - d)) atTop (𝓝 0) := by
  have := (tendstozero_inv_linear z (-b)).neg
  simp only [Int.cast_neg, neg_mul, one_div, neg_zero, ← inv_neg] at *
  exact this.congr (fun _ ↦ by ring)

lemma HasSum_IcoFilter_iff {f : ℤ → ℂ} {x : ℂ} :
    HasSum f x (IcoFilter ℤ) ↔ Tendsto ((fun N : ℕ ↦
    ∑ n ∈ (Finset.Ico (-(N : ℤ)) (N : ℤ)), f n)) atTop (𝓝 x) := by
  simp [HasSum, IcoFilter, ← Nat.map_cast_int_atTop, tendsto_map'_iff]
  constructor
  · intro h
    apply h.congr
    simp only [comp_apply, implies_true]
  · intro h
    simp at *
    apply h.congr
    simp

lemma G2_S_aa (z : ℍ) : ∑'[IcoFilter ℤ] n : ℤ, (∑' m : ℤ, (1 / ((m : ℂ) * z + n) ^ 2)) =
    ((z.1 ^ 2)⁻¹ * G2 (ModularGroup.S • z)) := by
  apply HasSum.tsum_eq
  rw [HasSum_IcoFilter_iff]
  have := G2_S_act z
  apply this.congr
  intro x
  rw [Summable.tsum_finsetSum]
  intro i hi
  simpa using linear_left_summable (ne_zero z) (i : ℤ) (k := 2) (by omega)

lemma tsumFilter_Ico_eq_zero (z : ℍ) (m : ℤ) :
    ∑'[IcoFilter ℤ] n : ℤ, (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1)) = 0 := by
  apply HasSum.tsum_eq
  simp only [HasSum_IcoFilter_iff] at *
  conv =>
    enter [1, N]
    rw [telescope_aux z m N]
  simpa using Filter.Tendsto.sub (tendstozero_inv_linear_sub z m) (tendstozero_inv_linear z m)

theorem int_tsum_pNat {α : Type*} [UniformSpace α] [CommRing α] [IsUniformAddGroup α]
  [CompleteSpace α] [T2Space α] {f : ℤ → α} (hf2 : Summable f) :
  ∑' n, f n = f 0 + ∑' n : ℕ+, f n + ∑' m : ℕ+, f (-m) := by
  rw [summable_int_iff_summable_nat_and_neg_add_zero, tsum_of_add_one_of_neg_add_one] at *
  · simp only [neg_add_rev, Int.reduceNeg, tsum_pnat_eq_tsum_succ (f := fun n ↦ f n), Nat.cast_add,
    Nat.cast_one, tsum_pnat_eq_tsum_succ (f := fun n ↦ f (-n)), add_left_inj]
    ring
  · have hf21 := hf2.1
    rw [← summable_nat_add_iff (k := 1)] at hf21
    simpa using hf21
  · simpa using hf2.2

lemma summable_pnat_iff_summable_nat {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] {f : ℕ → G} : Summable (fun n : ℕ+ ↦ f n) ↔ Summable f := by
  rw [summable_pnat_iff_summable_succ , summable_nat_add_iff]

private lemma linear_sub_linear_eq (z : ℍ) (a b m : ℤ) (hm : m ≠ 0) :
    1 / ((m : ℂ) * z + a) - 1 / (m * z + b) = (b - a) * (1 / ((m * z + a) * (m * z + b))) := by
  rw [← one_div_mul_sub_mul_one_div_eq_one_div_add_one_div]
  · simp only [one_div, add_sub_add_left_eq_sub, mul_inv_rev]
    ring
  · simpa using UpperHalfPlane.linear_ne_zero z (cd := ![m, a]) (by simp [hm])
  · simpa using UpperHalfPlane.linear_ne_zero z (cd := ![m, b]) (by simp [hm])

private lemma linear_sub_linear_eq' (z : ℍ) (b m : ℤ) (hm1 : b ≠ 0) (hm2 : b + 1 ≠ 0) :
    1 / ((m : ℂ) * z + b) - 1 / (m * z + b + 1) = 1 / ((m * z + b + 1) * (m * z + b)) := by
  rw [← one_div_mul_sub_mul_one_div_eq_one_div_add_one_div]
  · simp only [one_div, mul_inv_rev]
    ring
  · simpa using UpperHalfPlane.linear_ne_zero z (cd := ![m, b]) (by simp [hm1])
  · simpa [add_assoc] using UpperHalfPlane.linear_ne_zero z (cd := ![m, b + 1])
      (by simp; intro h; norm_cast at *)

lemma summable_one_div_linear_sub_one_div_linear (z : ℍ) (a b : ℤ) :
    Summable fun m : ℤ ↦ 1 / (m * (z : ℂ) + a) - 1 / (m * z + b) := by
  have := Summable.mul_left  (b - a : ℂ) (summable_linear_mul_linear (ne_zero z) a b)
  rw [← Finset.summable_compl_iff (s := {0})] at *
  apply this.congr
  intro m
  rw [linear_sub_linear_eq z a b m (by grind)]
  simp

lemma summable_one_div_linear_sub_one_div_linear_succ (z : ℍ) (a : ℤ) :
    Summable fun b : ℤ ↦ 1 / ((a : ℂ) * ↑z + ↑b) - 1 / ((a : ℂ) * ↑z + ↑b + 1) := by
  have := (summable_linear_add_mul_linear_add z a a)
  rw [← Finset.summable_compl_iff (s := {0, -1})] at *
  apply this.congr
  intro m
  have := linear_sub_linear_eq' z m a (by grind) (by grind)
  simp [add_assoc] at *
  rw [← this]

private lemma aux_tsum_identity_2 (z : ℍ) (d : ℕ+) :
    ∑' (m : ℤ), (1 / ((m : ℂ) * z - d) - 1 / (m * z + d)) = -(2 / d) +
    ∑' m : ℕ+, (1 / ((m : ℂ) * z - d) + 1 / (-m * z + -d) - 1 / ((m : ℂ) * z + d) -
    1 / (-m * z + d)) := by
  rw [eq_neg_add_iff_add_eq (b := 2 / (d : ℂ)), int_tsum_pNat]
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
      enter [1, n]
      rw [show ((n : ℂ) + 1) = (n + 1 : ℕ) by simp]
    rw [summable_nat_add_iff (k := 1)
      (f := fun n ↦ (-d / (z : ℂ) - (n))⁻¹ + (-d / (z : ℂ) + (n))⁻¹)] at this
    apply this.subtype

lemma pnat_div_upper (n : ℕ+) (z : ℍ) : 0 < (-(n : ℂ) / z).im := by
  simp only [div_im, neg_im, natCast_im, neg_zero, coe_re, zero_mul,
    zero_div, neg_re, natCast_re, coe_im, neg_mul, zero_sub, Left.neg_pos_iff, div_neg_iff]
  right
  simpa using ⟨z.2, ne_zero z⟩

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

lemma tendsto_zero_geometric_tsum {r : 𝕜} (hr : ‖r‖ < 1) :
    Tendsto (fun m : ℕ+ ↦ ∑' (n : ℕ+), r ^ (n * m : ℕ)) atTop (𝓝 0) := by
  have := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (g := fun (n : ℕ+) ↦ 0)
    (f := fun d n : ℕ+ ↦ r ^ (n * d : ℕ)) (bound := fun n : ℕ+ ↦ (‖r ^ (n : ℕ)‖))
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
    exact ⟨1, fun b hb k ↦
      pow_le_pow_of_le_one (norm_nonneg _) hr.le (Nat.le_mul_of_pos_right k hb)⟩

lemma aux_tendsto_tsum_cexp_pnat (z : ℍ) :
    Tendsto (fun N : ℕ+ ↦ ∑' (n : ℕ+), cexp (2 * π * I * (-N / z)) ^ (n : ℕ)) atTop (𝓝 0) := by
  have := tendsto_zero_geometric_tsum (UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨-1 / z,
    by simpa using (pnat_div_upper 1 z)⟩)
  simp only [← exp_nsmul, mul_neg, neg_div] at *
  apply this.congr fun n ↦ ?_
  congr
  grind [one_div, coe_mk_subtype, mul_neg, smul_neg, nsmul_eq_mul, Nat.cast_mul, neg_inj]

private theorem aux_tendsto_tsum (z : ℍ) : Tendsto (fun n : ℕ ↦ (2 / z *
    ∑' (m : ℕ+), (1 / (-(n : ℂ) / z - m) + 1 / (-n / z + m)))) atTop (𝓝 (-2 * π * I / z)) := by
  suffices Tendsto (fun n : ℕ+ ↦ (2 / (z : ℂ) * ∑' (m : ℕ+),
      (1 / (-(n : ℂ) / z - m) + 1 / (-n / z + m)))) atTop (𝓝 (-2 * π * I / z)) by
    rw [← tendsto_comp_val_Ioi_atTop]
    exact this
  have H0 : (fun n : ℕ+ ↦ (2 / z * ∑' (m : ℕ+), (1 / (-(n : ℂ) / z - m) + 1 / (-n / z + m)))) =
      (fun N : ℕ+ ↦ (-2 * π * I / z) - (2 / z * (2 * π * I)) *
      (∑' n : ℕ+, cexp (2 * π * I * (-N / z)) ^ (n : ℕ)) + 2 / N) := by
    ext N
    let Z : ℍ := ⟨-N / z, pnat_div_upper N z⟩
    have h2 := cot_series_rep (UpperHalfPlane.coe_mem_integerComplement Z)
    rw [pi_mul_cot_pi_q_exp, ← sub_eq_iff_eq_add'] at h2
    simp only [coe_mk_subtype, one_div, inv_div, neg_mul, Z] at *
    rw [← h2, ← tsum_zero_pnat_eq_tsum_nat
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

lemma tendsto_tsum_one_div_linear_sub_succ_eq (z : ℍ) : Tendsto (fun N : ℕ+ ↦ ∑ n ∈ Ico (-N : ℤ) N,
    ∑' m : ℤ, (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1))) atTop (𝓝 (-2 * π * I / z)) := by
  have : (fun N : ℕ+ ↦ ∑ n ∈ (Ico (-N : ℤ) N),
      ∑' m : ℤ , (1 / ((m : ℂ) * z + n) -  1 / (m * z + n + 1))) = (fun N : ℕ+ ↦
      ∑' m : ℤ ,  ∑ n ∈ Ico (-N : ℤ) N, (1 / ((m : ℂ) * z + n) -  1 / (m * z + n + 1))) := by
    ext n
    rw [Summable.tsum_finsetSum]
    intro i hi
    apply (summable_one_div_linear_sub_one_div_linear z ((i : ℤ)) (i + 1 : ℤ)).congr
    grind [one_div, Int.cast_add, Int.cast_one, sub_right_inj, inv_inj]
  conv at this =>
    enter [2, n]
    conv =>
      enter [1, m]
      rw [telescope_aux z]
    rw [show (n : ℂ) = (n : ℕ+) by simp, aux_tsum_identity_2 z]
  rw [this, show -2 * π * I / z = 0 + -2 * π * I / z by ring]
  apply Tendsto.add
  · have : Tendsto (fun x : ℕ ↦ -(2 / (x : ℂ))) atTop (𝓝 0) := by
      simpa [tendsto_zero_iff_norm_tendsto_zero] using Filter.Tendsto.const_div_atTop
        (g := fun n : ℕ ↦ ‖(n : ℂ)‖) (r := 2) (by simpa using tendsto_natCast_atTop_atTop)
    exact tendsto_comp_val_Ioi_atTop.mpr this
  · conv =>
      enter [1, n]
      rw [aux_tsum_identity_3]
    have HH := aux_tendsto_tsum z
    rw [← tendsto_comp_val_Ioi_atTop] at HH
    exact HH

--these are the two key lemmas

lemma tsumFilter_tsum_eq (z : ℍ) :
    ∑'[IcoFilter ℤ] n : ℤ, ∑' m : ℤ, (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1)) =
    -2 * π * I / z := by
  apply HasSum.tsum_eq
  have := (tendsto_tsum_one_div_linear_sub_succ_eq z)
  simp [HasSum, IcoFilter, ← Nat.map_cast_int_atTop, tendsto_map'_iff] at *
  suffices H :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ Ico (-N : ℤ) N,
     ∑' m : ℤ, (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1))) atTop (𝓝 (-2 * π * I / z)) by
    simp at *
    apply H.congr
    simp
  exact tendsto_comp_val_Ioi_atTop.mp (tendsto_tsum_one_div_linear_sub_succ_eq z)

lemma tsum_tsumFilter_eq (z : ℍ) :
    ∑' m : ℤ, (∑'[IcoFilter ℤ] n : ℤ, (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1))) = 0 := by
  convert tsum_zero
  apply tsumFilter_Ico_eq_zero

/-- This is an auxiliary correction term for proving how E2 transforms. It allows us to work with
nicer indexing sets for our infinite sums. -/
private def δ (x : Fin 2 → ℤ) : ℂ := if x = ![0,0] then 1 else if x = ![0, -1] then 2 else 0

@[simp]
private lemma δ_eq : δ ![0,0] = 1 := by simp [δ]

private lemma δ_eq2 : δ ![0, -1] = 2 := by simp [δ]

private lemma δ_neq (a b : ℤ) (h : a ≠ 0) : δ ![a,b] = 0 := by
  simp [δ, h]

/-- This gives term gives and alternative infinte sum for G2 which is absolutely convergent. -/
abbrev G2Term (z : ℍ) (m : Fin 2 → ℤ) : ℂ := (((m 0 : ℂ) * z + m 1) ^ 2 * (m 0 * z + m 1 + 1))⁻¹

lemma G_2_alt_summable (z : ℍ) : Summable (fun m ↦ (G2Term z m)) := by
  have hk' : 2 < (3 : ℝ) := by linarith
  apply summable_inv_of_isBigO_rpow_norm_inv hk'
  simpa [pow_three, pow_two, ← mul_assoc] using ((isBigO_linear_add_const_vec z 0 1).mul
    (isBigO_linear_add_const_vec z 0 0)).mul (isBigO_linear_add_const_vec z 0 0)

lemma G_2_alt_summable_δ (z : ℍ) : Summable fun (m : Fin 2 → ℤ) ↦ (G2Term z m + δ m):= by
  let s : Finset (Fin 2 → ℤ) := {![0,0], ![0,-1]}
  rw [← Finset.summable_compl_iff s]
  apply ((G_2_alt_summable z).subtype sᶜ).congr
  intro b
  have hb1 : b.1 ≠ ![0, 0] := by aesop
  have hb2 : b.1 ≠ ![0, -1] := by aesop
  simp [δ, hb1, hb2]

lemma G2_prod_summable1_δ (z : ℍ) (b : ℤ) : Summable fun c ↦ G2Term z ![b,c] + δ ![b, c] := by
  have := G_2_alt_summable_δ z
  simp only [G2Term, Fin.isValue, mul_inv_rev, ← (finTwoArrowEquiv _).symm.summable_iff,
    finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at *
  exact this.prod_factor b

theorem extracted_2_δ (z : ℍ) (b : ℤ) : CauchySeq fun N : ℕ ↦ ∑ n ∈ Ico (-N : ℤ) N,
    (G2Term z ![b,n] + δ ![b, n]) := by
  apply Filter.Tendsto.cauchySeq (x := ∑' (x : ℤ),
        (((b  : ℂ) * z + x + 1)⁻¹ * (((b : ℂ) * z + x) ^ 2)⁻¹  + δ ![b, x]))
  simpa [← Nat.map_cast_int_atTop] using (G2_prod_summable1_δ z b).hasSum.comp
    tendsto_Ico_atTop_atTop

theorem extracted_3 (z : ℍ) (b : ℤ) : CauchySeq fun N : ℕ ↦
  ∑ n ∈ Finset.Ico (-N : ℤ) N, (1 / ((b : ℂ) * z + n) - 1 / (b * z + n + 1)) := by
  simp_rw [telescope_aux ]
  apply Filter.Tendsto.cauchySeq
  simpa using Filter.Tendsto.sub (tendstozero_inv_linear_sub z b) (tendstozero_inv_linear z b)

lemma extracted_4 (z : ℍ) (b : ℤ) :
    CauchySeq fun N : ℕ ↦ ∑ n ∈ Ico (-N : ℤ) N, (1 / ((b : ℂ) * z + n) ^ 2 ) := by
  apply Filter.Tendsto.cauchySeq (x := ∑' (x : ℤ), ((((b : ℂ) * z + x) ^ 2)⁻¹))
  simpa [← Nat.map_cast_int_atTop] using
    ((linear_right_summable z b  (k := 2) (by norm_num)).hasSum).comp tendsto_Ico_atTop_atTop

lemma poly_id (z : ℍ) (b n : ℤ) : ((b : ℂ) * z + n + 1)⁻¹ * (((b : ℂ) * z + n) ^ 2)⁻¹ +
    (δ ![b, n]) + (((b : ℂ) * z + n)⁻¹ - ((b : ℂ) * z + n + 1)⁻¹) = (((b : ℂ) * z + n) ^ 2)⁻¹ := by
  by_cases h : b = 0 ∧ n = 0
  · simp_rw [h.1, h.2]
    simp
  · simp only [not_and] at h
    by_cases hb : b = 0
    · by_cases hn : n = -1
      · simp only [hb, Int.cast_zero, zero_mul, hn, Int.reduceNeg, Int.cast_neg, Int.cast_one,
        zero_add, neg_add_cancel, inv_zero, even_two, Even.neg_pow, one_pow, inv_one, mul_one,
        δ_eq2, inv_neg, sub_zero]
        ring
      · have hn0 : (n : ℂ) ≠ 0 := by aesop
        have hn1 : (n : ℂ) + 1 ≠ 0 := by norm_cast; omega
        simp only [hb, Int.cast_zero, zero_mul, zero_add, δ, Nat.succ_eq_add_one, Nat.reduceAdd,
          Matrix.vecCons_inj, h hb, and_true, and_false, ↓reduceIte, Int.reduceNeg, hn, add_zero]
        field_simp
        ring
    · simp only [δ, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.vecCons_inj, hb, and_true,
        false_and, ↓reduceIte, Int.reduceNeg, add_zero]
      have h0 : ((b : ℂ) * z + n + 1) ≠ 0 := by
        simpa [add_assoc] using linear_ne_zero (cd := ![b, n + 1]) z (by aesop)
      have h1 : ((b : ℂ) * z + n) ≠ 0 := by
        simpa using linear_ne_zero (cd := ![b, n]) z (by aesop)
      field_simp
      ring

--this sum is now abs convergent. Idea is to subtract limUnder_sum_eq_zero from the G2 defn.
lemma G2_alt_eq (z : ℍ) : G2 z = ∑' m, ∑' n, (G2Term z ![m, n] + δ ![m, n]) := by
  set t :=  ∑' m, ∑' n,  (G2Term z ![m, n] + δ ![m, n])
  rw [G2, show t = t + 0 by ring, ←   tsum_tsumFilter_eq z, ← Summable.tsum_add]
  · rw [← tsum_eq_of_summable_unconditional (L := symCondInt)]
    · congr
      ext a
      rw [e2Summand, tsum_eq_of_summable_unconditional (L := IcoFilter ℤ), ← Summable.tsum_add]
      · congr
        ext b
        simp [eisSummand, G2Term, poly_id z a b]
        rfl
      · apply G2_prod_summable1_δ
      · apply summable_one_div_linear_sub_one_div_linear_succ z a
      · apply summable_one_div_linear_sub_one_div_linear_succ z a
    · conv =>
        enter [1, N]
        rw [tsumFilter_Ico_eq_zero z N, add_zero]
      apply ((finTwoArrowEquiv _).symm.summable_iff.mpr (G_2_alt_summable_δ z)).prod
  · apply (((finTwoArrowEquiv _).symm.summable_iff.mpr (G_2_alt_summable_δ z)).prod).congr
    simp
  · apply summable_zero.congr
    intro b
    simp [← tsumFilter_Ico_eq_zero z b]

/-- The map that swaps the two co-ordinates of a `Fin 2 → α` -/
def swap {α : Type*} : (Fin 2 → α) → (Fin 2 → α) := fun x ↦ ![x 1, x 0]

@[simp]
lemma swap_apply {α : Type*} (b : Fin 2 → α) : swap b = ![b 1, b 0] := rfl

lemma swap_involutive {α : Type*} (b : Fin 2 → α) : swap (swap b) = b := by
  ext i
  fin_cases i <;> rfl

/-- An equivalence between `Fin 2 → α` and itself given by swapping the two co-ordinates -/
def swap_equiv {α : Type*} : Equiv (Fin 2 → α) (Fin 2 → α) := Equiv.mk swap swap
  (by rw [Function.LeftInverse]; apply swap_involutive)
  (by rw [Function.RightInverse]; apply swap_involutive)

lemma G2_inde_lhs (z : ℍ) : (z.1 ^ 2)⁻¹ * G2 (ModularGroup.S • z) - -2 * π * I / z =
    ∑' n : ℤ, ∑' m : ℤ, (G2Term z ![m, n] + δ ![m, n]) := by
  rw [← tsumFilter_tsum_eq z, ← (G2_S_aa z), ← tsum_eq_of_summable_unconditional (L := IcoFilter ℤ),
    ← Summable.tsum_sub]
  · congr
    ext N
    rw [← Summable.tsum_sub]
    · congr
      ext M
      simp only [one_div, G2Term, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, mul_inv_rev]
      have := poly_id z M N
      nth_rw 1 [← this]
      ring
    · simpa using linear_left_summable (ne_zero z) N (k := 2) (by norm_num)
    · simpa [add_assoc] using summable_one_div_linear_sub_one_div_linear z N (N + 1)
  · apply HasSum.summable (a := (z.1 ^ 2)⁻¹ * G2 (ModularGroup.S • z))
    rw [HasSum_IcoFilter_iff]
    have H := G2_S_act z
    apply H.congr
    intro x
    rw [Summable.tsum_finsetSum]
    intro i hi
    simpa using linear_left_summable (ne_zero z) i (k := 2) (by norm_num)
  · apply HasSum.summable (a := -2 * π * I / z)
    rw [HasSum_IcoFilter_iff]
    have H := tendsto_tsum_one_div_linear_sub_succ_eq z
    rw [← tendsto_comp_val_Ioi_atTop]
    apply H
  · have := G_2_alt_summable_δ z
    rw [← swap_equiv.summable_iff, ← (finTwoArrowEquiv _).symm.summable_iff] at this
    simpa using Summable.prod this

lemma G2_alt_indexing_δ (z : ℍ) : ∑' (m : Fin 2 → ℤ), (G2Term z m + δ m)  =
    ∑' m : ℤ, ∑' n : ℤ, (G2Term z ![m, n] + (δ ![m, n])) := by
  rw [ ← (finTwoArrowEquiv _).symm.tsum_eq]
  simp only [Fin.isValue, finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, mul_inv_rev]
  refine Summable.tsum_prod' ?_ ?_
  · have := G_2_alt_summable_δ z
    simp at this
    rw [← (finTwoArrowEquiv _).symm.summable_iff] at this
    exact this
  · intro b
    have := G_2_alt_summable_δ z
    simp only [Fin.isValue, mul_inv_rev, ← (finTwoArrowEquiv _).symm.summable_iff] at this
    exact this.prod_factor b

lemma G2_alt_indexing2_δ (z : ℍ) : ∑' (m : Fin 2 → ℤ), (G2Term z m + δ m)  =
    ∑' n : ℤ, ∑' m : ℤ, (G2Term z ![m, n] + δ ![m, n]) := by
  have := (G_2_alt_summable_δ z)
  simp at this
  rw [← (finTwoArrowEquiv _).symm.summable_iff] at this
  rw [ Summable.tsum_comm', G2_alt_indexing_δ]
  · apply this.congr
    grind [Fin.isValue, finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_inv_rev]
  · intro b
    simp only [mul_inv_rev]
    exact this.prod_factor b
  · intro c
    have H := (G_2_alt_summable_δ z)
    rw [← swap_equiv.summable_iff, ← (finTwoArrowEquiv _).symm.summable_iff] at H
    simpa using H.prod_factor c

lemma G2_transf_aux (z : ℍ) :
    (z.1 ^ 2)⁻¹ * G2 (ModularGroup.S • z) - -2 * π * I / z = G2 z := by
  rw [G2_inde_lhs, G2_alt_eq z , ← G2_alt_indexing2_δ , G2_alt_indexing_δ]

end transform
