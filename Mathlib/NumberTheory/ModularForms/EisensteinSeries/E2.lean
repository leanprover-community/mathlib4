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

/-!
# Eisenstein Series E2

We define the Eisenstein series `E2` of weight `2` and level `1` as a limit of partial sums
over non-symmetric intervals.

-/

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace  intervalIntegral
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

/-- The Eisenstein series of weight `2` and level `1` defined as the limit as `N` tends to
infinity of the partial sum of `m` in `[N,N)` of `e2Summand m`. This sum over symmetric
intervals is handy in showing it is Cauchy. -/
def G2 : ℍ → ℂ := fun z => limUnder atTop (fun N : ℕ => ∑ m ∈ Icc (-N : ℤ) N, e2Summand m z)

/-- The normalised Eisenstein series of weight `2` and level `1`. -/
def E2 : ℍ → ℂ := (1 / (2 * riemannZeta 2)) •  G2

/-- This function measures the defect in `E2` being a modular form. -/
def D2 (γ : SL(2, ℤ)) : ℍ → ℂ := fun z => (2 * π * Complex.I * γ 1 0) / (denom γ z)

lemma Icc_succ_succ (n : ℕ) : Finset.Icc (-(n + 1) : ℤ) (n + 1) = Finset.Icc (-n : ℤ) n ∪
  {(-(n + 1) : ℤ), (n + 1 : ℤ)} := by
  refine Finset.ext_iff.mpr ?_
  intro a
  simp only [neg_add_rev, Int.reduceNeg, Finset.mem_Icc, add_neg_le_iff_le_add, Finset.union_insert,
    Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
  omega

lemma sum_Icc_of_even_eq_range {α : Type*} [CommRing α] (f : ℤ → α) (hf : ∀ n, f n = f (-n))
    (N : ℕ) : ∑ m ∈  Finset.Icc (-N : ℤ) N, f m =  2 * ∑ m ∈ Finset.range (N + 1), f m  - f 0 := by
  induction' N with N ih
  · simp [two_mul]
  · have := Icc_succ_succ N
    simp only [neg_add_rev, Int.reduceNeg,  Nat.cast_add, Nat.cast_one] at *
    rw [this, Finset.sum_union (by simp), Finset.sum_pair (by omega), ih]
    nth_rw 2 [Finset.sum_range_succ]
    have HF := hf (N + 1)
    simp only [neg_add_rev, Int.reduceNeg] at HF
    rw [← HF]
    ring_nf
    norm_cast

lemma G2_partial_sum_eq (z : ℍ) (N : ℕ) : (∑ m ∈ Icc (-N : ℤ) N, e2Summand m z) =
    (2 * riemannZeta 2) + (∑ m ∈ Finset.range N, 2 * (-2 * ↑π * Complex.I) ^ 2  *
    ∑' n : ℕ+, n  * cexp (2 * ↑π * Complex.I * (m + 1) * z) ^ (n : ℕ)) := by
  rw [sum_Icc_of_even_eq_range, Finset.sum_range_succ', mul_add]
  · nth_rw 2 [two_mul]
    ring_nf
    have (a : ℕ):= EisensteinSeries.qExpansion_identity_pnat (k := 1) (by omega) ⟨(a + 1) * z, by
      have ha : 0 < a + (1 : ℝ) := by linarith
      simpa [ha] using z.2⟩
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
      apply tsum_congr
      intro b
      ring_nf
  · intro n
    simp only [e2Summand, eisSummand, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Int.reduceNeg, zpow_neg, Int.cast_neg, neg_mul]
    nth_rw 2 [← tsum_int_eq_tsum_neg]
    apply tsum_congr
    intro b
    norm_cast
    ring_nf
    aesop

private lemma aux_tsum_identity (z : ℍ) : ∑' m : ℕ, (2 * (-2 * ↑π * Complex.I) ^ 2  *
    ∑' n : ℕ+, n * cexp (2 * ↑π * Complex.I * (m + 1) * z) ^ (n : ℕ))  =
    -8 * π ^ 2 * ∑' (n : ℕ+), (sigma 1 n) * cexp (2 * π * Complex.I * z) ^ (n : ℕ) := by
  have := tsum_prod_pow_cexp_eq_tsum_sigma 1 z
  rw [tsum_pnat_eq_tsum_succ (fun d =>
    ∑' (c : ℕ+), (c ^ 1 : ℂ) * cexp (2 * ↑π * Complex.I * d * z) ^ (c : ℕ))] at this
  simp only [neg_mul, even_two, Even.neg_pow, ← tsum_mul_left, ← this, Nat.cast_add, Nat.cast_one]
  apply tsum_congr
  intro b
  apply tsum_congr
  intro c
  simp only [mul_pow, I_sq, mul_neg, mul_one, neg_mul, neg_inj]
  ring

theorem G2_tendsto (z : ℍ) : Tendsto (fun N ↦ ∑ x ∈ range N, 2 * (2 * ↑π * Complex.I) ^ 2 *
    ∑' (n : ℕ+), n * cexp (2 * ↑π * Complex.I * (↑x + 1) * ↑z) ^ (n : ℕ)) atTop
    (𝓝 (-8 * ↑π ^ 2 * ∑' (n : ℕ+), ↑((σ 1) ↑n) * cexp (2 * ↑π * Complex.I * ↑z) ^ (n : ℕ))) := by
  rw [← aux_tsum_identity]
  have hf : Summable fun m : ℕ => ( 2 * (-2 * ↑π * Complex.I) ^ 2 *
      ∑' n : ℕ+, n ^ ((2 - 1)) * Complex.exp (2 * ↑π * Complex.I * (m + 1) * z) ^ (n : ℕ)) := by
    apply Summable.mul_left
    have := (summable_prod_aux 1 z).prod_symm.prod
    have h0 := pnat_summable_iff_summable_succ
      (f := fun b ↦ ∑' (c : ℕ+), c * cexp (2 * ↑π * Complex.I * ↑↑b * ↑z) ^ (c : ℕ))
    simp at *
    rw [← h0]
    apply this
  simpa using (hf.hasSum).comp tendsto_finset_range

lemma G2_cauchy (z : ℍ) : CauchySeq (fun N : ℕ => ∑ m ∈ Icc (-N : ℤ) N, e2Summand m z) := by
  conv =>
    enter [1]
    ext n
    rw [G2_partial_sum_eq]
  apply CauchySeq.const_add
  apply Filter.Tendsto.cauchySeq (x :=
    -8 * π ^ 2 * ∑' (n : ℕ+), (σ 1 n) * cexp (2 * π * Complex.I * z) ^ (n : ℕ))
  simpa using G2_tendsto z

lemma G2_q_exp (z : ℍ) : G2 z = (2 * riemannZeta 2)  - 8 * π ^ 2 *
  ∑' n : ℕ+, sigma 1 n * cexp (2 * π * Complex.I * z) ^ (n : ℕ) := by
  rw [G2, Filter.Tendsto.limUnder_eq]
  conv =>
    enter [1]
    ext N
    rw [G2_partial_sum_eq z N]
  rw [sub_eq_add_neg]
  apply Filter.Tendsto.add
  · simp
  · simpa using G2_tendsto z

section transform

lemma rest (f g : ℕ → ℂ) (x : ℂ) (hf : Tendsto f atTop (𝓝 x)) (hfg : Tendsto (g - f) atTop (𝓝 0)) :
  Tendsto g atTop (𝓝 x) := by
  have := Tendsto.add hf hfg
  simp at this
  exact this

lemma sum_Icc_eq_sum_Ico_succ {α : Type*} [AddCommMonoid α] (f : ℤ → α)
    {l u : ℤ} (h : l ≤ u) :
    ∑ m ∈ Finset.Icc l u, f m = (∑ m ∈ Finset.Ico l u, f m) + f u := by
  rw [Finset.Icc_eq_cons_Ico h]
  simp only [Finset.cons_eq_insert, Finset.mem_Ico, lt_self_iff_false, and_false, not_false_eq_true,
    Finset.sum_insert]
  rw [add_comm]

lemma sum_Icc_pred {R : Type*} [AddCommGroup R] (f : ℤ → R) {N : ℕ}
  (hn : 1 ≤ N) : ∑ m ∈ Finset.Icc (-N : ℤ) N, f m =
  f N + f (-N : ℤ)  + ∑ m ∈ Finset.Icc (-(N - 1) : ℤ) (N - 1), f m := by
  induction' N with N ih
  · grind
  · zify
    rw [Icc_succ_succ, Finset.sum_union (by simp)]
    grind

lemma cauchSeq_sum_Icc_tendsto_zero {F : Type*} [NormedRing F] [NormSMulClass ℤ F] (f : ℤ → F)
    (hc : CauchySeq fun N : ℕ => ∑ m ∈ Finset.Icc (-N : ℤ) N, f m) (hs : ∀ n , f n = f (-n)) :
    Tendsto f atTop (𝓝 0) := by
  have h := cauchySeq_iff_tendsto_dist_atTop_0.mp hc
  simp_rw [cauchySeq_iff_le_tendsto_0] at *
  obtain ⟨g, hg, H, Hg⟩ := hc
  simp [Metric.tendsto_atTop] at *
  intro ε hε
  obtain ⟨N, hN⟩ := (Hg (2 * ε) (by linarith))
  use N + 1
  intro n hn
  have H3 := H (n).natAbs (n -1).natAbs N (by omega) (by omega)
  rw [sum_Icc_pred f (by omega)] at H3
  have h1 : |n| = n := by
    simp only [abs_eq_self]
    omega
  have h2 : |n - 1| = n - 1 := by
    simp only [abs_eq_self, Int.sub_nonneg]
    omega
  simp [Nat.cast_natAbs, h1, Int.cast_eq, ← hs n, (two_mul (f n)).symm, neg_sub,
    h2, Int.cast_sub, Int.cast_one, dist_add_self_left] at H3
  have hgnn :  ‖2 * f n‖ < 2 * ε := lt_of_le_of_lt (le_trans H3 (le_abs_self (g N))) (hN N (by rfl))
  have := norm_smul (2 : ℤ) (f n)
  simp only [zsmul_eq_mul, Int.cast_ofNat] at this
  simpa [this, Int.norm_eq_abs] using hgnn


lemma int_tendsto_nat {f : ℤ → ℂ} {x : ℂ} (hf : Tendsto f atTop (𝓝 x)) :
  Tendsto (fun n : ℕ => f n) atTop (𝓝 x) := by
  rw [Metric.tendsto_atTop] at *
  intro ε hε
  obtain ⟨N, hN⟩ := hf ε hε
  use N.natAbs
  intro n hn
  apply hN n ?_
  omega

lemma G2_Ico (z : ℍ) : G2 z =
    limUnder (atTop) (fun N : ℕ => ∑ m ∈ Finset.Ico (-N : ℤ) N, e2Summand m z) := by
  apply symm
  simp [G2]
  rw [Filter.Tendsto.limUnder_eq]
  have := CauchySeq.tendsto_limUnder (G2_cauchy z)
  apply rest _ _ _ this
  have h0 := cauchSeq_sum_Icc_tendsto_zero _  (G2_cauchy z) ?_
  conv =>
    enter [1]
    ext N
    simp
    rw [sum_Icc_eq_sum_Ico_succ _ (by omega)]
    simp
  have := Filter.Tendsto.neg h0
  simp only [one_div, neg_zero] at this
  have := int_tendsto_nat this
  apply this
  · intro m
    simp [e2Summand]
    rw [← tsum_int_eq_tsum_neg (fun a => eisSummand 2 ![-m, a] z)]
    congr
    ext b
    simp [eisSummand]
    norm_cast
    simp only [Int.cast_neg]
    ring


end transform
