/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sébastien Gouëzel, Rémy Degenne
-/
module

public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Mean value inequalities

In this file we prove several mean inequalities for finite sums. Versions for integrals of some of
these inequalities are available in `MeasureTheory.MeanInequalities`.

## Main theorems: generalized mean inequality

The inequality says that for two non-negative vectors $w$ and $z$ with $\sum_{i\in s} w_i=1$
and $p ≤ q$ we have
$$
\sqrt[p]{\sum_{i\in s} w_i z_i^p} ≤ \sqrt[q]{\sum_{i\in s} w_i z_i^q}.
$$

Currently we only prove this inequality for $p=1$. As in the rest of `Mathlib`, we provide
different theorems for natural exponents (`pow_arith_mean_le_arith_mean_pow`), integer exponents
(`zpow_arith_mean_le_arith_mean_zpow`), and real exponents (`rpow_arith_mean_le_arith_mean_rpow` and
`arith_mean_le_rpow_mean`). In the first two cases we prove
$$
\left(\sum_{i\in s} w_i z_i\right)^n ≤ \sum_{i\in s} w_i z_i^n
$$
in order to avoid using real exponents. For real exponents we prove both this and standard versions.

## TODO

- each inequality `A ≤ B` should come with a theorem `A = B ↔ _`; one of the ways to prove them
  is to define `StrictConvexOn` functions.
- generalized mean inequality with any `p ≤ q`, including negative numbers;
- prove that the power mean tends to the geometric mean as the exponent tends to zero.

-/

public section


universe u v

open Finset NNReal ENNReal

noncomputable section

variable {ι : Type u} (s : Finset ι)

namespace Real

theorem pow_arith_mean_le_arith_mean_pow (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) (n : ℕ) :
    (∑ i ∈ s, w i * z i) ^ n ≤ ∑ i ∈ s, w i * z i ^ n :=
  (convexOn_pow n).map_sum_le hw hw' hz

theorem pow_arith_mean_le_arith_mean_pow_of_even (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1) {n : ℕ} (hn : Even n) :
    (∑ i ∈ s, w i * z i) ^ n ≤ ∑ i ∈ s, w i * z i ^ n :=
  hn.convexOn_pow.map_sum_le hw hw' fun _ _ => Set.mem_univ _

theorem zpow_arith_mean_le_arith_mean_zpow (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 < z i) (m : ℤ) :
    (∑ i ∈ s, w i * z i) ^ m ≤ ∑ i ∈ s, w i * z i ^ m :=
  (convexOn_zpow m).map_sum_le hw hw' hz

theorem rpow_arith_mean_le_arith_mean_rpow (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) {p : ℝ} (hp : 1 ≤ p) :
    (∑ i ∈ s, w i * z i) ^ p ≤ ∑ i ∈ s, w i * z i ^ p :=
  (convexOn_rpow hp).map_sum_le hw hw' hz

theorem arith_mean_le_rpow_mean (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 ≤ z i) {p : ℝ} (hp : 1 ≤ p) :
    ∑ i ∈ s, w i * z i ≤ (∑ i ∈ s, w i * z i ^ p) ^ (1 / p) := by
  have : 0 < p := by positivity
  rw [← rpow_le_rpow_iff _ _ this, ← rpow_mul, one_div_mul_cancel (ne_of_gt this), rpow_one]
  · exact rpow_arith_mean_le_arith_mean_rpow s w z hw hw' hz hp
  all_goals
    apply_rules [sum_nonneg, rpow_nonneg]
    intro i hi
    positivity [hw i hi, hz i hi]

end Real

namespace NNReal

/-- Weighted generalized mean inequality, version sums over finite sets, with `ℝ≥0`-valued
functions and natural exponent. -/
theorem pow_arith_mean_le_arith_mean_pow (w z : ι → ℝ≥0) (hw' : ∑ i ∈ s, w i = 1) (n : ℕ) :
    (∑ i ∈ s, w i * z i) ^ n ≤ ∑ i ∈ s, w i * z i ^ n :=
  mod_cast
    Real.pow_arith_mean_le_arith_mean_pow s _ _ (fun i _ => (w i).coe_nonneg)
      (mod_cast hw') (fun i _ => (z i).coe_nonneg) n

/-- Weighted generalized mean inequality, version for sums over finite sets, with `ℝ≥0`-valued
functions and real exponents. -/
theorem rpow_arith_mean_le_arith_mean_rpow (w z : ι → ℝ≥0) (hw' : ∑ i ∈ s, w i = 1) {p : ℝ}
    (hp : 1 ≤ p) : (∑ i ∈ s, w i * z i) ^ p ≤ ∑ i ∈ s, w i * z i ^ p :=
  mod_cast
    Real.rpow_arith_mean_le_arith_mean_rpow s _ _ (fun i _ => (w i).coe_nonneg)
      (mod_cast hw') (fun i _ => (z i).coe_nonneg) hp

/-- Weighted generalized mean inequality, version for two elements of `ℝ≥0` and real exponents. -/
theorem rpow_arith_mean_le_arith_mean2_rpow (w₁ w₂ z₁ z₂ : ℝ≥0) (hw' : w₁ + w₂ = 1) {p : ℝ}
    (hp : 1 ≤ p) : (w₁ * z₁ + w₂ * z₂) ^ p ≤ w₁ * z₁ ^ p + w₂ * z₂ ^ p := by
  have h := rpow_arith_mean_le_arith_mean_rpow univ ![w₁, w₂] ![z₁, z₂] ?_ hp
  · simpa [Fin.sum_univ_succ] using h
  · simp [hw', Fin.sum_univ_succ]

/-- Unweighted mean inequality, version for two elements of `ℝ≥0` and real exponents. -/
theorem rpow_add_le_mul_rpow_add_rpow (z₁ z₂ : ℝ≥0) {p : ℝ} (hp : 1 ≤ p) :
    (z₁ + z₂) ^ p ≤ (2 : ℝ≥0) ^ (p - 1) * (z₁ ^ p + z₂ ^ p) := by
  rcases eq_or_lt_of_le hp with (rfl | h'p)
  · simp only [rpow_one, sub_self, rpow_zero, one_mul]; rfl
  convert rpow_arith_mean_le_arith_mean2_rpow (1 / 2) (1 / 2) (2 * z₁) (2 * z₂) (add_halves 1) hp
    using 1
  · simp only [one_div, inv_mul_cancel_left₀, Ne, two_ne_zero,
      not_false_iff]
  · have A : p - 1 ≠ 0 := ne_of_gt (sub_pos.2 h'p)
    simp only [mul_rpow, rpow_sub' A, rpow_one]
    ring

/-- Weighted generalized mean inequality, version for sums over finite sets, with `ℝ≥0`-valued
functions and real exponents. -/
theorem arith_mean_le_rpow_mean (w z : ι → ℝ≥0) (hw' : ∑ i ∈ s, w i = 1) {p : ℝ} (hp : 1 ≤ p) :
    ∑ i ∈ s, w i * z i ≤ (∑ i ∈ s, w i * z i ^ p) ^ (1 / p) :=
  mod_cast
    Real.arith_mean_le_rpow_mean s _ _ (fun i _ => (w i).coe_nonneg) (mod_cast hw')
      (fun i _ => (z i).coe_nonneg) hp

private theorem add_rpow_le_one_of_add_le_one {p : ℝ} (a b : ℝ≥0) (hab : a + b ≤ 1) (hp1 : 1 ≤ p) :
    a ^ p + b ^ p ≤ 1 := by
  have h_le_one : ∀ x : ℝ≥0, x ≤ 1 → x ^ p ≤ x := fun x hx => rpow_le_self_of_le_one hx hp1
  have ha : a ≤ 1 := (self_le_add_right a b).trans hab
  have hb : b ≤ 1 := (self_le_add_left b a).trans hab
  exact (add_le_add (h_le_one a ha) (h_le_one b hb)).trans hab

theorem add_rpow_le_rpow_add {p : ℝ} (a b : ℝ≥0) (hp1 : 1 ≤ p) : a ^ p + b ^ p ≤ (a + b) ^ p := by
  have hp_pos : 0 < p := by positivity
  by_cases h_zero : a + b = 0
  · simp [add_eq_zero.mp h_zero, hp_pos.ne']
  have h_nonzero : ¬(a = 0 ∧ b = 0) := by rwa [add_eq_zero] at h_zero
  have h_add : a / (a + b) + b / (a + b) = 1 := by rw [← add_div, div_self h_zero]
  have h := add_rpow_le_one_of_add_le_one (a / (a + b)) (b / (a + b)) h_add.le hp1
  rw [div_rpow a (a + b), div_rpow b (a + b)] at h
  have hab_0 : (a + b) ^ p ≠ 0 := by simp [h_nonzero]
  have h_mul : (a + b) ^ p * (a ^ p / (a + b) ^ p + b ^ p / (a + b) ^ p) ≤ (a + b) ^ p := by
    nth_rw 4 [← mul_one ((a + b) ^ p)]; gcongr
  rwa [div_eq_mul_inv, div_eq_mul_inv, mul_add, mul_comm (a ^ p), mul_comm (b ^ p), ← mul_assoc, ←
    mul_assoc, mul_inv_cancel₀ hab_0, one_mul, one_mul] at h_mul

theorem rpow_add_rpow_le_add {p : ℝ} (a b : ℝ≥0) (hp1 : 1 ≤ p) :
    (a ^ p + b ^ p) ^ (1 / p) ≤ a + b := by
  rw [one_div]
  rw [← @NNReal.le_rpow_inv_iff _ _ p⁻¹ (by simp [lt_of_lt_of_le zero_lt_one hp1])]
  rw [inv_inv]
  exact add_rpow_le_rpow_add _ _ hp1

theorem rpow_add_rpow_le {p q : ℝ} (a b : ℝ≥0) (hp_pos : 0 < p) (hpq : p ≤ q) :
    (a ^ q + b ^ q) ^ (1 / q) ≤ (a ^ p + b ^ p) ^ (1 / p) := by
  have h_rpow : ∀ a : ℝ≥0, a ^ q = (a ^ p) ^ (q / p) := fun a => by
    rw [← NNReal.rpow_mul, div_eq_inv_mul, ← mul_assoc, mul_inv_cancel₀ hp_pos.ne.symm,
      one_mul]
  have h_rpow_add_rpow_le_add :
    ((a ^ p) ^ (q / p) + (b ^ p) ^ (q / p)) ^ (1 / (q / p)) ≤ a ^ p + b ^ p := by
    refine rpow_add_rpow_le_add (a ^ p) (b ^ p) ?_
    rwa [one_le_div hp_pos]
  rw [h_rpow a, h_rpow b, one_div p, NNReal.le_rpow_inv_iff hp_pos, ← NNReal.rpow_mul, mul_comm,
    mul_one_div]
  rwa [one_div_div] at h_rpow_add_rpow_le_add

theorem rpow_add_le_add_rpow {p : ℝ} (a b : ℝ≥0) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (a + b) ^ p ≤ a ^ p + b ^ p := by
  rcases hp.eq_or_lt with (rfl | hp_pos)
  · simp
  have h := rpow_add_rpow_le a b hp_pos hp1
  rw [one_div_one, one_div] at h
  repeat' rw [NNReal.rpow_one] at h
  exact (NNReal.le_rpow_inv_iff hp_pos).mp h

end NNReal

namespace Real

lemma add_rpow_le_rpow_add {p : ℝ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp1 : 1 ≤ p) :
     a ^ p + b ^ p ≤ (a + b) ^ p := by
  lift a to NNReal using ha
  lift b to NNReal using hb
  exact_mod_cast NNReal.add_rpow_le_rpow_add a b hp1

lemma rpow_add_rpow_le_add {p : ℝ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp1 : 1 ≤ p) :
    (a ^ p + b ^ p) ^ (1 / p) ≤ a + b := by
  lift a to NNReal using ha
  lift b to NNReal using hb
  exact_mod_cast NNReal.rpow_add_rpow_le_add a b hp1

lemma rpow_add_rpow_le {p q : ℝ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp_pos : 0 < p)
    (hpq : p ≤ q) :
    (a ^ q + b ^ q) ^ (1 / q) ≤ (a ^ p + b ^ p) ^ (1 / p) := by
  lift a to NNReal using ha
  lift b to NNReal using hb
  exact_mod_cast NNReal.rpow_add_rpow_le a b hp_pos hpq

lemma rpow_add_le_add_rpow {p : ℝ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 0 ≤ p)
    (hp1 : p ≤ 1) :
    (a + b) ^ p ≤ a ^ p + b ^ p := by
  lift a to NNReal using ha
  lift b to NNReal using hb
  exact_mod_cast NNReal.rpow_add_le_add_rpow a b hp hp1

end Real

namespace ENNReal

/-- Weighted generalized mean inequality, version for sums over finite sets, with `ℝ≥0∞`-valued
functions and real exponents. -/
theorem rpow_arith_mean_le_arith_mean_rpow (w z : ι → ℝ≥0∞) (hw' : ∑ i ∈ s, w i = 1) {p : ℝ}
    (hp : 1 ≤ p) : (∑ i ∈ s, w i * z i) ^ p ≤ ∑ i ∈ s, w i * z i ^ p := by
  have hp_pos : 0 < p := by positivity
  have hp_nonneg : 0 ≤ p := by positivity
  have hp_not_neg : ¬p < 0 := by simp [hp_nonneg]
  have h_top_iff_rpow_top : ∀ (i : ι), i ∈ s → (w i * z i = ⊤ ↔ w i * z i ^ p = ⊤) := by
    simp [ENNReal.mul_eq_top, hp_pos, hp_not_neg]
  refine le_of_top_imp_top_of_toNNReal_le ?_ ?_
  · -- first, prove `(∑ i ∈ s, w i * z i) ^ p = ⊤ → ∑ i ∈ s, (w i * z i ^ p) = ⊤`
    rw [rpow_eq_top_iff, sum_eq_top, sum_eq_top]
    grind
  · -- second, suppose both `(∑ i ∈ s, w i * z i) ^ p ≠ ⊤` and `∑ i ∈ s, (w i * z i ^ p) ≠ ⊤`,
    -- and prove `((∑ i ∈ s, w i * z i) ^ p).toNNReal ≤ (∑ i ∈ s, (w i * z i ^ p)).toNNReal`,
    -- by using `NNReal.rpow_arith_mean_le_arith_mean_rpow`.
    intro h_top_rpow_sum _
    -- show hypotheses needed to put the `.toNNReal` inside the sums.
    have h_top : ∀ a : ι, a ∈ s → w a * z a ≠ ⊤ :=
      haveI h_top_sum : ∑ i ∈ s, w i * z i ≠ ⊤ := by
        intro h
        rw [h, top_rpow_of_pos hp_pos] at h_top_rpow_sum
        exact h_top_rpow_sum rfl
      fun a ha => (lt_top_of_sum_ne_top h_top_sum ha).ne
    have h_top_rpow : ∀ a : ι, a ∈ s → w a * z a ^ p ≠ ⊤ := by
      intro i hi
      specialize h_top i hi
      rwa [Ne, ← h_top_iff_rpow_top i hi]
    -- put the `.toNNReal` inside the sums.
    simp_rw [toNNReal_sum h_top_rpow, toNNReal_rpow, toNNReal_sum h_top, toNNReal_mul,
      toNNReal_rpow]
    -- use corresponding nnreal result
    refine
      NNReal.rpow_arith_mean_le_arith_mean_rpow s (fun i => (w i).toNNReal)
        (fun i => (z i).toNNReal) ?_ hp
    -- verify the hypothesis `∑ i ∈ s, (w i).toNNReal = 1`, using `∑ i ∈ s, w i = 1` .
    have h_sum_nnreal : ∑ i ∈ s, w i = ↑(∑ i ∈ s, (w i).toNNReal) := by
      rw [coe_finset_sum]
      refine sum_congr rfl fun i hi => (coe_toNNReal ?_).symm
      refine (lt_top_of_sum_ne_top ?_ hi).ne
      exact hw'.symm ▸ ENNReal.one_ne_top
    rwa [← coe_inj, ← h_sum_nnreal]

/-- Weighted generalized mean inequality, version for two elements of `ℝ≥0∞` and real
exponents. -/
theorem rpow_arith_mean_le_arith_mean2_rpow (w₁ w₂ z₁ z₂ : ℝ≥0∞) (hw' : w₁ + w₂ = 1) {p : ℝ}
    (hp : 1 ≤ p) : (w₁ * z₁ + w₂ * z₂) ^ p ≤ w₁ * z₁ ^ p + w₂ * z₂ ^ p := by
  have h := rpow_arith_mean_le_arith_mean_rpow univ ![w₁, w₂] ![z₁, z₂] ?_ hp
  · simpa [Fin.sum_univ_succ] using h
  · simp [hw', Fin.sum_univ_succ]

/-- Unweighted mean inequality, version for two elements of `ℝ≥0∞` and real exponents. -/
theorem rpow_add_le_mul_rpow_add_rpow (z₁ z₂ : ℝ≥0∞) {p : ℝ} (hp : 1 ≤ p) :
    (z₁ + z₂) ^ p ≤ (2 : ℝ≥0∞) ^ (p - 1) * (z₁ ^ p + z₂ ^ p) := by
  convert rpow_arith_mean_le_arith_mean2_rpow (1 / 2) (1 / 2) (2 * z₁) (2 * z₂)
      (ENNReal.add_halves 1) hp using 1
  · simp [← mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ofNat_ne_top]
  · simp only [mul_rpow_of_nonneg _ _ (zero_le_one.trans hp), rpow_sub _ _ two_ne_zero ofNat_ne_top,
      ENNReal.div_eq_inv_mul, rpow_one, mul_one]
    ring

theorem add_rpow_le_rpow_add {p : ℝ} (a b : ℝ≥0∞) (hp1 : 1 ≤ p) : a ^ p + b ^ p ≤ (a + b) ^ p := by
  have hp_pos : 0 < p := by positivity
  by_cases h_top : a + b = ⊤
  · rw [← @ENNReal.rpow_eq_top_iff_of_pos (a + b) p hp_pos] at h_top
    rw [h_top]
    exact le_top
  obtain ⟨ha_top, hb_top⟩ := add_ne_top.mp h_top
  lift a to ℝ≥0 using ha_top
  lift b to ℝ≥0 using hb_top
  simpa [ENNReal.coe_rpow_of_nonneg _ hp_pos.le] using
    ENNReal.coe_le_coe.2 (NNReal.add_rpow_le_rpow_add a b hp1)

theorem rpow_add_rpow_le_add {p : ℝ} (a b : ℝ≥0∞) (hp1 : 1 ≤ p) :
    (a ^ p + b ^ p) ^ (1 / p) ≤ a + b := by
  rw [one_div, ← @ENNReal.le_rpow_inv_iff _ _ p⁻¹ (by simp [lt_of_lt_of_le zero_lt_one hp1])]
  rw [inv_inv]
  exact add_rpow_le_rpow_add _ _ hp1

theorem rpow_add_rpow_le {p q : ℝ} (a b : ℝ≥0∞) (hp_pos : 0 < p) (hpq : p ≤ q) :
    (a ^ q + b ^ q) ^ (1 / q) ≤ (a ^ p + b ^ p) ^ (1 / p) := by
  have h_rpow : ∀ a : ℝ≥0∞, a ^ q = (a ^ p) ^ (q / p) := fun a => by
    rw [← ENNReal.rpow_mul, mul_div_cancel₀ _ hp_pos.ne']
  have h_rpow_add_rpow_le_add :
    ((a ^ p) ^ (q / p) + (b ^ p) ^ (q / p)) ^ (1 / (q / p)) ≤ a ^ p + b ^ p := by
    refine rpow_add_rpow_le_add (a ^ p) (b ^ p) ?_
    rwa [one_le_div hp_pos]
  rw [h_rpow a, h_rpow b, one_div p, ENNReal.le_rpow_inv_iff hp_pos, ← ENNReal.rpow_mul, mul_comm,
    mul_one_div]
  rwa [one_div_div] at h_rpow_add_rpow_le_add

theorem rpow_add_le_add_rpow {p : ℝ} (a b : ℝ≥0∞) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (a + b) ^ p ≤ a ^ p + b ^ p := by
  rcases hp.eq_or_lt with (rfl | hp_pos)
  · simp
  have h := rpow_add_rpow_le a b hp_pos hp1
  rw [one_div_one, one_div] at h
  repeat' rw [ENNReal.rpow_one] at h
  exact (ENNReal.le_rpow_inv_iff hp_pos).mp h

end ENNReal
