/-
Copyright (c) 2023 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Properties of Shannon binary entropy

The [binary entropy function](https://en.wikipedia.org/wiki/Binary_entropy_function)
`h₂ p := - p * log p - (1-p) * log p`
is the Shannon entropy of a Bernoulli random variable with success probability `p`.

This file assumes that entropy is measured in Nats, hence natural logarithms.
Most lemmas are also valid using a different-base logarithm.

## Tags

entropy, Shannon, binary
-/

namespace Entropy

open Real

/-- Shannon Binary entropy function (measured in bits).
It's the Shannon entropy of a Bernoulli random variable with success probability `p`.
Usual domain of definition is p ∈ [0,1], i.e., input is a probability.
`h₂ p := - p * log p - (1-p) * log p` -/
noncomputable def h₂ (p : ℝ) : ℝ := -p * log p - (1 - p) * log (1 - p)

-- Example values

@[simp] lemma h2_zero : h₂ 0 = 0 := by simp [h₂]

@[simp] lemma h2_one : h₂ 1 = 0 := by simp [h₂]

@[simp] lemma h2_onehalf : h₂ 2⁻¹ = log 2 := by
  unfold h₂
  norm_num
  simp only [one_div, log_inv]
  field_simp

-- lemma mul_log2_lt {x y : ℝ} : x < y ↔ x * log 2 < y * log 2 := by field_simp

-- some basic facts about h₂

/-- `h₂` is symmetric about 1/2, i.e.,

`h₂ (1 - p) = h₂ p` -/
@[simp] lemma h2_eq_h2_one_minus (p : ℝ) : h₂ (1 - p) = h₂ p := by simp [h₂]; ring

lemma h2_gt_0 {p : ℝ} (pge0 : 0 < p) (ple1 : p < 1) : 0 < h₂ p := by
  unfold h₂
  simp only [zero_mul, neg_mul]
  have pos_sum_pos_pos (a b : ℝ) (ha : 0 ≤ a) (hb : b < 0) : 0 < a - b := by linarith
  refine pos_sum_pos_pos (-(p * log p)) ((1 - p) * log (1 - p)) ?_ ?_
  · have : -(p * log p) = p * (-log p) := by ring
    rw [this]
    refine LT.lt.le (Real.mul_pos ?_ ?_)
    linarith
    linarith [log_neg pge0 ple1]
  · have fac1 : 0 < 1 - p := by linarith
    have fac2 : log (1 - p) < 0 := log_neg fac1 (by linarith)
    exact Linarith.mul_neg fac2 fac1

/-- TODO assumptions not needed? -/
lemma h2_zero_iff_zero_or_one {p : ℝ} (domup : p ≤ 1) (domun : 0 ≤ p) :
    h₂ p = 0 ↔ p = 0 ∨ p = 1 := by
  constructor <;> intro h
  · by_cases pz : p = 0
    · left; assumption
    · by_cases p_is_one : p = 1
      · right; assumption
      · have : 0 < h₂ p := by
          apply h2_gt_0 (Ne.lt_of_le ?_ domun)
          refine Ne.lt_of_le ?_ ?_
          repeat assumption
          exact Iff.mp ne_comm pz
        simp_all only [lt_self_iff_false]
  · unfold h₂
    cases h <;> simp [*]

lemma zero_lt_log_2 : 0 < log 2 := by
  refine (log_pos_iff zero_lt_two).mpr one_lt_two

/-- For probability p < 0.5,

 h₂ p < 1.
-/
lemma h2_lt_log2_of_gt_half {p : ℝ} (pge0 : 0 ≤ p) (plehalf : p < 1/2) : h₂ p < log 2 := by
  -- Proof by concavity of log.
  unfold h₂
  simp only [neg_mul, one_mul, gt_iff_lt]
  by_cases pz : p = 0
  · simp [*]; exact zero_lt_log_2
  · have invppos : 0 < 1/p := by positivity
    have : 0 < 1 - p := by norm_num; linarith -- used implicitly by tactics. Can eliminate?
    have sub1pinvpos : 0 < 1 / (1 - p) := by positivity
    have logConcave := (strictConcaveOn_log_Ioi.right
      (x := 1/p) (y := 1/(1-p))) (a := p) (b := 1-p)
      invppos sub1pinvpos (by norm_num; linarith) (by positivity)
      (by norm_num; linarith) (by norm_num)
    have : p • (1 / p) + (1 - p) • (1 / (1 - p)) = 2 := by field_simp; norm_num
    rw [this] at logConcave
    have := calc -(p * log p) - (1 - p) * log (1 - p)
          _ = p * (-log p) + (1 - p) * (-log (1 - p)) := by ring
          _ = p * log (1/p) + (1 - p) * log (1 / (1 - p)) := by rw [← log_inv]; norm_num
    rw [this]
    exact logConcave

lemma h2_lt_one_of_gt_log2 {p : ℝ} : 1/2 < p → p ≤ 1 → h₂ p < log 2 := by
  intros
  rw [← h2_eq_h2_one_minus]
  exact h2_lt_log2_of_gt_half (by linarith) (by linarith)

lemma h2_one_iff_eq_half {p : ℝ} (pge0 : 0 ≤ p) (ple1 : p ≤ 1) : h₂ p = log 2 ↔ p = 1/2 := by
  constructor <;> intro h
  · by_cases h' : p < 1/2
    · linarith [h2_lt_log2_of_gt_half pge0 h']
    · by_cases pgthalf : 1/2 < p
      · have := h2_lt_one_of_gt_log2 pgthalf ple1
        linarith
      · linarith
  · simp [h]

lemma h2_le_log_2 {p : ℝ} (pge0 : 0 ≤ p) (ple1 : p ≤ 1) : h₂ p ≤ log 2 := by
  by_cases hh: p = 1/2
  · simp only [one_div, h2_onehalf, le_refl, hh]
  · by_cases gg: h₂ p = log 2
    · simp only [le_refl, gg]
    · by_cases hhh: p < 1/2
      · linarith [h2_lt_log2_of_gt_half pge0 hhh]
      · have : 1/2 < p := by
          refine Ne.lt_of_le ?_ ?_
          aesop
          aesop
        have := h2_lt_one_of_gt_log2 this ple1
        exact LT.lt.le this

/- Binary entropy is continuous everywhere.
This is due to definition of `Real.log` for negative numbers. -/
lemma h₂_continuous : Continuous h₂ := by
  unfold h₂
  apply Continuous.add
  · simp_rw [← neg_mul_eq_neg_mul]
    apply Continuous.neg
    exact continuous_mul_log
  · apply Continuous.neg
    exact Continuous.comp continuous_mul_log (continuous_sub_left 1)

/-! ### Derivatives of binary entropy function -/

/-- Derivative of binary entropy function (shown in `deriv_h₂`) -/
protected noncomputable def h₂deriv (p : ℝ) : ℝ := log (1 - p) - log p

@[simp] lemma deriv_one_minus (x : ℝ) : deriv (fun (y : ℝ) ↦ 1 - y) x = -1 := by
  have onem (y : ℝ) : 1 - y = -(y + -1) := by ring
  simp_rw [onem]
  simp only [neg_add_rev, neg_neg, differentiableAt_const, deriv_const_add', deriv_neg'']

@[simp] lemma differentiable_one_minus (p : ℝ) : DifferentiableAt ℝ (fun p => 1 - p) p := by
  have (p : ℝ) : 1 - p = -(p - 1) := by ring
  simp_rw [this]
  apply differentiableAt_neg_iff.mpr
  apply DifferentiableAt.add_const
  simp only [differentiableAt_id']

-- TODO don't need assumptions
lemma deriv_log_one_sub {x : ℝ} (hh : x ≠ 1): deriv (fun p ↦ log (1 - p)) x = -(1-x)⁻¹ := by
  rw [deriv.log]
  simp only [deriv_one_minus]
  field_simp
  exact differentiable_one_minus x
  exact sub_ne_zero.mpr hh.symm

@[simp] lemma differentiableAt_log_const_neg {x c : ℝ} (h : x ≠ c) :
    DifferentiableAt ℝ (fun p ↦ log (c - p)) x := by
  apply DifferentiableAt.log
  apply DifferentiableAt.sub
  apply differentiableAt_const
  apply differentiableAt_id'
  exact sub_ne_zero.mpr (id (Ne.symm h))

-- TODO don't need assumptions
lemma deriv_h₂' {x : ℝ} (h: x ≠ 0) (hh : x ≠ 1) :
    deriv (fun p => -p * log p - (1 - p) * log (1 - p)) x = log (1 - x) - log x := by
  rw [deriv_sub]
  simp_rw [← neg_mul_eq_neg_mul]
  rw [deriv.neg, deriv_mul_log h]
  simp_rw [mul_sub_right_distrib]
  simp only [one_mul]
  rw [deriv_sub, deriv_log_one_sub hh]
  · rw [deriv_mul, deriv_id'']
    rw [deriv.log]
    simp only [one_mul, deriv_one_minus]
    field_simp
    ring_nf
    calc -1 + (-log x - x * (1 - x)⁻¹) + (1 - x)⁻¹ + log (1 - x)
      _ = -1 + (1 - x) * (1 - x)⁻¹ + log (1 - x) - log x := by ring
      _ = -log x + log (1 - x) := by
        field_simp [sub_ne_zero.mpr hh.symm]
        ring
    apply differentiable_one_minus
    exact sub_ne_zero.mpr hh.symm
    apply differentiableAt_id'
    exact differentiableAt_log_const_neg hh
  · exact differentiableAt_log_const_neg hh
  · apply DifferentiableAt.mul
    apply differentiableAt_id'
    apply DifferentiableAt.log
    exact differentiable_one_minus x
    exact sub_ne_zero.mpr hh.symm
  · apply DifferentiableAt.mul
    apply DifferentiableAt.neg
    exact differentiableAt_id'
    exact differentiableAt_log h
  · apply DifferentiableAt.mul
    apply differentiable_one_minus
    exact differentiableAt_log_const_neg hh

-- TODO don't need assumptions
lemma deriv_h₂ {x : ℝ} (h: x ≠ 0) (hh : x ≠ 1) : deriv h₂ x = log (1 - x) - log x := by
  unfold h₂
  apply deriv_h₂' h hh

/- Binary entropy has derivative `log (1 - p) - log p`. -/
lemma hasDerivAt_h₂ {x : ℝ} (xne0: x ≠ 0) (gne1 : x ≠ 1) :
    HasDerivAt h₂ (Entropy.h₂deriv x) x := by
  have diffAtStuff : DifferentiableAt ℝ (fun p => -p * log p - (1 - p) * log (1 - p)) x := by
    apply DifferentiableAt.sub
    apply DifferentiableAt.mul
    apply DifferentiableAt.neg
    exact differentiableAt_id'
    apply DifferentiableAt.log differentiableAt_id' xne0
    apply DifferentiableAt.mul
    apply DifferentiableAt.sub
    apply differentiableAt_const
    exact differentiableAt_id'
    apply DifferentiableAt.log
    apply DifferentiableAt.sub
    apply differentiableAt_const
    exact differentiableAt_id'
    exact sub_ne_zero.mpr gne1.symm
  convert hasDerivAt_deriv_iff.mpr diffAtStuff using 1
  exact (deriv_h₂' xne0 gne1).symm

open Filter Topology

/- Second derivative.
TODO Assumptions not needed (use junk value after proving that `¬DifferentiableAt` there) ?!-/
lemma deriv2_h₂ {x : ℝ} (h : x ≠ 0) (hh : 1 ≠ x) : deriv^[2] h₂ x = -1 / (x * (1-x)) := by
  simp only [Function.iterate_succ]
  suffices ∀ᶠ y in (𝓝 x), deriv (fun x ↦ h₂ x) y = log (1 - y) - log y by
    refine (Filter.EventuallyEq.deriv_eq this).trans ?_
    rw [deriv_sub]
    · repeat rw [deriv_div_const]
      repeat rw [deriv.log]
      simp only [deriv_one_minus, deriv_id'', one_div]
      · field_simp [sub_ne_zero_of_ne hh]
        ring
      exact differentiableAt_id'
      exact h
      exact differentiable_one_minus x
      exact sub_ne_zero.mpr hh
    · exact differentiableAt_log_const_neg (id (Ne.symm hh))
    · exact differentiableAt_log h
  filter_upwards [eventually_ne_nhds h, eventually_ne_nhds hh.symm] with y h h2 using deriv_h₂ h h2


/-! ### Strict Monotonicity of binary entropy -/

open Set
/- Binary entropy is strictly increasing in interval [0, 1/2]. -/
lemma h2_strictMono : StrictMonoOn h₂ (Set.Icc 0 (1/2)) := by
  intro p1 hp1 p2 hp2 p1le2
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 (1 / 2)) _ _ hp1 hp2 p1le2
  · apply h₂_continuous.continuousOn
  · intro x hx
    simp at hx
    rw [← one_div 2] at hx
    rw [deriv_h₂ (by linarith) (by linarith)]
    · field_simp
      have : 1 - x ∈ Ioi 0 := by
        simp [mem_Ioi, sub_pos, hx.2]
        linarith
      apply Real.strictMonoOn_log hx.1 this
      linarith

/-! ### Strict Concavity of binary entropy -/

lemma log2_ne_0 : log 2 ≠ 0 := by norm_num
lemma log2_gt_0 : 0 < log 2 := by positivity

-- NOTE: NOT USED! TODO
-- lemma log2_lt_1 : log 2 < 1 := by
--   rw [show (1 : ℝ) = 2 - 1 by norm_num]
--   apply Real.log_lt_sub_one_of_pos zero_lt_two (Ne.symm (OfNat.one_ne_ofNat 2))


lemma strictConcave_h2 : StrictConcaveOn ℝ (Icc 0 1) h₂ := by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc 0 1) h₂_continuous.continuousOn
  intro x hx
  rw [deriv2_h₂]
  · simp_all
    apply div_neg_of_neg_of_pos
    norm_num [log2_gt_0]
    simp_all only [gt_iff_lt, mul_pos_iff_of_pos_left, sub_pos, hx, log2_gt_0]
  · simp_all only [interior_Icc, mem_Ioo]
    exact ne_of_gt hx.1
  · simp_all only [interior_Icc, mem_Ioo]
    exact (ne_of_lt (hx.2)).symm
