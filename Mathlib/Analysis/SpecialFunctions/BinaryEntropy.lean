/-
Copyright (c) 2023 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Properties of Shannon binary entropy

The [binary entropy function](https://en.wikipedia.org/wiki/Binary_entropy_function)
`h₂ p := - p * log₂ p - (1-p) * log₂ p`
is the Shannon entropy of a Bernoulli random variable with success probability `p`.

This file assumes that entropy is measured in bits, hence logarithms base 2.
Most lemmas are also valid using any other logarithm

## Tags

entropy, Shannon, binary
-/

namespace Entropy

open Real

noncomputable abbrev log₂ (p : ℝ) : ℝ := Real.logb 2 p

/-- Shannon Binary entropy measured in bits
 Usual domain of definition is p ∈ [0,1], i.e., expects a probability as input. -/
noncomputable def h₂ (p : ℝ) : ℝ := -p * log₂ p - (1 - p) * log₂ (1 - p)

-- Example values

@[simp] lemma h2_zero : h₂ 0 = 0 := by simp [h₂]

@[simp] lemma h2_one : h₂ 1 = 0 := by simp [h₂]

@[simp] lemma h2_onehalf : h₂ (1 / 2) = 1 := by
  simp [h₂, log₂, logb]
  norm_num
  simp
  field_simp

@[simp] lemma h2_onehalf' : h₂ 2⁻¹ = 1 := by
  simp [h₂, log₂, logb]
  norm_num
  simp
  field_simp

lemma mul_log2_lt {x y : ℝ} :  x < y ↔ x * log 2 < y * log 2 := by field_simp

-- some basic facts about h₂

/-- `h₂` is symmetric about 1/2, i.e.,

`h₂ (1 - p) = h₂ p` -/
@[simp] lemma h2_p_eq_h2_1_minus_p (p : ℝ) : h₂ (1 - p) = h₂ p := by simp [h₂]; ring

lemma h2_gt_0 {p : ℝ} (pge0 : 0 < p) (ple1 : p < 1) : 0 < h₂ p := by
  rw [h₂, log₂, log₂, logb, logb, mul_log2_lt]
  simp
  have : (-(p * (log p / log 2)) - (1 - p) * (log (1 - p) / log 2)) * log 2
       = -p * log p - (1 - p) * log (1 - p) := by calc
       _ = (-(p * (log p / log 2)) * log 2 - (1 - p) * (log (1 - p) / log 2) * log 2) := by ring
       _ = -p * log p - (1 - p) * log (1 - p) := by simp; field_simp
  rw [this]
  have pos_sum_pos_pos (a b : ℝ) (ha : 0 ≤ a) (hb : b < 0) : 0 < a - b := by linarith
  refine pos_sum_pos_pos (-p * log p) ((1 - p) * log (1 - p)) ?_ ?_
  · have : -p * log p = p * (-log p) := by ring
    rw [this]
    refine LT.lt.le (Real.mul_pos ?_ ?_)
    linarith
    have := log_neg pge0 ple1
    linarith
  · have fac1 : 0 < 1 - p := by linarith
    have fac2 : log (1 - p) < 0 := log_neg fac1 (by linarith)
    exact Linarith.mul_neg fac2 fac1

/-- TODO assumptions not needed? -/
lemma h2_zero_iff_p_zero_or_1 {p : ℝ} (domup : p ≤ 1) (domun : 0 ≤ p) :
    0 = h₂ p ↔ p = 0 ∨ p = 1 := by
  constructor <;> intro h
  · by_cases pz : p = 0
    · left; assumption
    · by_cases p_is_1 : p = 1
      · right; assumption
      · have : 0 < h₂ p := by
          apply h2_gt_0 (Ne.lt_of_le ?_ domun)
          refine Ne.lt_of_le ?_ ?_
          repeat assumption
          exact Iff.mp ne_comm pz
        simp_all only [lt_self_iff_false]
  · simp [h₂, log₂, logb]
    cases h <;> simp [*]

/-- For probability p < 0.5,

 h₂ p < 1.
-/
lemma h2_lt_1_of_p_lt_half {p : ℝ} (pge0 : 0 ≤ p) (plehalf : p < 1/2) : h₂ p < 1 := by
  -- Proof by concavity of log.
  simp only [h₂, logb]
  have (x y : ℝ) :  x < y ↔ x * log 2 < y * log 2 := by field_simp
  rw [this]
  have : (-p * (log p / log 2) - (1 - p) * (log (1 - p) / log 2)) * log 2
          = -p * log p - (1 - p) * log (1 - p) := by calc
    _ = (-(p * (log p / log 2)) * log 2 - (1 - p) * (log (1 - p) / log 2) * log 2) := by ring
    _ = -p * log p - (1 - p) * log (1 - p) := by simp; field_simp
  rw [this]
  simp
  by_cases pz : p = 0
  · simp [*]; norm_num
  · have invppos : 0 < 1/p := by positivity
    have : 0 < 1 - p := by norm_num; linarith -- used implicitly by tactics. Can eliminate?
    have sub1pinvpos : 0 < 1 / (1 - p) := by positivity
    have logConcave := (strictConcaveOn_log_Ioi.right
      (x := 1/p) (y := 1/(1-p))) (a := p) (b := 1-p)
      invppos sub1pinvpos (by norm_num; linarith) (by positivity)
      (by norm_num; linarith) (by norm_num)
    have : p • (1 / p) + (1 - p) • (1 / (1 - p)) = 2 := by field_simp; norm_num
    rw [this] at logConcave
    have : -(p * log p) - (1 - p) * log (1 - p)
      = p * log (1/p) + (1 - p) * log (1 / (1 - p)) := by calc
          _ = p * (-log p) + (1 - p) * (-log (1 - p)) := by ring
          _ = p * log (1/p) + (1 - p) * log (1 / (1 - p)) := by rw [←log_inv]; norm_num
    rw [this]
    apply logConcave

lemma h2_lt_one_of_p_gt_half {p : ℝ} : 0 ≤ p → 1/2 < p → p ≤ 1 → h₂ p < 1 := by
  intros
  rw [←h2_p_eq_h2_1_minus_p]
  have : 1 - p < 1/2 := by linarith
  refine h2_lt_1_of_p_lt_half ?_ this
  linarith

lemma h2_one_iff_p_is_half {p : ℝ} (pge0 : 0 ≤ p) (ple1 : p ≤ 1) : h₂ p = 1 ↔ p = 1/2
:= by
  constructor <;> intro h
  · by_cases h' : p < 1/2
    · linarith [h2_lt_1_of_p_lt_half pge0 h']
    · by_cases pgthalf : 1/2 < p
      · have := h2_lt_one_of_p_gt_half pge0 pgthalf ple1
        linarith
      · linarith
  · simp [h]

lemma h2_le_1 {p : ℝ} (pge0 : 0 ≤ p) (ple1 : p ≤ 1) : h₂ p ≤ 1
:= by
  by_cases hh: p = 1/2
  · simp [*];
  · by_cases h₂ p = 1
    · simp [*]
    · by_cases hhh: p < 1/2
      · linarith [h2_lt_1_of_p_lt_half pge0 hhh]
      · have : 1/2 < p := by
          refine Ne.lt_of_le ?_ ?_
          aesop
          aesop
        have := h2_lt_one_of_p_gt_half pge0 this ple1
        exact LT.lt.le this

---------------------------------------------------------------------------------- derivatives

/-- Derivative of binary entropy function -/
protected noncomputable def h₂deriv (p : ℝ) : ℝ := log₂ (1 - p) - log₂ p

@[simp] lemma deriv_one_minus (x : ℝ) : deriv (fun (y : ℝ) ↦ 1 - y) x = -1 := by
  have onem (y : ℝ) : 1 - y = -(y + -1) := by ring
  simp_rw [onem]
  simp

@[simp] lemma differentiable_1_minusp (p : ℝ) : DifferentiableAt ℝ (fun p => 1 - p) p := by
  have (p : ℝ) : 1 - p = -(p - 1) := by ring
  simp_rw [this]
  apply differentiableAt_neg_iff.mpr
  apply DifferentiableAt.add_const
  simp

lemma deriv_log_one_sub {x : ℝ} (hh : x ≠ 1): deriv (fun p ↦ log (1 - p)) x = -(1-x)⁻¹ := by
  rw [deriv.log]
  simp
  field_simp
  exact differentiable_1_minusp x
  exact sub_ne_zero.mpr (id (Ne.symm hh))

@[simp] lemma differentiableAt_log_const_neg {x c : ℝ} (h : x ≠ c) :
    DifferentiableAt ℝ (fun p ↦ log (c - p)) x := by
  apply DifferentiableAt.log
  apply DifferentiableAt.sub
  simp
  simp
  exact sub_ne_zero.mpr (id (Ne.symm h))

lemma deriv_h₂' {x : ℝ} (h: x ≠ 0) (hh : x ≠ 1) :
    deriv (fun p => -p * log₂ p - (1 - p) * log₂ (1 - p)) x = log₂ (1 - x) - log₂ x := by
  simp [log₂, logb]
  rw [deriv_sub, deriv.neg]
  simp_rw [mul_div]
  rw [deriv_div_const, deriv_mul_log h, deriv_div_const]
  simp_rw [mul_sub_right_distrib]
  simp
  rw [deriv_sub, deriv_log_one_sub hh]
  · rw [deriv_mul, deriv_id'']
    rw [deriv.log]
    simp
    field_simp
    ring_nf
    calc -1 + (-log x - x * (1 - x)⁻¹) + (1 - x)⁻¹ + log (1 - x)
      _ = -1 + (1 - x) * (1 - x)⁻¹ + log (1 - x) - log x := by ring
      _ = -log x + log (1 - x) := by
        field_simp [sub_ne_zero.mpr hh.symm]
        ring
    simp
    exact sub_ne_zero.mpr hh.symm
    simp
    exact differentiableAt_log_const_neg hh
  · exact differentiableAt_log_const_neg hh
  · apply DifferentiableAt.mul
    simp
    apply DifferentiableAt.log
    exact differentiable_1_minusp x
    exact sub_ne_zero.mpr hh.symm
  · apply DifferentiableAt.neg
    apply DifferentiableAt.mul
    simp
    apply DifferentiableAt.div_const
    exact differentiableAt_log h
  · apply DifferentiableAt.mul
    simp
    apply DifferentiableAt.div_const
    exact differentiableAt_log_const_neg hh

lemma deriv_h₂ {x : ℝ} (h: x ≠ 0) (hh : x ≠ 1) : deriv h₂ x = log₂ (1 - x) - log₂ x := by
  have : h₂ = fun x ↦ h₂ x := by ext; rfl
  rw [this]
  simp_rw [h₂]
  apply deriv_h₂' h hh

/- Binary entropy has derivative `log₂ (1 - p) - log₂ p`. -/
lemma hasDerivAt_h₂ {x : ℝ} (xne0: x ≠ 0) (gne1 : x ≠ 1) :
    HasDerivAt h₂ (Entropy.h₂deriv x) x := by
  have : h₂ = fun x ↦ h₂ x := by ext; rfl
  rw [this]
  have : Entropy.h₂deriv = fun x ↦ Entropy.h₂deriv x := by ext; rfl
  rw [this]
  simp_rw [h₂, Entropy.h₂deriv]
  have diffAtStuff : DifferentiableAt ℝ (fun p => -p * log₂ p - (1 - p) * log₂ (1 - p)) x := by
    simp [log₂, logb]
    apply DifferentiableAt.sub
    apply DifferentiableAt.neg
    apply DifferentiableAt.mul
    exact differentiableAt_id'
    apply DifferentiableAt.div_const
    apply DifferentiableAt.log _ xne0
    exact differentiableAt_id'
    apply DifferentiableAt.mul
    apply DifferentiableAt.sub
    simp
    exact differentiableAt_id'
    apply DifferentiableAt.div_const
    apply DifferentiableAt.log
    apply DifferentiableAt.sub
    simp
    exact differentiableAt_id'
    exact sub_ne_zero.mpr gne1.symm
  convert hasDerivAt_deriv_iff.mpr diffAtStuff using 1
  exact (deriv_h₂' xne0 gne1).symm

lemma cancel_log2 (x : ℝ) : log x / log 2 * log 2 = log x := by field_simp

open Set

/- Binary entropy is continuous everywhere.
This is due to definition of `Real.log` for negative numbers. -/
lemma h₂_continuous : Continuous h₂ := by
  have mycalc (x : ℝ) : (-x * (log x / log 2)) = -((x * log x) / log 2) := by
      field_simp
  have : h₂ = fun x ↦ h₂ x := by ext; rfl
  rw [this]
  simp_rw [h₂, log₂, logb]
  apply Continuous.add
  simp_rw [mycalc]
  apply Continuous.neg
  apply Continuous.div_const
  apply continuous_mul_log
  have mycalc2 (x : ℝ) : -((1-x) * (log (1-x) / log 2)) = -(((1-x) * log (1-x))) / log 2 := by field_simp
  simp_rw [mycalc2]
  apply Continuous.div_const
  apply Continuous.neg
  exact Continuous.comp continuous_mul_log (show Continuous fun x ↦ 1 - x by continuity)

lemma strictConcave_h2 : StrictConcaveOn ℝ (Icc 0 1) h₂ := by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc 0 1) h₂_continuous.continuousOn
  intro x hx
  simp_all
  have : deriv h₂ = fun x ↦ deriv h₂ x := by rfl
  rw [this]
  have : (fun x ↦ deriv h₂ x) = (fun x ↦ log₂ (1 - x) - log₂ x) := by
    ext
    -- exact deriv_h₂
    sorry
  sorry

/- Binary entropy is strictly increasing in interval [0, 1/2]. -/
lemma h2_strictMono : StrictMonoOn h₂ (Set.Icc 0 (1/2)) := by
  intro p1 hp1 p2 hp2 p1le2
  apply Convex.strictMonoOn_of_deriv_pos (convex_Icc 0 (1 / 2)) _ _ hp1 hp2 p1le2
  · apply h₂_continuous.continuousOn
  · intro x hx
    simp at hx
    rw [←one_div 2] at hx
    rw [deriv_h₂ (by linarith) (by linarith)]
    · simp [log₂, logb]
      apply mul_log2_lt.mpr
      field_simp
      have : 1 - x ∈ Ioi 0 := by
        simp [mem_Ioi, sub_pos, hx.2]
        linarith
      apply Real.strictMonoOn_log hx.1 this
      linarith
