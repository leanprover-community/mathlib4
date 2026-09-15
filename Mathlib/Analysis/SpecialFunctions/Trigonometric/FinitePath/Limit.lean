/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.FinitePath.Coherence

/-!
# Limit of finite path coherence

The coherence tends to the square root of pi squared over three minus two.
-/

@[expose] public section

noncomputable section
open Real Filter
open scoped Topology
namespace Real.FinitePath
theorem size_tendsto_atTop : Tendsto size atTop atTop := by
  unfold size
  exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop

theorem angle_tendsto_zero : Tendsto angle atTop (𝓝 0) := by
  unfold angle
  exact size_tendsto_atTop.const_div_atTop π

private theorem coherenceSq_sinc_tendsto :
    Tendsto
      (fun d : ℕ =>
        2 * (1 - 2 / size d) / Real.cos (angle d) ^ 2 *
          ((π ^ 2 * Real.sinc (angle d) ^ 2 +
            2 * Real.sin (angle d) ^ 2) / 6 - 1))
      atTop (𝓝 (π ^ 2 / 3 - 2)) := by
  have hratio : Tendsto (fun d : ℕ => 1 - 2 / size d) atTop (𝓝 1) := by
    convert tendsto_const_nhds.sub
      (size_tendsto_atTop.const_div_atTop 2) using 1
    norm_num
  have hcos : Tendsto
      (fun d : ℕ => Real.cos (angle d) ^ 2) atTop (𝓝 1) := by
    simpa [Real.cos_zero] using
      (Real.continuous_cos.continuousAt.tendsto.comp angle_tendsto_zero).pow 2
  have hsinc : Tendsto
      (fun d : ℕ => Real.sinc (angle d) ^ 2) atTop (𝓝 1) := by
    simpa [Real.sinc_zero] using
      (Real.continuous_sinc.continuousAt.tendsto.comp angle_tendsto_zero).pow 2
  have hsin : Tendsto
      (fun d : ℕ => Real.sin (angle d) ^ 2) atTop (𝓝 0) := by
    simpa [Real.sin_zero] using
      (Real.continuous_sin.continuousAt.tendsto.comp angle_tendsto_zero).pow 2
  have hbracket : Tendsto
      (fun d : ℕ =>
        (π ^ 2 * Real.sinc (angle d) ^ 2 +
          2 * Real.sin (angle d) ^ 2) / 6 - 1)
      atTop (𝓝 (π ^ 2 / 6 - 1)) := by
    convert ((tendsto_const_nhds.mul hsinc).add
      (tendsto_const_nhds.mul hsin)).div_const 6 |>.sub_const 1 using 1
    ring_nf
  have hfactor : Tendsto
      (fun d : ℕ => 2 * (1 - 2 / size d) / Real.cos (angle d) ^ 2)
      atTop (𝓝 2) := by
    have htworatio : Tendsto
        (fun d : ℕ => (2 : ℝ) * (1 - 2 / size d))
        atTop (𝓝 ((2 : ℝ) * 1)) :=
      tendsto_const_nhds.mul hratio
    convert htworatio.div hcos (by norm_num : (1 : ℝ) ≠ 0) using 1
    ext d
    simp
  convert hfactor.mul hbracket using 1
  · ext d
    ring_nf

theorem coherenceSq_tendsto :
    Tendsto coherenceSq atTop (𝓝 (π ^ 2 / 3 - 2)) := by
  apply coherenceSq_sinc_tendsto.congr'
  filter_upwards with d
  exact (coherenceSq_eq_sinc d).symm

theorem coherence_tendsto : Tendsto coherence atTop (𝓝 coherenceLimit) := by
  unfold coherence coherenceLimit
  exact Real.continuous_sqrt.continuousAt.tendsto.comp coherenceSq_tendsto

theorem coherence_tendsto_aux : Tendsto coherence atTop (𝓝 coherenceLimit) :=
  coherence_tendsto

theorem gap_tendsto :
    Tendsto gap atTop (𝓝 gapLimit) := by
  unfold gap gapLimit
  exact coherence_tendsto.sub_const 1

theorem gapLimit_pos : 0 < gapLimit := by
  unfold gapLimit coherenceLimit
  have hpi : (3 : ℝ) < π := Real.pi_gt_three
  have hx : (1 : ℝ) < π ^ 2 / 3 - 2 := by
    nlinarith [Real.pi_pos]
  have hs := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hx
  rw [Real.sqrt_one] at hs
  linarith

theorem gap_tendsto_and_gapLimit_pos :
    Tendsto gap atTop (𝓝 gapLimit) ∧ gapLimit = coherenceLimit - 1 ∧ 0 < gapLimit :=
  ⟨gap_tendsto, rfl, gapLimit_pos⟩

theorem coherenceLimit_pos : 0 < coherenceLimit := by
  have h := gapLimit_pos
  unfold gapLimit at h
  linarith

theorem firstOrderGap_strictMono : StrictMono firstOrderGap := by
  intro a b hab
  have hNa : 0 < size a := by
    unfold size
    positivity
  have hNlt : size a < size b := by
    have habr : (a : ℝ) < b := by exact_mod_cast hab
    unfold size
    linarith
  have hinv : 1 / size b < 1 / size a :=
    one_div_lt_one_div_of_lt hNa hNlt
  unfold firstOrderGap
  have hmul := mul_lt_mul_of_pos_left hinv coherenceLimit_pos
  simpa [div_eq_mul_inv] using sub_lt_sub_left hmul gapLimit

end Real.FinitePath
