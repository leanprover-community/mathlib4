/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Derivative of Γ at positive integers

We prove the formula for the derivative of `Real.Gamma` at a positive integer:

`deriv Real.Gamma (n + 1) = Nat.factorial n * (-Real.eulerMascheroniConstant + harmonic n)`

-/

open Real Set Filter Topology

open Nat

/-- Explicit formula for the derivative of the Gamma function at integers, in terms of harmonic
numbers and the Euler-Mascheroni constant `γ`. -/
lemma Real.deriv_Gamma_nat (n : ℕ) :
    deriv Gamma (n + 1) = (n)! * (-eulerMascheroniConstant + harmonic n) := by
  /- This follows from two properties of the function `f n = log (Gamma n)`:
  firstly, the elementary computation that `deriv f (n + 1) = deriv f n + 1 / n`, so that
  `deriv f n = deriv f 1 + harmonic n`; secondly, the convexity of `f` (the Bohr-Mollerup theorem),
  which shows that `deriv f n` is `log n + o(1)` as `n → ∞`.
  `-/
  let f := log ∘ Gamma
  -- First reduce to computing derivative of `log ∘ Gamma`.
  suffices deriv (log ∘ Gamma) (n + 1) = -eulerMascheroniConstant + harmonic n by
    rwa [Function.comp_def, deriv.log ?_ (by positivity), Gamma_nat_eq_factorial,
    div_eq_iff_mul_eq (by positivity), mul_comm, Eq.comm] at this
    exact differentiableAt_Gamma (fun m ↦ by linarith)
  have hc : ConvexOn ℝ (Ioi 0) f := convexOn_log_Gamma
  have h_rec (x : ℝ) (hx : 0 < x) : f (x + 1) = f x + log x := by simp only [f, Function.comp_apply,
      Gamma_add_one hx.ne', log_mul hx.ne' (Gamma_pos_of_pos hx).ne', add_comm]
  have hder {x : ℝ} (hx : 0 < x) : DifferentiableAt ℝ f x := by
    refine ((differentiableAt_Gamma ?_).log (Gamma_ne_zero ?_)) <;>
    exact fun m ↦ ne_of_gt (by linarith)
  -- Express derivative at general `n` in terms of value at `1` using recurrence relation
  have hder_rec (x : ℝ) (hx : 0 < x) : deriv f (x + 1) = deriv f x + 1 / x := by
    rw [← deriv_comp_add_const _ _ (hder <| by positivity), one_div, ← deriv_log,
      ← deriv_add (hder <| by positivity) (differentiableAt_log hx.ne')]
    apply EventuallyEq.deriv_eq
    filter_upwards [eventually_gt_nhds hx] using h_rec
  have hder_nat (n : ℕ) : deriv f (n + 1) = deriv f 1 + harmonic n := by
    induction' n with n hn
    · simp
    · rw [cast_succ, hder_rec (n + 1) (by positivity), hn, harmonic_succ]
      push_cast
      ring
  suffices -deriv f 1 = eulerMascheroniConstant by rw [hder_nat n, ← this, neg_neg]
  -- Use convexity to show derivative of `f` at `n + 1` is between `log n` and `log (n + 1)`
  have derivLB (n : ℕ) (hn : 0 < n) : log n ≤ deriv f (n + 1) := by
    refine (le_of_eq ?_).trans <| hc.slope_le_deriv (mem_Ioi.mpr <| Nat.cast_pos.mpr hn)
      (by positivity : _ < (_ : ℝ)) (by linarith) (hder <| by positivity)
    rw [slope_def_field, show n + 1 - n = (1 : ℝ) by ring, div_one, h_rec n (by positivity),
      add_sub_cancel']
  have derivUB (n : ℕ) : deriv f (n + 1) ≤ log (n + 1) := by
    refine (hc.deriv_le_slope (by positivity : (0 : ℝ) < n + 1) (by positivity : (0 : ℝ) < n + 2)
        (by linarith) (hder <| by positivity)).trans (le_of_eq ?_)
    rw [slope_def_field, show n + 2 - (n + 1) = (1 : ℝ) by ring, div_one,
      show n + 2 = (n + 1) + (1 : ℝ) by ring, h_rec (n + 1) (by positivity), add_sub_cancel']
  -- deduce `-deriv f 1` is bounded above + below by sequences which both tend to `γ`
  apply le_antisymm
  · apply ge_of_tendsto tendsto_harmonic_sub_log
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [le_sub_iff_add_le', ← sub_eq_add_neg, sub_le_iff_le_add', ← hder_nat]
    exact derivLB n hn
  · apply le_of_tendsto tendsto_harmonic_sub_log_add_one
    filter_upwards with n
    rw [sub_le_iff_le_add', ← sub_eq_add_neg, le_sub_iff_add_le', ← hder_nat]
    exact derivUB n

lemma Real.eulerMascheroniConstant_eq_neg_deriv : eulerMascheroniConstant = -deriv Gamma 1 := by
  rw [show (1 : ℝ) = ↑(0 : ℕ) + 1 by simp, deriv_Gamma_nat 0]
  simp
