/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Derivative of Γ at positive integers

We prove the formula for the derivative of `Real.Gamma` at a positive integer:

`deriv Real.Gamma (n + 1) = Nat.factorial n * (-Real.eulerMascheroniConstant + harmonic n)`

-/

open Nat Set Filter Topology

local notation "γ" => Real.eulerMascheroniConstant

namespace Real

/-- Explicit formula for the derivative of the Gamma function at positive integers, in terms of
harmonic numbers and the Euler-Mascheroni constant `γ`. -/
lemma deriv_Gamma_nat (n : ℕ) :
    deriv Gamma (n + 1) = n ! * (-γ + harmonic n) := by
  /- This follows from two properties of the function `f n = log (Gamma n)`:
  firstly, the elementary computation that `deriv f (n + 1) = deriv f n + 1 / n`, so that
  `deriv f n = deriv f 1 + harmonic n`; secondly, the convexity of `f` (the Bohr-Mollerup theorem),
  which shows that `deriv f n` is `log n + o(1)` as `n → ∞`. -/
  let f := log ∘ Gamma
  -- First reduce to computing derivative of `log ∘ Gamma`.
  suffices deriv (log ∘ Gamma) (n + 1) = -γ + harmonic n by
    rwa [Function.comp_def, deriv.log (differentiableAt_Gamma (fun m ↦ by linarith))
      (by positivity), Gamma_nat_eq_factorial, div_eq_iff_mul_eq (by positivity),
      mul_comm, Eq.comm] at this
  have hc : ConvexOn ℝ (Ioi 0) f := convexOn_log_Gamma
  have h_rec (x : ℝ) (hx : 0 < x) : f (x + 1) = f x + log x := by simp only [f, Function.comp_apply,
      Gamma_add_one hx.ne', log_mul hx.ne' (Gamma_pos_of_pos hx).ne', add_comm]
  have hder {x : ℝ} (hx : 0 < x) : DifferentiableAt ℝ f x := by
    refine ((differentiableAt_Gamma ?_).log (Gamma_ne_zero ?_)) <;>
    exact fun m ↦ ne_of_gt (by linarith)
  -- Express derivative at general `n` in terms of value at `1` using recurrence relation
  have hder_rec (x : ℝ) (hx : 0 < x) : deriv f (x + 1) = deriv f x + 1 / x := by
    rw [← deriv_comp_add_const, one_div, ← deriv_log,
      ← deriv_add (hder <| by positivity) (differentiableAt_log hx.ne')]
    apply EventuallyEq.deriv_eq
    filter_upwards [eventually_gt_nhds hx] using h_rec
  have hder_nat (n : ℕ) : deriv f (n + 1) = deriv f 1 + harmonic n := by
    induction n with
    | zero => simp
    | succ n hn =>
      rw [cast_succ, hder_rec (n + 1) (by positivity), hn, harmonic_succ]
      push_cast
      ring
  suffices -deriv f 1 = γ by rw [hder_nat n, ← this, neg_neg]
  -- Use convexity to show derivative of `f` at `n + 1` is between `log n` and `log (n + 1)`
  have derivLB (n : ℕ) (hn : 0 < n) : log n ≤ deriv f (n + 1) := by
    refine (le_of_eq ?_).trans <| hc.slope_le_deriv (mem_Ioi.mpr <| Nat.cast_pos.mpr hn)
      (by positivity : _ < (_ : ℝ)) (by linarith) (hder <| by positivity)
    rw [slope_def_field, show n + 1 - n = (1 : ℝ) by ring, div_one, h_rec n (by positivity),
      add_sub_cancel_left]
  have derivUB (n : ℕ) : deriv f (n + 1) ≤ log (n + 1) := by
    refine (hc.deriv_le_slope (by positivity : (0 : ℝ) < n + 1) (by positivity : (0 : ℝ) < n + 2)
        (by linarith) (hder <| by positivity)).trans (le_of_eq ?_)
    rw [slope_def_field, show n + 2 - (n + 1) = (1 : ℝ) by ring, div_one,
      show n + 2 = (n + 1) + (1 : ℝ) by ring, h_rec (n + 1) (by positivity), add_sub_cancel_left]
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


lemma hasDerivAt_Gamma_nat (n : ℕ) :
    HasDerivAt Gamma (n ! * (-γ + harmonic n)) (n + 1) :=
  (deriv_Gamma_nat n).symm ▸
    (differentiableAt_Gamma fun m ↦ (by linarith : (n : ℝ) + 1 ≠ -m)).hasDerivAt

lemma eulerMascheroniConstant_eq_neg_deriv : γ = -deriv Gamma 1 := by
  rw [show (1 : ℝ) = ↑(0 : ℕ) + 1 by simp, deriv_Gamma_nat 0]
  simp

lemma hasDerivAt_Gamma_one : HasDerivAt Gamma (-γ) 1 := by
  simpa only [factorial_zero, cast_one, harmonic_zero, Rat.cast_zero, add_zero, mul_neg, one_mul,
    cast_zero, zero_add] using hasDerivAt_Gamma_nat 0

lemma hasDerivAt_Gamma_one_half : HasDerivAt Gamma (-√π * (γ + 2 * log 2)) (1 / 2) := by
  have h_diff {s : ℝ} (hs : 0 < s) : DifferentiableAt ℝ Gamma s :=
    differentiableAt_Gamma fun m ↦ ((neg_nonpos.mpr m.cast_nonneg).trans_lt hs).ne'
  have h_diff' {s : ℝ} (hs : 0 < s) : DifferentiableAt ℝ (fun s ↦ Gamma (2 * s)) s :=
    .comp (g := Gamma) _ (h_diff <| mul_pos two_pos hs) (differentiableAt_id.const_mul _)
  refine (h_diff one_half_pos).hasDerivAt.congr_deriv ?_
  -- We calculate the deriv of Gamma at 1/2 using the doubling formula, since we already know
  -- the derivative of Gamma at 1.
  calc deriv Gamma (1 / 2)
  _ = (deriv (fun s ↦ Gamma s * Gamma (s + 1 / 2)) (1 / 2)) + √π * γ := by
    rw [deriv_mul, Gamma_one_half_eq,
      add_assoc, ← mul_add, deriv_comp_add_const,
      (by norm_num : 1/2 + 1/2 = (1 : ℝ)), Gamma_one, mul_one,
      eulerMascheroniConstant_eq_neg_deriv, add_neg_cancel, mul_zero, add_zero]
    · apply h_diff; norm_num -- s = 1
    · exact ((h_diff (by norm_num)).hasDerivAt.comp_add_const).differentiableAt -- s = 1
  _ = (deriv (fun s ↦ Gamma (2 * s) * 2 ^ (1 - 2 * s) * √π) (1 / 2)) + √π * γ := by
    rw [funext Gamma_mul_Gamma_add_half]
  _ = √π * (deriv (fun s ↦ Gamma (2 * s) * 2 ^ (1 - 2 * s)) (1 / 2) + γ) := by
    rw [mul_comm √π, mul_comm √π, deriv_mul_const, add_mul]
    apply DifferentiableAt.mul
    · exact .comp (g := Gamma) _ (by apply h_diff; norm_num) -- s = 1
        (differentiableAt_id.const_mul _)
    · exact (differentiableAt_const _).rpow (by fun_prop) two_ne_zero
  _ = √π * (deriv (fun s ↦ Gamma (2 * s)) (1 / 2) +
              deriv (fun s : ℝ ↦ 2 ^ (1 - 2 * s)) (1 / 2) + γ) := by
    congr 2
    rw [deriv_mul]
    · congr 1 <;> norm_num
    · exact h_diff' one_half_pos
    · exact DifferentiableAt.rpow (by fun_prop) (by fun_prop) two_ne_zero
  _ = √π * (-2 * γ + deriv (fun s : ℝ ↦ 2 ^ (1 - 2 * s)) (1 / 2) + γ) := by
    congr 3
    change deriv (Gamma ∘ fun s ↦ 2 * s) _ = _
    rw [deriv_comp, deriv_const_mul, mul_one_div, div_self two_ne_zero, deriv_id''] <;>
    dsimp only
    · rw [mul_one, mul_comm, hasDerivAt_Gamma_one.deriv, mul_neg, neg_mul]
    · fun_prop
    · apply h_diff; norm_num -- s = 1
    · fun_prop
  _ = √π * (-2 * γ + -(2 * log 2) + γ) := by
    congr 3
    apply HasDerivAt.deriv
    have := HasDerivAt.rpow (hasDerivAt_const (1 / 2 : ℝ) (2 : ℝ))
      (?_ : HasDerivAt (fun s : ℝ ↦ 1 - 2 * s) (-2) (1 / 2)) two_pos
    · norm_num at this; exact this
    simp_rw [mul_comm (2 : ℝ) _]
    apply HasDerivAt.const_sub
    exact hasDerivAt_mul_const (2 : ℝ)
  _ = -√π * (γ + 2 * log 2) := by ring

end Real

namespace Complex

open scoped Real

private lemma HasDerivAt.complex_of_real {f : ℂ → ℂ} {g : ℝ → ℝ} {g' s : ℝ}
    (hf : DifferentiableAt ℂ f s) (hg : HasDerivAt g g' s) (hfg : ∀ s : ℝ, f ↑s = ↑(g s)) :
    HasDerivAt f ↑g' s := by
  refine HasDerivAt.congr_deriv hf.hasDerivAt ?_
  rw [← (funext hfg ▸ hf.hasDerivAt.comp_ofReal.deriv :)]
  exact hg.ofReal_comp.deriv

lemma differentiableAt_Gamma_nat_add_one (n : ℕ) :
    DifferentiableAt ℂ Gamma (n + 1) := by
  refine differentiableAt_Gamma _ (fun m ↦ ?_)
  simp only [Ne, ← ofReal_natCast, ← ofReal_one, ← ofReal_add, ← ofReal_neg, ofReal_inj,
    eq_neg_iff_add_eq_zero]
  positivity

@[deprecated (since := "2025-06-06")] alias differentiable_at_Gamma_nat_add_one :=
  differentiableAt_Gamma_nat_add_one

lemma hasDerivAt_Gamma_nat (n : ℕ) :
    HasDerivAt Gamma (n ! * (-γ + harmonic n)) (n + 1) := by
  exact_mod_cast HasDerivAt.complex_of_real
    (by exact_mod_cast differentiableAt_Gamma_nat_add_one n)
    (Real.hasDerivAt_Gamma_nat n) Gamma_ofReal

/-- Explicit formula for the derivative of the complex Gamma function at positive integers, in
terms of harmonic numbers and the Euler-Mascheroni constant `γ`. -/
lemma deriv_Gamma_nat (n : ℕ) :
    deriv Gamma (n + 1) = n ! * (-γ + harmonic n) :=
  (hasDerivAt_Gamma_nat n).deriv

lemma hasDerivAt_Gamma_one : HasDerivAt Gamma (-γ) 1 := by
  simpa only [factorial_zero, cast_one, harmonic_zero, Rat.cast_zero, add_zero, mul_neg, one_mul,
    cast_zero, zero_add] using hasDerivAt_Gamma_nat 0

lemma hasDerivAt_Gamma_one_half : HasDerivAt Gamma (-√π * (γ + 2 * log 2)) (1 / 2) := by
  have := HasDerivAt.complex_of_real
    (differentiableAt_Gamma _ ?_) Real.hasDerivAt_Gamma_one_half Gamma_ofReal
  · simpa only [neg_mul, one_div, ofReal_neg, ofReal_mul, ofReal_add, ofReal_ofNat, ofNat_log,
      ofReal_inv] using this
  · intro m
    rw [← ofReal_natCast, ← ofReal_neg, ne_eq, ofReal_inj]
    exact ((neg_nonpos.mpr m.cast_nonneg).trans_lt one_half_pos).ne'

lemma hasDerivAt_Gammaℂ_one : HasDerivAt Gammaℂ (-(γ + log (2 * π)) / π) 1 := by
  let f (s : ℂ) : ℂ := 2 * (2 * π) ^ (-s)
  have : HasDerivAt (fun s : ℂ ↦ 2 * (2 * π : ℂ) ^ (-s)) (-log (2 * π) / π) 1 := by
    have := (hasDerivAt_neg' (1 : ℂ)).const_cpow (c := 2 * π)
      (Or.inl (by exact_mod_cast Real.two_pi_pos.ne'))
    refine (this.const_mul 2).congr_deriv ?_
    rw [mul_neg_one, mul_neg, cpow_neg_one, ← div_eq_inv_mul, ← mul_div_assoc,
      mul_div_mul_left _ _ two_ne_zero, neg_div]
  have := this.mul hasDerivAt_Gamma_one
  simp only [f] at this
  rwa [Gamma_one, mul_one, cpow_neg_one, ← div_eq_mul_inv, ← div_div, div_self two_ne_zero,
    mul_comm (1 / _), mul_one_div, ← _root_.add_div, ← neg_add, add_comm] at this

lemma hasDerivAt_Gammaℝ_one : HasDerivAt Gammaℝ (-(γ + log (4 * π)) / 2) 1 := by
  let f (s : ℂ) : ℂ := π ^ (-s / 2)
  let g (s : ℂ) : ℂ := Gamma (s / 2)
  have aux : (π : ℂ) ^ (1 / 2 : ℂ) = ↑√π := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le, ofReal_div, ofReal_one, ofReal_ofNat]
  have aux2 : (√π : ℂ) ≠ 0 := by rw [ofReal_ne_zero]; positivity
  have hf : HasDerivAt f (-log π / 2 / √π) 1 := by
    have := ((hasDerivAt_neg (1 : ℂ)).div_const 2).const_cpow (c := π) (Or.inr (by norm_num))
    refine this.congr_deriv ?_
    rw [mul_assoc, ← mul_div_assoc, mul_neg_one, neg_div, cpow_neg, ← div_eq_inv_mul, aux]
  have hg : HasDerivAt g (-√π * (γ + 2 * log 2) / 2) 1 := by
    have := hasDerivAt_Gamma_one_half.comp 1 (?_ : HasDerivAt (fun s : ℂ ↦ s / 2) (1 / 2) 1)
    · rwa [mul_one_div] at this
    · exact (hasDerivAt_id _).div_const _
  refine HasDerivAt.congr_deriv (hf.mul hg) ?_
  simp only [f]
  rw [Gamma_one_half_eq, aux, div_mul_cancel₀ _ aux2, neg_div _ (1 : ℂ), cpow_neg, aux,
    mul_div_assoc, ← mul_assoc, mul_neg, inv_mul_cancel₀ aux2, neg_one_mul, ← neg_div,
    ← _root_.add_div, ← neg_add, add_comm, add_assoc, ← ofReal_log Real.pi_pos.le, ← ofReal_ofNat,
    ← ofReal_log zero_le_two,
    ← ofReal_mul, ← Nat.cast_ofNat (R := ℝ), ← Real.log_pow, ← ofReal_add,
    ← Real.log_mul (by positivity) (by positivity),
    Nat.cast_ofNat, ofReal_ofNat, ofReal_log (by positivity)]
  norm_num

end Complex
