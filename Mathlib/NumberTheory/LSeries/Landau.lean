/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.NumberTheory.LSeries.Positivity

import Mathlib.Analysis.Complex.TaylorSeries

/-!
# Landau's theorem for L-series with nonnegative coefficients

Let `a : ℕ → ℂ` take nonnegative real values. We show that the real point of the abscissa of
absolute convergence of `LSeries a` is a singularity (Landau, 1905).

## Main results

* `LSeries.LSeriesSummable_of_differentiableOn_ball`: if `x` is real with
  `abscissaOfAbsConv a < x` and `f` is holomorphic on `ball x R` and agrees with `LSeries a`
  near `x`, then `LSeries a` converges absolutely at every real `y` with `x - R < y < x`.
* `LSeries.not_differentiableOn_of_abscissaOfAbsConv_eq`: if `abscissaOfAbsConv a = σ` is real,
  there is no holomorphic function on `{s | σ < s.re} ∪ ball σ ε` agreeing with `LSeries a`
  on the half-plane `{s | σ < s.re}`.

The proof expands `f` in its Taylor series at `x`. By `LSeries_iteratedDeriv` the `k`-th
coefficient is a series of nonnegative reals in `n`, so the resulting double series can be
rearranged, and summing the exponential series in `k` gives `∑ₙ ‖term a y n‖`.
-/

public section

open Complex LSeries
open scoped ComplexOrder Nat

namespace LSeries

lemma iterate_logMul_apply (a : ℕ → ℂ) (k n : ℕ) :
    (logMul^[k] a) n = (Real.log n : ℂ) ^ k * a n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', logMul, ih, ← natCast_log]; ring

lemma iterate_logMul_nonneg {a : ℕ → ℂ} (ha : 0 ≤ a) (k : ℕ) : 0 ≤ logMul^[k] a := by
  intro n
  rw [iterate_logMul_apply]
  have h1 : (0 : ℂ) ≤ (Real.log n : ℂ) ^ k := by
    rw [← ofReal_pow]; exact_mod_cast pow_nonneg (Real.log_natCast_nonneg n) k
  exact mul_nonneg h1 (ha n)

private lemma ofReal_norm_of_nonneg {z : ℂ} (hz : 0 ≤ z) : ((‖z‖ : ℝ) : ℂ) = z := by
  have h := eq_re_of_ofReal_le hz
  rw [h, norm_real, Real.norm_eq_abs, abs_of_nonneg]
  exact (Complex.zero_le_real.mp (h ▸ hz))

private lemma norm_term_iterate (a : ℕ → ℂ) (x : ℝ) (k n : ℕ) :
    ‖term (logMul^[k] a) x n‖ = Real.log n ^ k * ‖term a x n‖ := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [term_of_ne_zero hn, term_of_ne_zero hn, iterate_logMul_apply, norm_div, norm_div,
      norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_natCast_nonneg n)]
    ring

/-- If `a ≥ 0`, `x` is real to the right of the abscissa of absolute convergence, and `f` is
holomorphic on `ball x R` and agrees with `L a` near `x`, then `L a` converges absolutely at every
real `y` with `x - R < y < x`. -/
theorem LSeriesSummable_of_differentiableOn_ball {a : ℕ → ℂ} (ha : 0 ≤ a) {x : ℝ}
    (hx : abscissaOfAbsConv a < x)
    {f : ℂ → ℂ} {R : ℝ} (hf : DifferentiableOn ℂ f (Metric.ball (x : ℂ) R))
    (hfx : f =ᶠ[nhds (x : ℂ)] LSeries a) {y : ℝ} (hy : y < x) (hyR : x - y < R) :
    LSeriesSummable a y := by
  set N : ℕ → ℕ → ℝ := fun k n => ‖term (logMul^[k] a) x n‖ with hN
  set G : ℕ × ℕ → ℝ := fun p => ((p.1)! : ℝ)⁻¹ * (x - y) ^ p.1 * N p.1 p.2 with hG
  have hG0 : 0 ≤ G := fun p => by
    simp only [hG, Pi.zero_apply]
    have : 0 ≤ x - y := by linarith
    positivity
  -- each row summable
  have hrow : ∀ k, Summable fun n => G (k, n) := by
    intro k
    have hs : LSeriesSummable (logMul^[k] a) x :=
      LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using hx)
    simpa [hG, hN, mul_assoc] using hs.norm.mul_left (((k)! : ℝ)⁻¹ * (x - y) ^ k)
  -- Taylor series
  have hyball : (y : ℂ) ∈ Metric.ball (x : ℂ) R := by
    rw [Metric.mem_ball, dist_eq, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_sub_comm,
      abs_of_pos (by linarith)]; exact hyR
  have hT := Complex.hasSum_taylorSeries_on_ball hf hyball
  have hcoef : ∀ k, ((k ! : ℂ)⁻¹ • ((y : ℂ) - x) ^ k • iteratedDeriv k f x) =
      ((∑' n, G (k, n) : ℝ) : ℂ) := by
    intro k
    rw [hfx.iteratedDeriv_eq, LSeries_iteratedDeriv _ (by simpa using hx), LSeries]
    have hterm : ∀ n, term (logMul^[k] a) x n = ((N k n : ℝ) : ℂ) := fun n =>
      (ofReal_norm_of_nonneg (term_nonneg (iterate_logMul_nonneg ha k n) x)).symm
    simp_rw [hterm]
    rw [← ofReal_tsum]
    simp only [hG, tsum_mul_left, smul_eq_mul]
    push_cast
    have : ((y : ℂ) - x) ^ k * (-1) ^ k = ((x : ℂ) - y) ^ k := by
      rw [← mul_pow]; ring_nf
    linear_combination (↑(k !) : ℂ)⁻¹ * (∑' n, (N k n : ℂ)) * this
  have hcol : Summable fun k => ∑' n, G (k, n) := by
    have := hT.summable
    simp_rw [hcoef] at this
    exact Complex.summable_ofReal.mp this
  have hprod : Summable G := (summable_prod_of_nonneg hG0).mpr ⟨hrow, hcol⟩
  have hswap := (summable_prod_of_nonneg (f := fun p : ℕ × ℕ => G p.swap)
    (fun p => hG0 p.swap)).mp hprod.prod_symm
  -- column sums are the terms at y
  have hcolsum : ∀ n, (∑' k, G (k, n)) = ‖term a y n‖ := by
    intro n
    simp only [hG, hN, norm_term_iterate]
    have : ∀ k, ((k ! : ℝ))⁻¹ * (x - y) ^ k * (Real.log n ^ k * ‖term a x n‖) =
        ‖term a x n‖ * (((x - y) * Real.log n) ^ k / k !) := fun k => by rw [mul_pow]; ring
    simp_rw [this]
    rw [tsum_mul_left, ← congrFun (NormedSpace.exp_eq_tsum_div (𝔸 := ℝ)) _,
      ← Real.exp_eq_exp_ℝ]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [norm_term_eq, norm_term_eq, ite_eq_right hn, ite_eq_right hn]
      simp only [ofReal_re]
      have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      rw [mul_comm ((x - y)) _, ← Real.rpow_def_of_pos hn', div_mul_eq_mul_div, mul_div_assoc,
        ← Real.rpow_sub hn']
      rw [show x - y - x = -y by ring, Real.rpow_neg hn'.le, div_eq_mul_inv]
  have hy_sum : Summable fun n => ‖term a y n‖ := by
    have := hswap.2
    simp only [Prod.swap] at this
    simpa [hcolsum] using this
  exact hy_sum.of_norm

/-- **Landau's theorem.** If `a ≥ 0` and the abscissa of absolute convergence of `L a` is a real
number `σ`, then `L a` admits no holomorphic extension to the half-plane `σ < re s` together
with a disc around `σ`. -/
theorem not_differentiableOn_of_abscissaOfAbsConv_eq {a : ℕ → ℂ} (ha : 0 ≤ a) {σ : ℝ}
    (hσ : abscissaOfAbsConv a = σ)
    {f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f ({s | σ < s.re} ∪ Metric.ball (σ : ℂ) ε))
    (heq : Set.EqOn f (LSeries a) {s | σ < s.re}) : False := by
  set x : ℝ := σ + ε / 4
  set y : ℝ := σ - ε / 8
  have hopen : IsOpen {s : ℂ | σ < s.re} := isOpen_lt continuous_const continuous_re
  have hxmem : (x : ℂ) ∈ {s : ℂ | σ < s.re} := by
    simp only [Set.mem_ofPred_eq, ofReal_re, x]; linarith
  have hfx : f =ᶠ[nhds (x : ℂ)] LSeries a := heq.eventuallyEq_of_mem (hopen.mem_nhds hxmem)
  have hball :
      Metric.ball (x : ℂ) (ε / 2) ⊆ {s | σ < s.re} ∪ Metric.ball (σ : ℂ) ε := by
    intro z hz
    by_cases h : σ < z.re
    · exact Or.inl h
    · right
      rw [Metric.mem_ball] at hz ⊢
      have hxσ : dist (x : ℂ) σ = ε / 4 := by
        rw [dist_eq, ← ofReal_sub, norm_real, Real.norm_eq_abs,
          abs_of_pos (by simp [x]; linarith)]
        simp [x]
      calc dist z σ ≤ dist z x + dist (x : ℂ) σ := dist_triangle _ _ _
        _ < ε / 2 + ε / 4 := by rw [hxσ]; linarith
        _ < ε := by linarith
  have hx : abscissaOfAbsConv a < x := by
    rw [hσ]; exact_mod_cast (show σ < x by simp [x]; linarith)
  have hs := LSeriesSummable_of_differentiableOn_ball ha hx (hf.mono hball) hfx (y := y)
    (by simp [x, y]; linarith) (by simp [x, y]; linarith)
  have hle := hs.abscissaOfAbsConv_le
  rw [hσ, ofReal_re] at hle
  have : σ ≤ y := by exact_mod_cast hle
  simp [y] at this
  linarith

end LSeries
