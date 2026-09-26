/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alastair Irving, Pietro Monticone, Robby Sneiderman, Guiseppe Sorge, Terence Tao,
Yan Yablonovskiy, Yi Yuan
-/
module

public import Mathlib.NumberTheory.Mertens.Weight
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import Mathlib.NumberTheory.LSeries.PrimesInAP

import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.InvLog
import Mathlib.Analysis.SpecialFunctions.Log.Sum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic.NormNum.Prime


/-!
# Constructing the Mertens weights

This file constructs the two main examples of Mertens weights: the von Mangoldt weight
`Weight.vonMangoldt n = Λ n / n` and the prime weight `Weight.prime`, and computes their
explicit constants.

-/

@[expose] public section

namespace Mertens

open Nat hiding log log_pos
open Finset Filter Real Chebyshev intervalIntegral Asymptotics MeasureTheory Topology
  Measurable ContinuousOn
open ArithmeticFunction hiding log
open scoped Nat.Prime

section ConstructWeights

/-!
## Constructing the two Mertens weights

In this section we construct the two standard Mertens weights:

* The von Mangoldt weight `Weight.vonMangoldt n = Λ n / n`, where `Λ` is the von Mangoldt function.
* The prime weight `Weight.prime n = log n / n` if `n` is prime and `0` otherwise.

In the former case we obtain lower and upper bounds of `-2` and `log 4 + 1` for the first Mertens
theorem error term, with an improvement of the lower bound to `-1` for natural numbers.

In the latter case we obtain lower and upper bounds of `-3` and `log 4`, with an improvement of
the lower bound to `-2` in the natural number case.

The two sums `∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n` and `∑ n ∈ PrimesLE ⌊x⌋₊, log p / p` arising in the
first Mertens theorem differ asymptotically by a constant `E₁ = 0.755366...`.  Here we bound
this constant between `0` and `1`.
-/

variable (x : ℝ) (N : ℕ)

/-- The von Mangoldt weight is `Λ n / n`. -/
noncomputable def vonMangoldtFun : ℕ → ℝ := fun n ↦ Λ n / n

/-- The prime weight is `log n / n` if `n` is prime and `0` otherwise. -/
noncomputable def primeFun : ℕ → ℝ := fun n ↦ if n.Prime then log n / n else 0

/-- The sum of the prime weight over `Ioc 0 N` unfolds to `∑ log p / p` over the primes `≤ N`. -/
private lemma sum_prime_eq' : ∑ n ∈ Ioc 0 N, primeFun n = ∑ p ∈ primesLE N, log p / p := by
  simp [primeFun, primesLE_eq_filter_Ioc_zero, sum_filter]

/-- The partial sum of the logarithm is equal to a weighted sum of the von Mangoldt function. -/
theorem sum_log_eq_sum_mangoldt {x : ℝ} : ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊
  := by simp_rw [← log_apply, ← vonMangoldt_mul_zeta, sum_Ioc_mul_zeta_eq_sum, ← floor_div_natCast]

lemma le_mul_sum_vonMangoldt {x : ℝ} (hx : 0 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n ≤ x * ∑ n ∈ Ioc 0 ⌊x⌋₊, vonMangoldtFun n := calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by simp [mul_sum, vonMangoldtFun]; ring_nf
  _ ≥ _ := by
    grw [sum_log_eq_sum_mangoldt, floor_le]
    apply div_nonneg <;> linarith

/-- An upper bound for the weighted prime sum in terms of the Chebyshev function `θ`. -/
private lemma mul_sum_prime_le :
    x * ∑ n ∈ Ioc 0 ⌊x⌋₊, primeFun n ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, log n + θ x := calc
  _ = ∑ p ∈ primesLE ⌊x⌋₊, log p * (x / p) := by rw [sum_prime_eq', mul_sum]; ring_nf
  _ ≤ ∑ p ∈ primesLE ⌊x⌋₊, log p * (⌊x / p⌋₊ + 1) := by gcongr; exact lt_floor_add_one _|>.le
  _ = ∑ p ∈ primesLE ⌊x⌋₊, log p * ⌊x / p⌋₊ + θ x := by
    simp [mul_add, sum_add_distrib, theta, primesLE_eq_filter_Ioc_zero]
  _ ≤ _ := by
    rw [sum_log_eq_sum_mangoldt, primesLE_eq_filter_Ioc_zero, sum_filter]
    gcongr
    split_ifs with hp
    · simp [vonMangoldt_apply_prime hp]
    positivity

/-- The partial sums of the prime weight grow at most like `log x`. -/
private lemma sum_prime_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, primeFun n ≤ log x + log 4 := by
  apply le_of_mul_le_mul_left _ (by linarith : 0 < x)
  grw [mul_sum_prime_le, theta_le_log4_mul_x (by linarith), sum_log_le' hx]
  simp [field]

/-- The summand defining the constant `E₁` below, with `e₁ p` defined to equal
`log p / (p * (p - 1))` if `p` is prime and `0` otherwise. -/
noncomputable def e₁ : ℕ → ℝ := fun p ↦ if p.Prime then log p / (p * (p - 1)) else 0

/-- The constant `E₁ = 0.755366...` (https://oeis.org/A138312) is defined as the sum of
`log p / (p * (p-1))` over primes `p`. -/
noncomputable def E₁ : ℝ := ∑' p, e₁ p

theorem e₁_nonneg (p : ℕ) : 0 ≤ e₁ p := by
  unfold e₁
  split_ifs with h
  · positivity [(mod_cast h.one_le : 1 ≤ (p : ℝ))]
  simp

theorem e₁_summable : Summable e₁ := by
  refine (summable_one_div_nat_rpow.mpr (by norm_num : 1 < (3 : ℝ) / 2) |>.const_div
    4).of_nonneg_of_le e₁_nonneg fun p ↦ ?_
  unfold e₁
  split_ifs with h
  · have : 2 ≤ (p : ℝ) := mod_cast h.two_le
    have : p * ((p : ℝ) - 1) ≥ p ^ 2 / 2 := by nlinarith
    grw [log_le_rpow_div (cast_nonneg _) (by norm_num : 0 < (1 : ℝ) / 2), this]
    · field_simp
      rw [mul_assoc, ← rpow_add (by positivity)]
      ring_nf; norm_cast
    · grind
  · positivity

theorem E₁_nonneg : 0 ≤ E₁ := tsum_nonneg e₁_nonneg

/-- An upper bound for `E₁`. -/
theorem E₁_le : E₁ ≤ 1 := by
  refine e₁_summable.tsum_le_of_sum_range_le (fun N ↦ ?_)
  have : ∑ n ∈ range N, _ ≤ ∑ n ∈ range (2 * N + 5), _ :=
    sum_le_sum_of_subset_of_nonneg (by grind) (fun n _ _ ↦ e₁_nonneg n)
  have : ∑ n ∈ range (2 * N + 5), e₁ n = log 2 / 2 + log 3 / 6 + ∑ n ∈ .Ico 5 (2 * N + 5), e₁ n
      := by
    convert sum_union (s₁ := {0,1,2,3,4}) (s₂ := .Ico 5 (2 * N + 5)) (by grind [disjoint_left])
    · ext; simp; omega
    norm_num [e₁]
  have : ∑ n ∈ .Ico 5 (2 * N + 5), e₁ n = ∑ n ∈ .range N, e₁ (2 * n + 5) := by
    apply (sum_of_injOn (2 * · + 5) (by intro; grind) (by intro; grind) _ (by simp)).symm
    simp only [mem_Ico, coe_range, Set.mem_image, Set.mem_Iio, not_exists, e₁, ite_eq_right_iff]
    intro p _ h hp
    obtain ⟨ m, rfl ⟩ := hp.odd_of_ne_two (by omega)
    grind [h (m - 2)]
  let g : ℝ → ℝ := fun t ↦ log (2 * t + 3) / (2 * t + 3) ^ 2
  have : ∑ n ∈ .range N, e₁ (2 * n + 5) ≤ (5 / 4) * ∑ n ∈ .range N, g (n + 1) := by
    simp only [e₁, g, cast_add, cast_mul, cast_ofNat, mul_sum]
    gcongr with i _
    ring_nf
    have : 0 ≤ log (5 + (i : ℝ) * 2) := log_nonneg (by norm_cast; omega)
    split_ifs
    · field_simp; ring_nf; gcongr <;> norm_num
    positivity
  -- the main step: bound the tail sum by an integral, using that `g` is antitone
  have : ∑ n ∈ .range N, g (n + 1) ≤ ∫ x in 0..N, g x := by
    convert (antitoneOn_of_deriv_nonpos (convex_Icc 0 _) ..).sum_le_integral (a := N) (f := g)
        using 1
    · simp
    · simp
    · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
      have : (2 * t + 3) ≠ 0 := by grind
      fun_prop (disch := grind)
    · refine fun t ht ↦ DifferentiableAt.differentiableWithinAt ?_
      rw [interior_Icc] at ht
      have : (2 * t + 3) ^ 2 ≠ 0 := by simp; grind
      fun_prop (disch := grind)
    · intro t ht
      simp at ht
      rw [deriv_fun_div (by fun_prop (disch := grind)) (by fun_prop) (by simp; grind),
        deriv_comp_mul_left 2 (fun t ↦ log (t + 3)), deriv_comp_add_const,
        deriv_comp_mul_left 2 (fun t ↦ (t + 3) ^ 2)]
      simp
      field_simp
      have : 0 ≤ 2 * t + 3 := by linarith
      have : 1 ≤ 2 * log (2 * t + 3) := by grw [← ht.1]; simp; linarith [log_three_gt_d9]
      grw [this]; simp
  have : ∫ x in 0..N, g x ≤ (log 3 + 1) / 6 := by
    let f : ℝ → ℝ := fun t ↦ (-log (2 * t + 3) - 1) / (2 * (2 * t + 3))
    have {x} (hx : 0 ≤ x) : HasDerivAt f (g x) x := by
      have : HasDerivAt (2 * · + 3) 2 x := HasDerivAt.add_const _ (hasDerivAt_const_mul 2)
      convert! HasDerivAt.comp x ?_ this (h₂ := fun t ↦ (-log t - 1) / (2 * t))
        (h₂' := log (2 * x + 3) / (2 * (2 * x + 3)^2)) using 1
      · grind
      convert! HasDerivAt.fun_div (c' := -1 / (2 * x + 3)) _ (hasDerivAt_const_mul 2) _ using 1
      · field
      · convert! hasDerivAt_log (by linarith : 2 * x + 3 ≠ 0)|>.neg.sub_const _ using 1
        grind
      linarith
    have : 0 ≤ (N : ℝ) := cast_nonneg' N
    rw [integral_eq_sub_of_hasDerivAt (f := f)]
    · simp [f]; field_simp; grind [log_nonneg]
    · simp; grind
    · exact ContinuousOn.log (f := (2 * · + 3)) (by fun_prop) (by simp; grind)|>.div₀
        (by fun_prop) (by simp; grind)|>.intervalIntegrable
  linarith [log_two_lt_d9, log_three_lt_d9]

theorem sum_vonMangoldt_le_sum_prime_add_E₁ {x : ℝ} (hx : 1 ≤ x) :
    ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ ∑ p ∈ primesLE ⌊x⌋₊, log p / p + E₁ := by
  simp_rw [vonMangoldt_apply, ite_div, zero_div, ← sum_filter, sum_PrimePow_eq_sum_sum _
    (by linarith)]
  calc
  _ = ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ primesLE ⌊x ^ (1 / (k : ℝ))⌋₊, log p / (p ^ k : ℕ) := by
    simp only [primesLE_eq_filter_Ioc_zero]
    refine sum_congr rfl fun k hk ↦ sum_congr rfl fun p hp ↦ ?_
    rw [Prime.pow_minFac (by simp_all) (by grind)]
  _ ≤ ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ primesLE ⌊x⌋₊, log p / (p ^ k : ℕ) := by
    simp only [primesLE_eq_filter_Ioc_zero]
    gcongr with k hk
    apply rpow_le_self_of_one_le hx
    rw [mem_Icc] at hk
    exact div_le_one₀ (by norm_cast; linarith)|>.mpr (mod_cast hk.1)
  _ ≤ ∑ k ∈ Icc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ primesLE ⌊x⌋₊, log p / (p ^ k : ℕ) := by
    apply sum_le_sum_of_subset_of_nonneg _ fun _ _ _ ↦ sum_nonneg fun _ _ ↦ (by positivity)
    grw [← le_max_right]
  _ = ∑ p ∈ primesLE ⌊x⌋₊, log p / p +
      ∑ k ∈ Ioc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ primesLE ⌊x⌋₊, log p / (p ^ k : ℕ) := by
    simp [← add_sum_Ioc_eq_sum_Icc (le_max_left ..)]
  _ ≤ _ := by
    gcongr
    calc
      _ ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊, e₁ p := by
        unfold e₁
        rw [← sum_filter, ← primesLE_eq_filter_Ioc_zero, sum_comm]
        gcongr with p hp
        simp_rw [← mul_one_div (log p), cast_pow, ← one_div_pow, ← mul_sum]
        rw [primesLE_eq_filter_Ioc_zero, mem_filter, mem_Ioc] at hp
        gcongr
        grw [← Ico_add_one_add_one_eq_Ioc, geom_sum_Ico_le_of_lt_one (by simp)]
        · have : 0 < (p : ℝ) := mod_cast hp.1.1.pos
          norm_num; field_simp; simp
        · simpa using inv_lt_one_of_one_lt₀ (mod_cast hp.2.one_lt)
      _ ≤ _ := e₁_summable.sum_le_tsum _ fun p _ ↦ e₁_nonneg p

/-- The von Mangoldt weight `f : ℕ → ℝ := fun n ↦ Λ n / n`. -/
@[reducible]
noncomputable def Weight.vonMangoldt : Weight := {
  f := vonMangoldtFun
  map_zero' := by simp [vonMangoldtFun]
  map_one' := by simp [vonMangoldtFun]
  lowerBound := -2
  upperBound := log 4 + 1
  le_first' x hx := by
    suffices x * (log x - 2) ≤ x * ∑ n ∈ Ioc 0 ⌊x⌋₊, vonMangoldtFun n by
      linarith [le_of_mul_le_mul_left this (by linarith)]
    grw [← le_mul_sum_vonMangoldt (by linarith), ← le_sum_log' hx]
    grind [Real.log_le_self]
  first_le' x hx := by
    unfold vonMangoldtFun
    grind [sum_prime_le, E₁_le, sum_vonMangoldt_le_sum_prime_add_E₁, sum_prime_eq']
  C₀ := 1
  f_bound n := by
    unfold vonMangoldtFun
    grw [abs_of_nonneg (by positivity), one_mul, vonMangoldt_le_log]
}

@[simp]
lemma Weight.vonMangoldt_C₁_eq : vonMangoldt.C₁ = log 4 + 1 := by
  simp [C₁]; linarith [log_four_eq, log_two_gt_d9]

@[simp]
lemma Weight.vonMangoldt_C₂_eq : vonMangoldt.C₂ = log 4 + 3 := by grind [C₂]

/-- The Meissel--Mertens constant for the von Mangoldt weight simplifies to the
Euler--Mascheroni constant. -/
@[simp]
lemma Weight.vonMangoldt_M_eq : vonMangoldt.M = eulerMascheroniConstant := by
  rw [← sub_eq_zero]
  apply tendsto_nhds_unique vonMangoldt.sum_div_log_mul_pow_add_tendsto
  have := log_riemannZeta_add_log_sub_isLittleO_ofReal
  rw [isLittleO_one_iff] at this
  refine tendsto_nhdsWithin_congr (fun s hs ↦ ?_) this
  rw [log_riemannZeta_eq hs]
  congr! 3 with n
  rcases eq_or_ne 0 n with rfl | h <;> simp
  field_simp
  rw [mul_comm, ← mul_assoc, ← rpow_add (mod_cast (by omega))]
  simp [vonMangoldtFun]
  field_simp

/-- The prime weight `f : ℕ → ℝ := fun n ↦ 1 / n` if `n` is prime and `0` otherwise. -/
@[reducible]
noncomputable def Weight.prime : Weight := {
  f := primeFun
  map_zero' := by simp [primeFun]
  map_one' := by simp [primeFun]
  lowerBound := -3
  upperBound := log 4
  le_first' x hx := by
    have : -2 ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n - log x := Weight.vonMangoldt.le_first' x hx
    grind [E₁_le, sum_vonMangoldt_le_sum_prime_add_E₁, sum_prime_eq']
  first_le' x hx := by linarith [sum_prime_le hx]
  C₀ := 1
  f_bound n := by
    unfold primeFun
    split_ifs
    · rw [abs_of_nonneg, one_mul]; positivity
    · rw [abs_zero]; positivity
}

lemma sum_prime_eq : ∑ n ∈ Ioc 0 N, Weight.prime n = ∑ p ∈ primesLE N, log p / p :=
  sum_prime_eq' N

@[simp]
lemma Weight.prime_C₁_eq : prime.C₁ = 3 := by simp [C₁]; linarith [log_four_eq, log_two_lt_d9]

@[simp]
lemma Weight.prime_C₂_eq : prime.C₂ = log 4 + 3 := by simp [C₂]

lemma neg_inv_sub_log_sub_inv_eq (p : Primes) : - (1 / p + log (1 - 1 / p))
    = ∑' (k : ℕ), 1 / ((↑k + 2) * (p : ℝ) ^ ((k + 2))) := by
  symm; apply HasSum.tsum_eq
  let c : ℕ → ℝ := fun k ↦ 1 / ((↑k + 1) * (p : ℝ) ^ ((k + 1)))
  suffices HasSum (fun k ↦ c (k + 1)) (- (1 / p + log (1 - 1 / p))) by
    convert this using 2; unfold c; norm_cast
  rw [hasSum_nat_add_iff 1]
  have : 1 < (p : ℝ) := mod_cast p.prop.one_lt
  convert! (1 / (p : ℝ)).hasSum_pow_div_log_of_abs_lt_one
      (by grw [abs_of_pos (by positivity), ← this, div_one]) using 1
  <;> simp +contextual [c, division_def]

lemma tsum_inv_mul_pow_le {s : ℝ} (hs : 1 ≤ s) (p : Primes) :
    ∑' (k : ℕ), 1 / ((↑k + 2) * (p : ℝ) ^ ((↑k + 2) * s)) ≤ 1 / p ^ 2 := by
  have h0 : 0 < (p : ℝ) := mod_cast p.prop.pos
  have h2 : 2 ≤ (p : ℝ) := mod_cast p.prop.two_le
  refine tsum_le_of_sum_range_le (by intro; positivity) fun N ↦ ?_
  grw [← hs]
  · simp_rw [mul_one, rpow_add h0, rpow_ofNat, one_div, mul_inv_rev, mul_assoc, ← mul_sum]
    apply mul_le_of_le_one_right (by positivity)
    calc
      _ ≤ ∑ n ∈ range N, (1 - (2 : ℝ)⁻¹) * ((2 : ℝ)⁻¹) ^ n := by
        apply sum_le_sum; intros
        grw [← h2, inv_pow, rpow_natCast]
        field_simp; grind
      _ ≤ _ := by rw [← mul_sum, mul_neg_geom_sum, sub_le_self_iff]; positivity
  · linarith

/-- The standard formula for the Meissel-Mertens constant. -/
theorem Weight.prime_M_eq : prime.M = eulerMascheroniConstant
  + ∑' p : Primes, (log (1 - 1 / p) + 1 / p) := by
  rw [← sub_eq_iff_eq_add']
  apply tendsto_nhds_unique prime.sum_div_log_mul_pow_add_tendsto
  have h := log_riemannZeta_add_log_sub_isLittleO_ofReal
  rw [isLittleO_one_iff] at h
  suffices Tendsto (fun s : ℝ ↦ ∑' (p : Primes) (k : ℕ), 1 / ((k + 2) * (p : ℝ) ^ ((k + 2) * s)))
    (𝓝[>] 1) (𝓝 (∑' p : Primes, - (1 / p + log (1 - 1 / p)))) by
    convert tendsto_nhdsWithin_congr (fun s hs ↦ ?_) (h.sub this)
    · grind [tsum_neg]
    rw [log_riemannZeta_eq hs]
    nth_rw 1 [tsum_eq_tsum_primes_add_tsum_primes_of_support_subset_prime_powers]
    · have : ∑' p : Primes, Λ p / (p ^ s * log p)
          = ∑' n : ℕ, (log n)⁻¹ * prime n * (n : ℝ) ^ (1 - s) := by
        rw [Primes.tsum_eq_tsum_ite (fun p ↦ Λ p / (p ^ s * log p))]
        refine tsum_congr fun n ↦ ?_
        split_ifs with h <;> simp [vonMangoldt_apply_prime, primeFun, h]
        have := h.pos
        have := h.log_pos
        field_simp (disch := positivity)
        rw [← rpow_add (by positivity)]
        simp
      have :  ∑' (p : Primes) (k : ℕ),
          Λ (p ^ (k + 2)) / ((p ^ (k + 2) : ℕ) ^ s * log (p ^ (k + 2) : ℕ))
          = ∑' (p : Primes) (k : ℕ), 1 / ((k + 2) * (p : ℝ) ^ ((k + 2 : ℝ) * s)) := by
        refine tsum_congr fun p ↦ tsum_congr fun k ↦ ?_
        simp [ArithmeticFunction.vonMangoldt, p.prop.isPrimePow.pow, p.prop.pow_minFac]
        have : 0 < log p := p.prop.log_pos
        field_simp (disch := positivity)
        rw [rpow_mul (by positivity)]
        norm_cast
      linarith
    · apply (summable_one_div_nat_rpow.mpr hs).of_norm_bounded
      intro n
      rcases (by omega : n = 0 ∨ n = 1 ∨ 1 < n) with rfl | rfl | h
      · simp [zero_rpow_nonneg]
      · simp
      · have : 0 < log n := log_pos (mod_cast h)
        grw [norm_eq_abs, abs_div, abs_mul, vonMangoldt_le_log]
        field_simp
        apply le_abs_self
    · intro; simp +contextual [vonMangoldt_ne_zero_iff]
  apply tendsto_tsum_of_dominated_convergence ((summable_one_div_nat_pow.mpr one_lt_two).subtype _)
  · intro p
    rw [neg_inv_sub_log_sub_inv_eq p]
    have : 1 ≤ (p : ℝ) := mod_cast p.prop.one_le
    have : 2 ≤ (p : ℝ) := mod_cast p.prop.two_le
    apply tendsto_tsum_of_dominated_convergence summable_geometric_two
    · intro k
      convert! tendsto_const_nhds.div (b := (k + 2) * (p : ℝ) ^ (k + 2))
        (Tendsto.mono_left _ nhdsWithin_le_nhds) (by positivity) using 1
      have : Continuous (fun s : ℝ ↦ (k + 2) * (p : ℝ) ^ ((k + 2) * s)) := by
        fun_prop (disch := positivity)
      convert this.tendsto 1
      norm_cast; simp
    · filter_upwards [eventually_mem_nhdsWithin] with s (hs : 1 < s)
      intro
      grw [norm_eq_abs, abs_of_nonneg (by positivity), ← hs, ← this, one_div_pow]
      norm_cast; gcongr; grind
  · filter_upwards [eventually_mem_nhdsWithin] with s (hs : 1 < s)
    intro p
    rw [norm_eq_abs, abs_of_nonneg (by positivity)]
    exact tsum_inv_mul_pow_le hs.le p

end ConstructWeights

end Mertens
