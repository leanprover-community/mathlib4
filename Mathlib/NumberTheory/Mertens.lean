/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alastair Irving, Pietro Monticone, Terence Tao
-/
module

public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.NumberTheory.Chebyshev

/-!
# Mertens theorems

This file establishes the Mertens theorems that estimate sums and products involving primes
or the von Mangoldt function.

## Main definitions

- `E₁Λ`: The error `∑ d ∈ Ioc 0 ⌊x⌋₊, (Λ d) / d - log x` in the von Mangoldt form
of Mertens' first theorem.
- `E₁p`: The error `∑ p ∈ primesLE ⌊x⌋₊, (log p) / p - log x` in the prime form of Mertens' first
theorem.

## Main results

- Mertens' first theorem: both `E₁Λ` and `E₁p` are bounded in magnitude.  In fact we obtain
the explicit upper bound of  `log 4 + 4`.

## TODO

Add Mertens' second and third theorems.

## References

Parts of this file were upstreamed from the PrimeNumberTheoremAnd project by Kontorovich et al,
https://github.com/alexKontorovich/PrimeNumberTheoremAnd.

-/

@[expose] public section

namespace Mertens

open Nat hiding log
open Finset Filter Real Chebyshev intervalIntegral Asymptotics MeasureTheory
open ArithmeticFunction hiding log
open scoped Nat.Prime

/-!
## Bounds on the partial sum of the logarithm

The partial sum of the logarithm can also be expressed as the logarithm of the factorial, as well
as a sum involving the von Mangoldt function.  Here we state these identities and also provide
some upper and lower bounds on the partial sum of `log n`.

TODO: add sharper bounds arising from the Euler-Maclaurin formula.

-/

/-- The partial sum of the logarithm is equal to the log of the factorial. -/
theorem sum_log_eq_log_factorial (N : ℕ) :
    ∑ n ∈ Ioc 0 N, log n = log N.factorial := by
  rw [← prod_Ico_id_eq_factorial, ← log_prod (by intros; simp; grind), prod_natCast]
  rfl

/-- The partial sum of the logarithm is equal to a weighted sum of the von Mangoldt function. -/
theorem sum_log_eq_sum_mangoldt {x : ℝ} :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
  have : ∀ n : ℕ, log n = (Λ * zeta) n := by simp [vonMangoldt_mul_zeta]
  simp_rw [this, sum_Ioc_mul_zeta_eq_sum, ← floor_div_natCast]

/-- A crude upper bound on the partial sum of the logarithm. -/
theorem sum_log_le {x : ℝ} (hx : 1 ≤ x) : ∑ n ∈ Ioc 0 ⌊x⌋₊, log n ≤ x * log x := calc
  _ ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, log x := by
    refine sum_le_sum fun n hn ↦ ?_
    simp only [mem_Ioc] at hn
    exact log_le_log (by exact_mod_cast hn.1) (le_floor_iff (by linarith)|>.mp hn.2)
  _ = ⌊x⌋₊ * log x := by simp
  _ ≤ _ := by
    gcongr
    · exact log_nonneg hx
    · exact floor_le (by linarith)

private lemma integral_log_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, log t ≤ log b * (b - a) := by
  apply le_of_abs_le
  have : ∀ t ∈ Set.uIoc a b, ‖log t‖ ≤ log b := by
    intro t ht
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at ht
    rw [norm_of_nonneg <| log_nonneg (by linarith)]
    gcongr <;> linarith
  grw [← norm_eq_abs, norm_integral_le_of_norm_le_const this, abs_of_nonneg (by linarith)]

/-- A crude lower bound on the partial sum of the logarithm. -/
theorem le_sum_log {x : ℝ} (hx : 1 ≤ x) :
    x * log x - 2 * x ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, log n := by
  have one_le_floor : 1 ≤ ⌊x⌋₊ := by simpa
  rw [←ge_iff_le]
  calc
  _ = ∑ n ∈ Icc 1 ⌊x⌋₊, log n := by rfl
  _ = ∑ n ∈ Ico (1 + 1) (⌊x⌋₊ + 1), log n := by simp [← add_sum_Ioc_eq_sum_Icc one_le_floor]; rfl
  _ = ∑ n ∈ Ico 1 ⌊x⌋₊, log ((n + 1 : ℕ)) := by rw [← sum_Ico_add']
  _ ≥ ∫ t in 1..⌊x⌋₊, log t := by
    convert MonotoneOn.integral_le_sum_Ico one_le_floor ?_|>.ge
    · norm_cast
    · exact (strictMonoOn_log.mono fun _ _ ↦ by simp_all; linarith).monotoneOn
  _ = (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log t := by
    nth_rw 3 [integral_symm]
    rw [sub_neg_eq_add, integral_add_adjacent_intervals] <;> exact intervalIntegrable_log'
  _ ≥ (∫ t in 1..x, log t) - log x := by
    gcongr
    grw [integral_log_le (by simpa) (floor_le (by linarith))]
    nth_rw 2 [← mul_one (log x)]
    gcongr
    · exact log_nonneg hx
    · linarith [lt_floor_add_one x]
  _ ≥ _ := by simp; linarith [log_le_self (by linarith : 0 ≤ x)]

section FirstTheorem

/-!
## Mertens' first theorem

Mertens' first theorem can be formulated in terms of two error terms:

* `E₁Λ x = ∑ d ∈ Ioc 0 ⌊x⌋₊, (Λ d) / d - log x` (von Mangoldt error).  We bound this
error between `-2` and `log 4 + 4`.
* `E₁p x = ∑ p ∈ primesLE ⌊x⌋₊, (log p) / p - log x` (prime error). We bound this error
in magnitude by `log 4 + 4`.

-/

variable (x : ℝ)

/-- The error term in the von Mangoldt form of Mertens' first theorem. -/
noncomputable def E₁Λ : ℝ := ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d - log x

theorem sum_mangoldt_div_eq : ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d = log x + E₁Λ x := by simp [E₁Λ]

theorem le_E₁Λ {x : ℝ} (hx : 1 ≤ x) : -2 ≤ E₁Λ x := by
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≥ x * (log x - 2) by
    unfold E₁Λ
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by rw [mul_sum]; ring_nf
  _ ≥ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
    gcongr
    · exact vonMangoldt_nonneg
    · exact floor_le <| div_nonneg (by linarith) (by linarith)
  _ ≥ x * log x - 2 * x := sum_log_eq_sum_mangoldt ▸ le_sum_log hx
  _ = _ := by ring

theorem E₁Λ_le {x : ℝ} (hx : 1 ≤ x) : E₁Λ x ≤ log 4 + 4 := by
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ x * (log x + log 4 + 4) by
    unfold E₁Λ
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by rw [mul_sum]; ring_nf
  _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (⌊x / d⌋₊ + 1) := by
    gcongr
    · exact vonMangoldt_nonneg
    · exact lt_floor_add_one _|>.le
  _ = (∑ d ∈ Ioc 0 ⌊x⌋₊, log d) + psi x := by
    simp_rw [psi, mul_add, mul_one, sum_add_distrib, sum_log_eq_sum_mangoldt]
  _ ≤ x * log x + (log 4 + 4) * x := by grw [← sum_log_le hx, psi_le_const_mul_self (by linarith)]
  _ = _ := by ring

theorem sum_mangoldt_div_sub_log_bound {x : ℝ} (hx : 1 ≤ x) :
    |∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d - log x| ≤ log 4 + 4 := by
  grind [E₁Λ_le hx, le_E₁Λ hx, log_nonneg, sum_mangoldt_div_eq]

theorem E₁Λ_bounded' : ∃ c > 0, ∀ x ≥ 1, |E₁Λ x| ≤ c :=
  ⟨log 4 + 4, by positivity, fun x hx ↦ sum_mangoldt_div_sub_log_bound hx⟩

theorem E₁Λ_bounded : E₁Λ =O[atTop] (fun _ ↦ (1 : ℝ)) := by
  simp only [isBigO_iff, norm_eq_abs, norm_one, mul_one, eventually_atTop]
  exact ⟨log 4 + 4, 1, fun _ hx ↦ sum_mangoldt_div_sub_log_bound hx⟩

theorem sum_mangoldt_div_sim_log :
    (∑ d ∈ Ioc 0 ⌊·⌋₊, Λ d / d) ~[atTop] log :=
  (E₁Λ_bounded.trans_isLittleO (isLittleO_const_log_atTop (c := 1))).isEquivalent

/-- The error term in the von Mangoldt form of Mertens' first theorem. -/
noncomputable def E₁p : ℝ := ∑ p ∈ primesLE ⌊x⌋₊, log p / p - log x

theorem sum_log_prime_div_eq : ∑ p ∈ primesLE ⌊x⌋₊, log p / p = log x + E₁p x := by simp [E₁p]

theorem E₁p_le_E₁Λ : E₁p x ≤ E₁Λ x := by
  unfold E₁p E₁Λ; rw [primesLE_eq_filter_Ioc_zero, sum_filter]
  gcongr with p _
  split_ifs with hp
  · simp [vonMangoldt_apply_prime hp]
  have : 0 ≤ Λ p := vonMangoldt_nonneg
  positivity

theorem E₁p_le {x : ℝ} (hx : 1 ≤ x) : E₁p x ≤ log 4 + 4 := by linarith [E₁Λ_le hx, E₁p_le_E₁Λ x]

/-- The summand defining the constant `E₁` below. -/
noncomputable def e₁ : ℕ → ℝ := fun p ↦ if p.Prime then log p / (p * (p - 1)) else 0

/-- The constant `E₁ = 0.755366...` (https://oeis.org/A138312) is defined as the sum of
`log p / (p * (p-1))` over primes `p`. -/
noncomputable def E₁ : ℝ := ∑' p : ℕ, e₁ p

lemma e₁_nonneg (p : ℕ) : 0 ≤ e₁ p := by
  unfold e₁
  split_ifs with h
  · have : 1 ≤ (p : ℝ) := mod_cast h.one_le
    positivity
  rfl

theorem E₁_summable : Summable e₁ := by
  refine (summable_one_div_nat_rpow.mpr (by norm_num : 1 < (3 : ℝ) / 2) |>.const_div
    4).of_nonneg_of_le e₁_nonneg fun p ↦ ?_
  unfold e₁
  split_ifs with h
  · have : 2 ≤ (p : ℝ) := mod_cast h.two_le
    have denom : (p : ℝ) * ((p : ℝ) - 1) ≥ p ^ 2 / 2 := by
      rw [sq, mul_div_assoc]; gcongr; linarith
    grw [log_le_rpow_div (cast_nonneg _) (by norm_num : 0 < (1 : ℝ) / 2), denom]
    · apply le_of_eq
      rw [← Real.rpow_natCast]
      field_simp
      rw [mul_assoc, ← Real.rpow_add (by positivity)]
      grind
    exact mul_nonneg (by linarith) (by linarith)
  · positivity

private lemma antitoneOn_log_div_sq : AntitoneOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (.Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp at ht
    have : (t + 2) ≠ 0 := by simp; linarith
    fun_prop (disch := grind)
  · refine fun t ht ↦ DifferentiableAt.differentiableWithinAt ?_
    simp at ht
    have : (t + 2) ^ 2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · intro t ht
    simp at ht
    rw [deriv_fun_div (by fun_prop (disch := grind)) (by fun_prop) (by simp; grind),
      deriv_comp_add_const, deriv_log]
    simp
    field_simp
    rw [mul_zero, tsub_le_iff_right, zero_add, ← log_rpow (by linarith), ← log_exp 1, rpow_ofNat]
    gcongr
    nlinarith [exp_one_lt_three]

private lemma log_div_sq_nonneg : ∀ t ∈ Set.Ioi 0, 0 ≤ log (t + 2) / (t + 2) ^ 2 :=
  fun t ht ↦ div_nonneg (log_nonneg (by simp_all; linarith)) (by positivity)

private lemma log_div_sq_is_deriv : ∀ x ∈ Set.Ici 0,
    HasDerivAt (fun t ↦ (-log (t + 2) - 1) / (t + 2)) (log (x + 2) / (x + 2) ^ 2) x := by
  intro t ht
  simp at ht
  apply HasDerivAt.comp_add_const (f := (fun t ↦ (-log t - 1)/ t)) t 2
  convert! HasDerivAt.fun_div (c' := -1 / (t + 2)) (d' := (1 : ℝ)) _ _  _ using 1
  · field
  · apply HasDerivAt.sub_const
    convert (hasDerivAt_log (by linarith : t + 2 ≠ 0)).neg using 1
    · aesop
    ring_nf
  · exact hasDerivAt_id _
  · linarith

private lemma tendsto_antideriv_log_div_sq :
  atTop.Tendsto (fun t ↦ (-log (t + 2) - 1) / (t + 2)) (nhds 0) := by
  have : atTop.Tendsto (fun (t : ℝ) ↦ t + 2) atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_id
  apply Tendsto.comp (g := (fun t ↦ (-log t - 1) / t)) _ this
  convert Tendsto.sub (f := (fun t ↦ -log t / t)) (a := 0) _ tendsto_inv_atTop_zero using 1
  · ring_nf
  · ring_nf
  · convert (tendsto_pow_log_div_mul_add_atTop 1 0 1 (by linarith)).neg using 1
    · ext; ring
    · simp

private lemma integrableOn_log_div_sq : IntegrableOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (.Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg
    tendsto_antideriv_log_div_sq

private lemma integral_log_div_sq : ∫ t in .Ioi 0, log (t + 2) / (t + 2) ^ 2 = (log 2 + 1) / 2
    := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg
    tendsto_antideriv_log_div_sq]
  ring_nf

private lemma summable_log_div_sq : Summable (fun (n : ℕ) ↦ log (n + 3) / (n + 3) ^ 2) := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  suffices Summable (fun (n : ℕ) ↦ g n ) by
    convert! summable_nat_add_iff 1|>.mpr this using 2
    simp [g]; ring_nf
  exact antitoneOn_log_div_sq.summable_of_integrable integrableOn_log_div_sq log_div_sq_nonneg

private lemma sum_log_div_sq_le :
    ∑' (n : ℕ), log (n + 3) / (n + 3) ^ 2 ≤ (log 2 + 1) / 2 := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  calc
  _ = ∑' (n : ℕ), g (n + 1 : ℕ) := by simp [g]; ring_nf
  _ ≤ ∫ x in .Ioi 0, g x :=
    antitoneOn_log_div_sq.tsum_add_one_le_integral integrableOn_log_div_sq log_div_sq_nonneg
  _ = _ := integral_log_div_sq

/-- A crude upper bound of 1.6164... for `E₁`. -/
theorem E₁_le : E₁ ≤ (5 * log 2 + 3) / 4 := by
  unfold E₁
  calc
  _ = log 2 / 2 + ∑' (n : ℕ), if (n + 3).Prime then log (n + 3) / ((n + 3) * (n + 2)) else 0 := by
    rw [← E₁_summable.sum_add_tsum_nat_add 3, (by rfl : range 3 = {0, 1, 2})]
    simp [e₁, Nat.prime_two]
    ring_nf
  _ ≤ log 2 / 2 + ∑' (n : ℕ), (3 / 2) * (log (n + 3) / (n + 3) ^ 2) := by
    gcongr with n
    · convert! summable_nat_add_iff 3|>.mpr E₁_summable using 4
      simp [e₁]; ring_nf
    · exact summable_log_div_sq.mul_left _
    · split_ifs with h
      · grw [(by linarith : (n + 2 : ℝ) ≥ 2 * (n + 3) / 3)]
        · field_simp; rfl
        · exact log_nonneg (by grind)
      · exact mul_nonneg (by norm_num) (div_nonneg (log_nonneg (by grind)) (by positivity))
  _ ≤ _ := by grw [tsum_mul_left, sum_log_div_sq_le]; ring_nf; rfl

theorem E₁_nonneg : 0 ≤ E₁ := tsum_nonneg e₁_nonneg

theorem E₁Λ_le_E₁p_add_E₁ {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ E₁p x + E₁ := by
  unfold E₁Λ E₁p
  suffices ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ ∑ p ∈ primesLE ⌊x⌋₊, log p / p + E₁ by linarith
  simp_rw [vonMangoldt_apply, ite_div, zero_div, ← sum_filter, sum_PrimePow_eq_sum_sum _
    (by linarith)]
  calc
  _ = ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ primesLE ⌊x ^ (1 / (k : ℝ))⌋₊, log p / (p ^ k : ℕ) := by
    simp only [primesLE_eq_filter_Ioc_zero]
    refine sum_congr rfl fun k hk ↦ sum_congr rfl fun p hp ↦ ?_
    rw [Prime.pow_minFac (by simp_all) (by simp_all; linarith)]
  _ ≤ ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ primesLE ⌊x⌋₊, log p / (p ^ k : ℕ) := by
    simp only [primesLE_eq_filter_Ioc_zero]
    gcongr with k hk
    apply rpow_le_self_of_one_le hx
    simp only [mem_Icc] at hk
    exact div_le_one₀ (by norm_cast; linarith)|>.mpr (mod_cast hk.1)
  _ ≤ ∑ k ∈ Icc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ primesLE ⌊x⌋₊, log p / (p ^ k : ℕ) := by
    apply sum_le_sum_of_subset_of_nonneg
    · gcongr
      exact le_max_right ..
    · exact fun _ _ _ ↦ sum_nonneg fun _ _ ↦ (by positivity)
  _ = ∑ p ∈ primesLE ⌊x⌋₊, log p / p +
    ∑ k ∈ Ioc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ primesLE ⌊x⌋₊, log p / (p ^ k : ℕ) := by
    rw [← add_sum_Ioc_eq_sum_Icc (le_max_left ..)]
    simp
  _ ≤ _ := by
    gcongr
    rw [sum_comm]
    conv => lhs; arg 2; ext p; arg 2; ext k; rw [← mul_one_div, cast_pow, ← one_div_pow]
    simp_rw [← mul_sum]
    calc
    _ ≤ ∑ p ∈ primesLE ⌊x⌋₊, log p / (p * (p - 1)) := by
      gcongr with p hp
      simp only [primesLE_eq_filter_Ioc_zero, mem_filter, mem_Ioc] at hp
      conv => rhs; rw [← mul_one_div]
      gcongr
      rw [(by rfl : Ioc 1 (max 1 ⌊log x / log 2⌋₊) = Ico 2 (max 1 ⌊log x / log 2⌋₊  + 1))]
      grw [geom_sum_Ico_le_of_lt_one (by simp)]
      · apply le_of_eq
        have : (p : ℝ) ≠ 0 := mod_cast hp.1.1.ne.symm
        field
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast hp.2.one_lt)
    _ ≤ _ := by
      rw [primesLE_eq_filter_Ioc_zero, sum_filter]
      exact E₁_summable.sum_le_tsum _ fun p hp ↦ e₁_nonneg p

theorem le_E₁p {x : ℝ} (hx : 1 ≤ x) : -2 - E₁ ≤ E₁p x := by
  linarith [E₁Λ_le_E₁p_add_E₁ hx, le_E₁Λ hx]

theorem sum_log_prime_div_sub_log_bound {x : ℝ} (hx : 1 ≤ x) :
    |∑ p ∈ primesLE ⌊x⌋₊, log p / p - log x| ≤ log 4 + 4 := by
  refine abs_le'.mpr ⟨E₁p_le hx, ?_⟩
  have : log 2 > 0 := by positivity
  have : log 4 = 2 * log 2 := by rw [← log_rpow (by norm_num)]; norm_num
  grind [le_E₁p hx, E₁_le, sum_log_prime_div_eq]

theorem E₁p.bounded : ∃ c > 0, ∀ x ≥ 1, |E₁p x| ≤ c :=
  ⟨log 4 + 4, by positivity, fun _ hx ↦ sum_log_prime_div_sub_log_bound hx⟩

theorem sum_log_prime_div_eq_log_add_bounded : E₁p =O[atTop] (fun _ ↦ (1 : ℝ)) := by
  simp only [isBigO_iff, norm_eq_abs, norm_one, mul_one, eventually_atTop, E₁p]
  exact ⟨log 4 + 4, 1, fun _ ↦ sum_log_prime_div_sub_log_bound⟩

theorem sum_log_prime_div_sim_log : (fun x ↦ ∑ p ∈ primesLE ⌊x⌋₊, log p / p)
    ~[atTop] log := by
  apply IsLittleO.isEquivalent (IsBigO.trans_isLittleO _ (isLittleO_const_log_atTop (c := 1)))
  convert! sum_log_prime_div_eq_log_add_bounded using 1

end FirstTheorem

end Mertens
