/-
Copyright (c) 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching, Fabian Kruse, Nikolas Kuhn
-/
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Tactic.AdaptationNote

/-!
# Stirling's formula

This file proves Stirling's formula for the factorial.
It states that $n!$ grows asymptotically like $\sqrt{2\pi n}(\frac{n}{e})^n$.

Also some _global_ bounds on the factorial function and the Stirling sequence are proved.

## Proof outline

The proof follows: <https://proofwiki.org/wiki/Stirling%27s_Formula>.

We proceed in two parts.

**Part 1**: We consider the sequence $a_n$ of fractions $\frac{n!}{\sqrt{2n}(\frac{n}{e})^n}$
and prove that this sequence converges to a real, positive number $a$. For this the two main
ingredients are
- taking the logarithm of the sequence and
- using the series expansion of $\log(1 + x)$.

**Part 2**: We use the fact that the series defined in part 1 converges against a real number $a$
and prove that $a = \sqrt{\pi}$. Here the main ingredient is the convergence of Wallis' product
formula for `π`.
-/


open scoped Topology Real Nat Asymptotics

open Nat hiding log log_pow
open Finset Filter Real

namespace Stirling

/-!
### Part 1
https://proofwiki.org/wiki/Stirling%27s_Formula#Part_1
-/


/-- Define `stirlingSeq n` as $\frac{n!}{\sqrt{2n}(\frac{n}{e})^n}$.
Stirling's formula states that this sequence has limit $\sqrt(π)$.
-/
noncomputable def stirlingSeq (n : ℕ) : ℝ :=
  n ! / (√(2 * n : ℝ) * (n / exp 1) ^ n)

@[simp]
theorem stirlingSeq_zero : stirlingSeq 0 = 0 := by
  rw [stirlingSeq, cast_zero, mul_zero, Real.sqrt_zero, zero_mul, div_zero]

@[simp]
theorem stirlingSeq_one : stirlingSeq 1 = exp 1 / √2 := by
  rw [stirlingSeq, pow_one, factorial_one, cast_one, mul_one, mul_one_div, one_div_div]

theorem log_stirlingSeq_formula (n : ℕ) :
    log (stirlingSeq n) = Real.log n ! - 1 / 2 * Real.log (2 * n) - n * log (n / exp 1) := by
  cases n
  · simp
  · rw [stirlingSeq, log_div, log_mul, sqrt_eq_rpow, log_rpow, Real.log_pow, tsub_tsub]
      <;> positivity

/-- The sequence `log (stirlingSeq (m + 1)) - log (stirlingSeq (m + 2))` has the series expansion
`∑ 1 / (2 * (k + 1) + 1) * (1 / 2 * (m + 1) + 1)^(2 * (k + 1))`. -/
theorem log_stirlingSeq_diff_hasSum (m : ℕ) :
    HasSum (fun k : ℕ => (1 : ℝ) / (2 * ↑(k + 1) + 1) * ((1 / (2 * ↑(m + 1) + 1)) ^ 2) ^ ↑(k + 1))
      (log (stirlingSeq (m + 1)) - log (stirlingSeq (m + 2))) := by
  let f (k : ℕ) := (1 : ℝ) / (2 * k + 1) * ((1 / (2 * ↑(m + 1) + 1)) ^ 2) ^ k
  change HasSum (fun k => f (k + 1)) _
  rw [hasSum_nat_add_iff]
  convert (hasSum_log_one_add_inv m.cast_add_one_pos).mul_left ((↑(m + 1) : ℝ) + 1 / 2) using 1
  · ext k
    dsimp only [f]
    rw [← pow_mul, pow_add]
    push_cast
    field_simp
  · have h (x) (hx : x ≠ (0 : ℝ)) : 1 + x⁻¹ = (x + 1) / x := by field_simp
    simp (disch := positivity) only [log_stirlingSeq_formula, log_div, log_mul, log_exp,
      factorial_succ, cast_mul, cast_succ, range_one, sum_singleton, h]
    ring

/-- The sequence `log ∘ stirlingSeq ∘ succ` is monotone decreasing -/
theorem log_stirlingSeq'_antitone : Antitone (Real.log ∘ stirlingSeq ∘ succ) :=
  antitone_nat_of_succ_le fun n =>
    sub_nonneg.mp <| (log_stirlingSeq_diff_hasSum n).nonneg fun m => by positivity

/-- We have a bound for successive elements in the sequence `log (stirlingSeq k)`.
-/
theorem log_stirlingSeq_diff_le_geo_sum (n : ℕ) :
    log (stirlingSeq (n + 1)) - log (stirlingSeq (n + 2)) ≤
      ((1 : ℝ) / (2 * ↑(n + 1) + 1)) ^ 2 / (1 - ((1 : ℝ) / (2 * ↑(n + 1) + 1)) ^ 2) := by
  have h_nonneg : (0 : ℝ) ≤ ((1 : ℝ) / (2 * ↑(n + 1) + 1)) ^ 2 := sq_nonneg _
  have g : HasSum (fun k : ℕ => (((1 : ℝ) / (2 * ↑(n + 1) + 1)) ^ 2) ^ ↑(k + 1))
      (((1 : ℝ) / (2 * ↑(n + 1) + 1)) ^ 2 / (1 - ((1 : ℝ) / (2 * ↑(n + 1) + 1)) ^ 2)) := by
    have := (hasSum_geometric_of_lt_one h_nonneg ?_).mul_left (((1 : ℝ) / (2 * ↑(n + 1) + 1)) ^ 2)
    · simp_rw [← _root_.pow_succ'] at this
      exact this
    rw [one_div, inv_pow]
    exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ (lt_add_of_pos_left _ <| by positivity) two_ne_zero)
  have hab (k : ℕ) : (1 : ℝ) / (2 * ↑(k + 1) + 1) * ((1 / (2 * ↑(n + 1) + 1)) ^ 2) ^ ↑(k + 1) ≤
      (((1 : ℝ) / (2 * ↑(n + 1) + 1)) ^ 2) ^ ↑(k + 1) := by
    refine mul_le_of_le_one_left (pow_nonneg h_nonneg ↑(k + 1)) ?_
    rw [one_div]
    exact inv_le_one_of_one_le₀ (le_add_of_nonneg_left <| by positivity)
  exact hasSum_le hab (log_stirlingSeq_diff_hasSum n) g

/-- We have the bound `log (stirlingSeq n) - log (stirlingSeq (n+1))` ≤ 1/(4 n^2)
-/
theorem log_stirlingSeq_sub_log_stirlingSeq_succ (n : ℕ) :
    log (stirlingSeq (n + 1)) - log (stirlingSeq (n + 2)) ≤ 1 / (4 * (↑(n + 1) : ℝ) ^ 2) := by
  have h₁ : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 * 4 := by positivity
  have h₃ : (0 : ℝ) < (2 * ((n : ℝ) + 1) + 1) ^ 2 - 1 := by
    ring_nf
    positivity
  refine (log_stirlingSeq_diff_le_geo_sum n).trans ?_
  push_cast
  field_simp
  ring_nf
  norm_cast
  cutsat

/-- For any `n`, we have `log_stirlingSeq 1 - log_stirlingSeq n ≤ 1/4 * ∑' 1/k^2` -/
theorem log_stirlingSeq_bounded_aux :
    ∃ c : ℝ, ∀ n : ℕ, log (stirlingSeq 1) - log (stirlingSeq (n + 1)) ≤ c := by
  let d : ℝ := ∑' k : ℕ, (1 : ℝ) / (↑(k + 1) : ℝ) ^ 2
  use 1 / 4 * d
  let log_stirlingSeq' : ℕ → ℝ := fun k => log (stirlingSeq (k + 1))
  intro n
  have h₁ k : log_stirlingSeq' k - log_stirlingSeq' (k + 1) ≤ 1 / 4 * (1 / (↑(k + 1) : ℝ) ^ 2) := by
    convert log_stirlingSeq_sub_log_stirlingSeq_succ k using 1; field_simp
  have h₂ : (∑ k ∈ range n, 1 / (↑(k + 1) : ℝ) ^ 2) ≤ d := by
    have := (summable_nat_add_iff 1).mpr <| Real.summable_one_div_nat_pow.mpr one_lt_two
    exact this.sum_le_tsum (range n) (fun k _ => by positivity)
  calc
    log (stirlingSeq 1) - log (stirlingSeq (n + 1)) = log_stirlingSeq' 0 - log_stirlingSeq' n :=
      rfl
    _ = ∑ k ∈ range n, (log_stirlingSeq' k - log_stirlingSeq' (k + 1)) := by
      rw [← sum_range_sub' log_stirlingSeq' n]
    _ ≤ ∑ k ∈ range n, 1 / 4 * (1 / ↑((k + 1)) ^ 2) := sum_le_sum fun k _ => h₁ k
    _ = 1 / 4 * ∑ k ∈ range n, 1 / ↑((k + 1)) ^ 2 := by rw [mul_sum]
    _ ≤ 1 / 4 * d := by gcongr

/-- The sequence `log_stirlingSeq` is bounded below for `n ≥ 1`. -/
theorem log_stirlingSeq_bounded_by_constant : ∃ c, ∀ n : ℕ, c ≤ log (stirlingSeq (n + 1)) := by
  obtain ⟨d, h⟩ := log_stirlingSeq_bounded_aux
  exact ⟨log (stirlingSeq 1) - d, fun n => sub_le_comm.mp (h n)⟩

/-- The sequence `stirlingSeq` is positive for `n > 0` -/
theorem stirlingSeq'_pos (n : ℕ) : 0 < stirlingSeq (n + 1) := by unfold stirlingSeq; positivity

/-- The sequence `stirlingSeq` has a positive lower bound.
-/
theorem stirlingSeq'_bounded_by_pos_constant : ∃ a, 0 < a ∧ ∀ n : ℕ, a ≤ stirlingSeq (n + 1) := by
  obtain ⟨c, h⟩ := log_stirlingSeq_bounded_by_constant
  refine ⟨exp c, exp_pos _, fun n => ?_⟩
  rw [← le_log_iff_exp_le (stirlingSeq'_pos n)]
  exact h n

/-- The sequence `stirlingSeq ∘ succ` is monotone decreasing -/
theorem stirlingSeq'_antitone : Antitone (stirlingSeq ∘ succ) := fun n m h =>
  (log_le_log_iff (stirlingSeq'_pos m) (stirlingSeq'_pos n)).mp (log_stirlingSeq'_antitone h)

/-- The limit `a` of the sequence `stirlingSeq` satisfies `0 < a` -/
theorem stirlingSeq_has_pos_limit_a : ∃ a : ℝ, 0 < a ∧ Tendsto stirlingSeq atTop (𝓝 a) := by
  obtain ⟨x, x_pos, hx⟩ := stirlingSeq'_bounded_by_pos_constant
  have hx' : x ∈ lowerBounds (Set.range (stirlingSeq ∘ succ)) := by simpa [lowerBounds] using hx
  refine ⟨_, lt_of_lt_of_le x_pos (le_csInf (Set.range_nonempty _) hx'), ?_⟩
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  exact tendsto_atTop_ciInf stirlingSeq'_antitone ⟨x, hx'⟩

/-!
### Part 2
https://proofwiki.org/wiki/Stirling%27s_Formula#Part_2
-/


/-- The sequence `n / (2 * n + 1)` tends to `1/2` -/
theorem tendsto_self_div_two_mul_self_add_one :
    Tendsto (fun n : ℕ => (n : ℝ) / (2 * n + 1)) atTop (𝓝 (1 / 2)) := by
  conv =>
    congr
    · skip
    · skip
    rw [one_div, ← add_zero (2 : ℝ)]
  refine (((tendsto_const_div_atTop_nhds_zero_nat 1).const_add (2 : ℝ)).inv₀
    ((add_zero (2 : ℝ)).symm ▸ two_ne_zero)).congr' (eventually_atTop.mpr ⟨1, fun n hn => ?_⟩)
  rw [add_div' (1 : ℝ) 2 n (cast_ne_zero.mpr (one_le_iff_ne_zero.mp hn)), inv_div]

/-- For any `n ≠ 0`, we have the identity
`(stirlingSeq n)^4 / (stirlingSeq (2*n))^2 * (n / (2 * n + 1)) = W n`, where `W n` is the
`n`-th partial product of Wallis' formula for `π / 2`. -/
theorem stirlingSeq_pow_four_div_stirlingSeq_pow_two_eq (n : ℕ) (hn : n ≠ 0) :
    stirlingSeq n ^ 4 / stirlingSeq (2 * n) ^ 2 * (n / (2 * n + 1)) = Wallis.W n := by
  have : 4 = 2 * 2 := by rfl
  rw [stirlingSeq, this, pow_mul, stirlingSeq, Wallis.W_eq_factorial_ratio]
  simp_rw [div_pow, mul_pow]
  rw [sq_sqrt, sq_sqrt]
  any_goals positivity
  simp [field, ← exp_nsmul]
  ring_nf

/-- Suppose the sequence `stirlingSeq` (defined above) has the limit `a ≠ 0`.
Then the Wallis sequence `W n` has limit `a^2 / 2`.
-/
theorem second_wallis_limit (a : ℝ) (hane : a ≠ 0) (ha : Tendsto stirlingSeq atTop (𝓝 a)) :
    Tendsto Wallis.W atTop (𝓝 (a ^ 2 / 2)) := by
  refine Tendsto.congr' (eventually_atTop.mpr ⟨1, fun n hn =>
    stirlingSeq_pow_four_div_stirlingSeq_pow_two_eq n (one_le_iff_ne_zero.mp hn)⟩) ?_
  have h : a ^ 2 / 2 = a ^ 4 / a ^ 2 * (1 / 2) := by
    rw [mul_one_div, ← mul_one_div (a ^ 4) (a ^ 2), one_div, ← pow_sub_of_lt a]
    simp
  rw [h]
  exact ((ha.pow 4).div ((ha.comp (tendsto_id.const_mul_atTop' two_pos)).pow 2)
    (pow_ne_zero 2 hane)).mul tendsto_self_div_two_mul_self_add_one

/-- **Stirling's Formula** -/
theorem tendsto_stirlingSeq_sqrt_pi : Tendsto stirlingSeq atTop (𝓝 (√π)) := by
  obtain ⟨a, hapos, halimit⟩ := stirlingSeq_has_pos_limit_a
  have hπ : π / 2 = a ^ 2 / 2 :=
    tendsto_nhds_unique Wallis.tendsto_W_nhds_pi_div_two (second_wallis_limit a hapos.ne' halimit)
  rwa [(div_left_inj' (two_ne_zero' ℝ)).mp hπ, sqrt_sq hapos.le]

/-- **Stirling's Formula**, formulated in terms of `Asymptotics.IsEquivalent`. -/
lemma factorial_isEquivalent_stirling :
    (fun n ↦ n ! : ℕ → ℝ) ~[atTop] fun n ↦ Real.sqrt (2 * n * π) * (n / exp 1) ^ n := by
  refine Asymptotics.isEquivalent_of_tendsto_one ?_ ?_
  · filter_upwards [eventually_ne_atTop 0] with n hn h
    exact absurd h (by positivity)
  · have : sqrt π ≠ 0 := by positivity
    nth_rewrite 2 [← div_self this]
    convert tendsto_stirlingSeq_sqrt_pi.div tendsto_const_nhds this using 1
    ext n
    simp [field, stirlingSeq, mul_right_comm]

/-! ### Global bounds -/

/--
The Stirling sequence is bounded below by `√π`, for all positive naturals. Note that this bound
holds for all `n > 0`, rather than for sufficiently large `n`: it is effective.
-/
theorem sqrt_pi_le_stirlingSeq {n : ℕ} (hn : n ≠ 0) : √π ≤ stirlingSeq n :=
  match n, hn with
  | n + 1, _ =>
    stirlingSeq'_antitone.le_of_tendsto (b := n) <|
      tendsto_stirlingSeq_sqrt_pi.comp (tendsto_add_atTop_nat 1)

/--
Stirling's approximation gives a lower bound for `n!` for all `n`.
The left-hand side is formulated to mimic the usual informal description of the approximation.
See also `factorial_isEquivalent_stirling` which says these are asymptotically equivalent. That
statement gives an upper bound also, but requires sufficiently large `n`. In contrast, this one is
only a lower bound, but holds for all `n`.
Sharper bounds due to Robbins are available, but are not yet formalised.
-/
theorem le_factorial_stirling (n : ℕ) : √(2 * π * n) * (n / exp 1) ^ n ≤ n ! := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  have : √(2 * π * n) * (n / exp 1) ^ n = √π * (√(2 * n) * (n / exp 1) ^ n) := by
    simp [sqrt_mul']; ring
  rw [this, ← le_div_iff₀ (by positivity)]
  exact sqrt_pi_le_stirlingSeq hn

/--
Stirling's approximation gives a lower bound for `log n!` for all positive `n`.
The left-hand side is formulated in decreasing order in `n`: the higher order terms are first.
This is a consequence of `le_factorial_stirling`, but is stated separately since the logarithmic
version is sometimes more practical, and having this version eases algebraic calculations for
applications.
Sharper bounds due to Robbins are available, but are not yet formalised. These would add
lower order terms (beginning with `(12 * n)⁻¹`) to the left-hand side.
-/
theorem le_log_factorial_stirling {n : ℕ} (hn : n ≠ 0) :
    n * log n - n + log n / 2 + log (2 * π) / 2 ≤ log n ! := by
  calc
    _ = (log (2 * π) + log n) / 2 + n * (log n - 1) := by ring
    _ = log (√(2 * π * n) * (n / rexp 1) ^ n) := by
      rw [log_mul (x := √_), log_sqrt, log_mul (x := 2 * π), log_pow, log_div, log_exp] <;>
      positivity
    _ ≤ _ := log_le_log (by positivity) (le_factorial_stirling n)

end Stirling
