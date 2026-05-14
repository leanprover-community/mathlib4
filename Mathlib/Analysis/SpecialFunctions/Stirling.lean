/-
Copyright (c) 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching, Fabian Kruse, Nikolas Kuhn
-/
module

public import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Torsion
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Field
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Neighborhoods

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

@[expose] public section


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
    field
  · have h (x) (hx : x ≠ (0 : ℝ)) : 1 + x⁻¹ = (x + 1) / x := by field
    simp (disch := positivity) only [log_stirlingSeq_formula, log_div, log_mul, log_exp,
      factorial_succ, cast_mul, cast_succ, range_one, sum_singleton, h]
    ring

/-- The sequence `log ∘ stirlingSeq ∘ succ` is monotone decreasing -/
theorem log_stirlingSeq'_antitone : Antitone (Real.log ∘ stirlingSeq ∘ succ) :=
  antitone_nat_of_succ_le fun n =>
    sub_nonneg.mp <| (log_stirlingSeq_diff_hasSum n).nonneg fun m => by positivity

/-- We have a bound for successive elements in the sequence `log (stirlingSeq k)`. -/
@[deprecated "Use `log_stirlingSeq_diff_le` instead." (since := "2026-03-16")]
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

/-- **Robbins' sharp stepwise bound** for the Stirling sequence:
`log (stirlingSeq n) - log (stirlingSeq (n+1)) ≤ 1 / (12 n (n + 1))`. -/
theorem log_stirlingSeq_diff_le (n : ℕ) :
    log (stirlingSeq n) - log (stirlingSeq (n + 1)) ≤ 1 / (12 * n * (n + 1)) := by
  rcases n with (_ | n)
  · suffices 0 ≤ Real.log (Real.exp 1 / Real.sqrt 2) by simpa
    apply Real.log_nonneg
    grw [one_le_div (by positivity), Real.sqrt_le_left (by positivity), ← Real.add_one_le_exp]
    norm_num
  set r := ((1 : ℝ) / (2 * (n + 1) + 1)) ^ 2 with hr
  have hr1 : r < 1 := by grw [hr, ← n.zero_le]; norm_num
  suffices HasSum (fun j ↦ r ^ (j + 1) / 3) ((1 : ℝ) / (12 * (n + 1 : ℕ) * ((n + 1 : ℕ) + 1))) by
    refine hasSum_le (fun j ↦ ?_) (log_stirlingSeq_diff_hasSum n) this
    simpa [hr, field] using show (3 : ℝ) ≤ 2 * (j + 1) + 1 by norm_cast; grind
  grind [((hasSum_geometric_of_lt_one (by positivity) hr1).mul_right r).div_const 3]

/-- We have the bound `log (stirlingSeq n) - log (stirlingSeq (n+1)) ≤ 1 / (4 n ^ 2)`. -/
@[deprecated "Use `log_stirlingSeq_diff_le` instead." (since := "2026-03-16")]
theorem log_stirlingSeq_sub_log_stirlingSeq_succ (n : ℕ) :
    log (stirlingSeq n) - log (stirlingSeq (n + 1)) ≤ 1 / (4 * n ^ 2) := by
  grw [log_stirlingSeq_diff_le]
  cases n <;> simp [field]; grind

/-- For any `n`, we have `log_stirlingSeq 1 - log_stirlingSeq n ≤ 12⁻¹`. -/
theorem log_stirlingSeq_bounded_aux (n : ℕ) :
    log (stirlingSeq 1) - log (stirlingSeq (n + 1)) ≤ 12⁻¹ := by
  let f (k : ℕ) : ℝ := log (stirlingSeq (k + 1))
  let g (k : ℕ) : ℝ := 1 / (12 * (k + 1))
  have hf k (hk : k ∈ range n) : f k - (f (k + 1)) ≤ g k - g (k + 1) := by
    grw [log_stirlingSeq_diff_le]
    simp [field]
  replace hf := Finset.sum_le_sum hf
  rw [Finset.sum_range_sub', Finset.sum_range_sub'] at hf
  simp only [f, g, zero_add] at hf
  grw [hf]
  simp
  grind

/-- The sequence `log_stirlingSeq` is bounded below for `n ≥ 1`. -/
theorem log_stirlingSeq_bounded_by_constant (n : ℕ) :
    1 - 12⁻¹ - log 2 / 2 ≤ log (stirlingSeq (n + 1)) := by
  have := log_stirlingSeq_bounded_aux n
  rw [stirlingSeq_one, log_div (by positivity), log_exp, log_sqrt] at this <;> grind

/-- The sequence `stirlingSeq` is positive for `n > 0`. -/
theorem stirlingSeq'_pos (n : ℕ) : 0 < stirlingSeq (n + 1) := by unfold stirlingSeq; positivity

/-- The sequence `stirlingSeq` has a positive lower bound. -/
theorem stirlingSeq'_bounded_by_pos_constant : ∃ a, 0 < a ∧ ∀ n : ℕ, a ≤ stirlingSeq (n + 1) := by
  let c := 1 - 12⁻¹ - log 2 / 2
  have h := log_stirlingSeq_bounded_by_constant
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
  apply Asymptotics.isEquivalent_of_tendsto_one
  have : sqrt π ≠ 0 := by positivity
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
See also `log_stirlingSeq_diff_le` for Robbins' sharp bound on successive differences in the
Stirling sequence.
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
See also `log_stirlingSeq_diff_le` for Robbins' sharp bound of `1/(12k(k+1))` on successive
differences in the Stirling sequence, which provides finer control over the convergence rate.
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
