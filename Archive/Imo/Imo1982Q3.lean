/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Alex Brodbelt
-/
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Data.NNReal.Basic

/-!
# IMO 1982 Q3

Consider infinite sequences $\{x_n\}$ of positive reals such that $x_0 = 1$ and
$x_0 \ge x_1 \ge x_2 \ge \ldots$

a) Prove that for every such sequence there is an $n \ge 1$ such that:

$$\frac{x_0^2}{x_1} + \ldots + \frac{x_{n-1}^2}{x_n} \ge 3.999$$

b) Find such a sequence such that for all $n$:

$$\frac{x_0^2}{x_1} + \ldots + \frac{x_{n-1}^2}{x_n} < 4$$

The solution is based on Solution 1 from the
[Art of Problem Solving](https://artofproblemsolving.com/wiki/index.php/1982_IMO_Problems/Problem_3)
website. For part a, we use Sedrakyan's lemma to show the sum is bounded below by
$\frac{4n}{n + 1}$, which can be made arbitrarily close to $4$ by taking large $n$. For part b, we
show the sequence $x_n = 2^{-n}$ satisfies the desired inequality.
-/

open Finset NNReal

variable {x : ℕ → ℝ} {n : ℕ} (hn : n ≠ 0) (hx : Antitone x)

namespace Imo1982Q3
include hn hx

/-- `x n` is at most the average of all previous terms in the sequence.

This is expressed here with `∑ k ∈ range n, x k` added to both sides. -/
lemma le_avg : ∑ k ∈ range (n + 1), x k ≤ (∑ k ∈ range n, x k) * (1 + 1 / n) := by
  rw [sum_range_succ, mul_one_add, add_le_add_iff_left, mul_one_div,
    le_div_iff₀ (mod_cast hn.bot_lt), mul_comm, ← nsmul_eq_mul]
  conv_lhs => rw [← card_range n, ← sum_const]
  gcongr with i hi
  refine hx <| le_of_lt ?_
  simpa using hi

/-- The main inequality used for part a. -/
lemma ineq (h0 : x 0 = 1) (hp : ∀ k, 0 < x k) :
    4 * n / (n + 1) ≤ ∑ k ∈ range (n + 1), x k ^ 2 / x (k + 1) := by
  calc
    -- We first use AM-GM.
    _ ≤ (∑ k ∈ range n, x (k + 1) + 1) ^ 2 / (∑ k ∈ range n, x (k + 1)) * n / (n + 1) := by
      gcongr
      rw [le_div_iff₀]
      · simpa using four_mul_le_sq_add (∑ k ∈ range n, x (k + 1)) 1
      · exact sum_pos (fun k _ ↦ hp _) (nonempty_range_iff.2 hn)
    -- We move the fraction into the denominator.
    _ = (∑ k ∈ range n, x (k + 1) + 1) ^ 2 / ((∑ k ∈ range n, x (k + 1)) * (1 + 1 / n)) := by
      field_simp
    -- We make use of the `le_avg` lemma.
    _ ≤ (∑ k ∈ range (n + 1), x k) ^ 2 / ∑ k ∈ range (n + 1), x (k + 1) := by
      gcongr
      · exact sum_pos (fun k _ ↦ hp _) nonempty_range_add_one
      · exact add_nonneg (sum_nonneg fun k _ ↦ (hp _).le) zero_le_one
      · rw [sum_range_succ', h0]
      · exact le_avg hn (hx.comp_monotone @Nat.succ_le_succ)
    -- We conclude by Sedrakyan.
    _ ≤ _ := sq_sum_div_le_sum_sq_div _ x fun k _ ↦ hp (k + 1)

end Imo1982Q3

/-- Part a of the problem is solved by `n = 4000`. -/
theorem imo1982_q3a (hx : Antitone x) (h0 : x 0 = 1) (hp : ∀ k, 0 < x k) :
    ∃ n : ℕ, 3.999 ≤ ∑ k ∈ range n, (x k) ^ 2 / x (k + 1) := by
  use 4000
  convert Imo1982Q3.ineq (Nat.succ_ne_zero 3998) hx h0 hp
  norm_num

/-- Part b of the problem is solved by `x k = (1 / 2) ^ k`. -/
theorem imo1982_q3b : ∃ x : ℕ → ℝ, Antitone x ∧ x 0 = 1 ∧ (∀ k, 0 < x k)
    ∧ ∀ n, ∑ k ∈ range n, x k ^ 2 / x (k + 1) < 4 := by
  refine ⟨fun k ↦ 2⁻¹ ^ k, ?_, pow_zero _, ?_, fun n ↦ ?_⟩
  · apply (pow_right_strictAnti₀ _ _).antitone <;> norm_num
  · simp
  · have {k : ℕ} : (2 : ℝ)⁻¹ ^ (k * 2) * ((2 : ℝ)⁻¹ ^ k)⁻¹ = (2 : ℝ)⁻¹ ^ k := by
      rw [← pow_sub₀] <;> simp [mul_two]
    simp_rw [← pow_mul, pow_succ, ← div_eq_mul_inv, div_div_eq_mul_div, mul_comm, mul_div_assoc,
      ← mul_sum, div_eq_mul_inv, this, ← two_add_two_eq_four, ← mul_two,
      mul_lt_mul_iff_of_pos_left two_pos]
    convert NNReal.coe_lt_coe.2 <| geom_sum_lt (inv_ne_zero two_ne_zero) two_inv_lt_one n
    · simp
    · norm_num
