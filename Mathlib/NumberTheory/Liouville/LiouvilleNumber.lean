/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Jujian Zhang
-/
import Mathlib.NumberTheory.Liouville.Basic

#align_import number_theory.liouville.liouville_number from "leanprover-community/mathlib"@"04e80bb7e8510958cd9aacd32fe2dc147af0b9f1"

/-!

# Liouville constants

This file contains a construction of a family of Liouville numbers, indexed by a natural number $m$.
The most important property is that they are examples of transcendental real numbers.
This fact is recorded in `transcendental_liouvilleNumber`.

More precisely, for a real number $m$, Liouville's constant is
$$
\sum_{i=0}^\infty\frac{1}{m^{i!}}.
$$
The series converges only for $1 < m$. However, there is no restriction on $m$, since,
if the series does not converge, then the sum of the series is defined to be zero.

We prove that, for $m \in \mathbb{N}$ satisfying $2 \le m$, Liouville's constant associated to $m$
is a transcendental number. Classically, the Liouville number for $m = 2$ is the one called
``Liouville's constant''.

## Implementation notes

The indexing $m$ is eventually a natural number satisfying $2 ≤ m$. However, we prove the first few
lemmas for $m \in \mathbb{R}$.
-/


noncomputable section

open scoped Nat

open Real Finset

/-- For a real number `m`, Liouville's constant is
$$
\sum_{i=0}^\infty\frac{1}{m^{i!}}.
$$
The series converges only for `1 < m`. However, there is no restriction on `m`, since,
if the series does not converge, then the sum of the series is defined to be zero.
-/
def liouvilleNumber (m : ℝ) : ℝ :=
  ∑' i : ℕ, 1 / m ^ i !
#align liouville_number liouvilleNumber

namespace LiouvilleNumber

/-- `LiouvilleNumber.partialSum` is the sum of the first `k + 1` terms of Liouville's constant,
i.e.
$$
\sum_{i=0}^k\frac{1}{m^{i!}}.
$$
-/
def partialSum (m : ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ range (k + 1), 1 / m ^ i !
#align liouville_number.partial_sum LiouvilleNumber.partialSum

/-- `LiouvilleNumber.remainder` is the sum of the series of the terms in `liouvilleNumber m`
starting from `k+1`, i.e
$$
\sum_{i=k+1}^\infty\frac{1}{m^{i!}}.
$$
-/
def remainder (m : ℝ) (k : ℕ) : ℝ :=
  ∑' i, 1 / m ^ (i + (k + 1))!
#align liouville_number.remainder LiouvilleNumber.remainder

/-!
We start with simple observations.
-/


protected theorem summable {m : ℝ} (hm : 1 < m) : Summable fun i : ℕ => 1 / m ^ i ! :=
  summable_one_div_pow_of_le hm Nat.self_le_factorial
#align liouville_number.summable LiouvilleNumber.summable

theorem remainder_summable {m : ℝ} (hm : 1 < m) (k : ℕ) :
    Summable fun i : ℕ => 1 / m ^ (i + (k + 1))! := by
  convert (summable_nat_add_iff (k + 1)).2 (LiouvilleNumber.summable hm)
#align liouville_number.remainder_summable LiouvilleNumber.remainder_summable

theorem remainder_pos {m : ℝ} (hm : 1 < m) (k : ℕ) : 0 < remainder m k :=
  tsum_pos (remainder_summable hm k) (fun _ => by positivity) 0 (by positivity)
#align liouville_number.remainder_pos LiouvilleNumber.remainder_pos

theorem partialSum_succ (m : ℝ) (n : ℕ) :
    partialSum m (n + 1) = partialSum m n + 1 / m ^ (n + 1)! :=
  sum_range_succ _ _
#align liouville_number.partial_sum_succ LiouvilleNumber.partialSum_succ

/-- Split the sum defining a Liouville number into the first `k` terms and the rest. -/
theorem partialSum_add_remainder {m : ℝ} (hm : 1 < m) (k : ℕ) :
    partialSum m k + remainder m k = liouvilleNumber m :=
  sum_add_tsum_nat_add _ (LiouvilleNumber.summable hm)
#align liouville_number.partial_sum_add_remainder LiouvilleNumber.partialSum_add_remainder

/-! We now prove two useful inequalities, before collecting everything together. -/


/-- An upper estimate on the remainder. This estimate works with `m ∈ ℝ` satisfying `1 < m` and is
stronger than the estimate `LiouvilleNumber.remainder_lt` below. However, the latter estimate is
more useful for the proof. -/
theorem remainder_lt' (n : ℕ) {m : ℝ} (m1 : 1 < m) :
    remainder m n < (1 - 1 / m)⁻¹ * (1 / m ^ (n + 1)!) :=
  -- two useful inequalities
  have m0 : 0 < m := zero_lt_one.trans m1
  have mi : 1 / m < 1 := (div_lt_one m0).mpr m1
  -- to show the strict inequality between these series, we prove that:
  calc
    (∑' i, 1 / m ^ (i + (n + 1))!) < ∑' i, 1 / m ^ (i + (n + 1)!) :=
        -- 1. the second series dominates the first
        tsum_lt_tsum (fun b => one_div_pow_le_one_div_pow_of_le m1.le
          (b.add_factorial_succ_le_factorial_add_succ n))
        -- 2. the term with index `i = 2` of the first series is strictly smaller than
        -- the corresponding term of the second series
        (one_div_pow_strictAnti m1 (n.add_factorial_succ_lt_factorial_add_succ (i := 2) le_rfl))
        -- 3. the first series is summable
        (remainder_summable m1 n)
        -- 4. the second series is summable, since its terms grow quickly
        (summable_one_div_pow_of_le m1 fun j => le_self_add)
    -- split the sum in the exponent and massage
    _ = ∑' i : ℕ, (1 / m) ^ i * (1 / m ^ (n + 1)!) := by
      simp only [pow_add, one_div, mul_inv, inv_pow]
    -- factor the constant `(1 / m ^ (n + 1)!)` out of the series
    _ = (∑' i, (1 / m) ^ i) * (1 / m ^ (n + 1)!) := tsum_mul_right
    -- the series is the geometric series
    _ = (1 - 1 / m)⁻¹ * (1 / m ^ (n + 1)!) := by rw [tsum_geometric_of_lt_one (by positivity) mi]
#align liouville_number.remainder_lt' LiouvilleNumber.remainder_lt'

theorem aux_calc (n : ℕ) {m : ℝ} (hm : 2 ≤ m) :
    (1 - 1 / m)⁻¹ * (1 / m ^ (n + 1)!) ≤ 1 / (m ^ n !) ^ n :=
  calc
    (1 - 1 / m)⁻¹ * (1 / m ^ (n + 1)!) ≤ 2 * (1 / m ^ (n + 1)!) :=
      -- the second factors coincide (and are non-negative),
      -- the first factors satisfy the inequality `sub_one_div_inv_le_two`
      mul_le_mul_of_nonneg_right (sub_one_div_inv_le_two hm) (by positivity)
    _ = 2 / m ^ (n + 1)! := mul_one_div 2 _
    _ = 2 / m ^ (n ! * (n + 1)) := (congr_arg (2 / ·) (congr_arg (Pow.pow m) (mul_comm _ _)))
    _ ≤ 1 / m ^ (n ! * n) := by
      -- [NB: in this block, I do not follow the brace convention for subgoals -- I wait until
      -- I solve all extraneous goals at once with `exact pow_pos (zero_lt_two.trans_le hm) _`.]
      -- Clear denominators and massage*
      apply (div_le_div_iff _ _).mpr
      focus
        conv_rhs => rw [one_mul, mul_add, pow_add, mul_one, pow_mul, mul_comm, ← pow_mul]
        -- the second factors coincide, so we prove the inequality of the first factors*
        refine (mul_le_mul_right ?_).mpr ?_
      -- solve all the inequalities `0 < m ^ ??`
      any_goals exact pow_pos (zero_lt_two.trans_le hm) _
      -- `2 ≤ m ^ n!` is a consequence of monotonicity of exponentiation at `2 ≤ m`.
      exact _root_.trans (_root_.trans hm (pow_one _).symm.le)
        (pow_right_mono (one_le_two.trans hm) n.factorial_pos)
    _ = 1 / (m ^ n !) ^ n := congr_arg (1 / ·) (pow_mul m n ! n)
#align liouville_number.aux_calc LiouvilleNumber.aux_calc

/-- An upper estimate on the remainder. This estimate works with `m ∈ ℝ` satisfying `2 ≤ m` and is
weaker than the estimate `LiouvilleNumber.remainder_lt'` above. However, this estimate is
more useful for the proof. -/
theorem remainder_lt (n : ℕ) {m : ℝ} (m2 : 2 ≤ m) : remainder m n < 1 / (m ^ n !) ^ n :=
  (remainder_lt' n <| one_lt_two.trans_le m2).trans_le (aux_calc _ m2)
#align liouville_number.remainder_lt LiouvilleNumber.remainder_lt

/-! Starting from here, we specialize to the case in which `m` is a natural number. -/


/-- The sum of the `k` initial terms of the Liouville number to base `m` is a ratio of natural
numbers where the denominator is `m ^ k!`. -/
theorem partialSum_eq_rat {m : ℕ} (hm : 0 < m) (k : ℕ) :
    ∃ p : ℕ, partialSum m k = p / ((m ^ k ! :) : ℝ) := by
  induction' k with k h
  · exact ⟨1, by rw [partialSum, range_one, sum_singleton, Nat.cast_one, Nat.factorial,
      pow_one, pow_one]⟩
  · rcases h with ⟨p_k, h_k⟩
    use p_k * m ^ ((k + 1)! - k !) + 1
    rw [partialSum_succ, h_k, div_add_div, div_eq_div_iff, add_mul]
    · norm_cast
      rw [add_mul, one_mul, Nat.factorial_succ, add_mul, one_mul, add_tsub_cancel_right, pow_add]
      simp [mul_assoc]
    all_goals positivity
#align liouville_number.partial_sum_eq_rat LiouvilleNumber.partialSum_eq_rat

end LiouvilleNumber

open LiouvilleNumber

theorem liouville_liouvilleNumber {m : ℕ} (hm : 2 ≤ m) : Liouville (liouvilleNumber m) := by
  -- two useful inequalities
  have mZ1 : 1 < (m : ℤ) := by norm_cast
  have m1 : 1 < (m : ℝ) := by norm_cast
  intro n
  -- the first `n` terms sum to `p / m ^ k!`
  rcases partialSum_eq_rat (zero_lt_two.trans_le hm) n with ⟨p, hp⟩
  refine ⟨p, m ^ n !, one_lt_pow mZ1 n.factorial_ne_zero, ?_⟩
  push_cast
  rw [Nat.cast_pow] at hp
  -- separate out the sum of the first `n` terms and the rest
  rw [← partialSum_add_remainder m1 n, ← hp]
  have hpos := remainder_pos m1 n
  simpa [abs_of_pos hpos, hpos.ne'] using @remainder_lt n m (by assumption_mod_cast)
#align liouville_liouville_number liouville_liouvilleNumber

theorem transcendental_liouvilleNumber {m : ℕ} (hm : 2 ≤ m) :
    Transcendental ℤ (liouvilleNumber m) :=
  (liouville_liouvilleNumber hm).transcendental
#align transcendental_liouville_number transcendental_liouvilleNumber
