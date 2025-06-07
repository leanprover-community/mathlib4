/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
import Mathlib.Data.Nat.Log

/-!
# Fueled version of natural numbers logarithms

(Draft)

-/

assert_not_exists OrderTop

namespace Nat

theorem le_pow_self (b n : ℕ) (hb : 2 ≤ b) : n ≤ b ^ n := by
  induction n with
  | zero => simp
  | succ n h =>
    rw [Nat.pow_succ]
    apply le_trans (b := b ^ n * 2)
    · rw [Nat.mul_two]
      exact add_le_add h (one_le_pow _ _ (zero_lt_of_lt hb))
    exact mul_le_mul_left _ hb

lemma clog_fueled_le (fuel b n : ℕ) (h : n ≤ b ^ (fuel + 1)) :
    (n + b - 1) / b ≤ b ^ fuel := by
  rcases Nat.eq_zero_or_pos b with hb | hb
  · simp [hb]
  · rw [Nat.div_le_iff_le_mul hb]
    apply Nat.sub_le_sub_right
    apply Nat.add_le_add_right
    rwa [← Nat.pow_succ]


def clog_fueled (b n : ℕ) : ℕ :=
  if hb : b ≤ 1 then 0
  else
  let rec go (fuel : ℕ) (b : ℕ) (hb : 2 ≤ b) (a n : ℕ) (h : n ≤ b ^ fuel) : ℕ :=
  match fuel with
  | 0 => 0
  | fuel + 1 =>
    if n ≤ 1
      then a
      else go fuel b hb
        (a + 1) ((n + b - 1) / b)
        (clog_fueled_le fuel b n h)
  go n b (not_le.mp hb) 0 n (Nat.le_pow_self _ _ (not_le.mp hb))


section Tests

set_option linter.style.longLine false
set_option linter.style.setOption false

set_option trace.profiler true

-- 0.046
#eval clog_fueled 2 123456789012345667890123456789012345667890123456789012345667890123456789012345667890

-- max recursion depth is reached
example : clog_fueled 2 123456789012345667890123456789012345667890123456789012345667890123456789012345667890 = 277 := rfl

-- 900 steps are enough
set_option maxRecDepth 900 in
example : clog_fueled 2 123456789012345667890123456789012345667890123456789012345667890123456789012345667890 = 277 := rfl


-- 0.0450
#eval clog_fueled 2 123456789012345667890123456789012345667890123456789012345667890123456789012345667890123456789012345667890123456789012345667890123456789012345667890123456789012345667890
-- = 556

set_option maxRecDepth 1700 in
example : clog_fueled 2 123456789012345667890123456789012345667890123456789012345667890123456789012345667890123456789012345667890123456789012345667890123456789012345667890123456789012345667890 = 556 := rfl

-- 0.042
#eval logC 2 123456789012345667890123456789012345667890123456789012345667890123456789012345667890123456789012345667890123456789012345667890123456789012345667890123456789012345667890
-- = 555

end Tests

end Nat
