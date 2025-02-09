/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Set

set_option linter.unusedVariables false in
example (n : ℕ) : True := by
  fail_if_success interval_cases n
  trivial

example (n : ℕ) (_ : 2 ≤ n) : True := by
  fail_if_success interval_cases n
  trivial

example (n m : ℕ) (_ : n ≤ m) : True := by
  fail_if_success interval_cases n
  trivial

example (n : ℕ) (w₂ : n < 0) : False := by interval_cases n

example (n : ℕ) (w₂ : n < 1) : n = 0 := by
  interval_cases n
  rfl -- done for free in the mathlib3 version

example (n : ℕ) (w₂ : n < 2) : n = 0 ∨ n = 1 := by
  interval_cases n
  · left; rfl
  · right; rfl

example (n : ℕ) (w₁ : 1 ≤ n) (w₂ : n < 3) : n = 1 ∨ n = 2 := by
  interval_cases n
  · left; rfl
  · right; rfl

example (n : ℕ) (w₁ : 1 ≤ n) (w₂ : n < 3) : n = 1 ∨ n = 2 := by
  interval_cases using w₁, w₂
  · left; rfl
  · right; rfl

-- make sure we only pick up bounds on the specified variable:
example (n m : ℕ) (w₁ : 1 ≤ n) (w₂ : n < 3) (_ : m < 2) : n = 1 ∨ n = 2 := by
  interval_cases n
  · left; rfl
  · right; rfl

example (n : ℕ) (w₁ : 1 < n) (w₂ : n < 4) : n = 2 ∨ n = 3 := by
  interval_cases n
  · left; rfl
  · right; rfl

example (n : ℕ) (w₁ : n ≥ 3) (w₂ : n < 5) : n = 3 ∨ n = 4 := by
  interval_cases n
  · left; rfl
  · right; rfl

example (n : ℕ) (w₀ : n ≥ 2) (w₁ : n ≥ 3) (w₂ : n < 5) : n = 3 ∨ n = 4 := by
  interval_cases n
  · left; rfl
  · right; rfl

example (n : ℕ) (w₁ : n > 2) (w₂ : n < 5) : n = 3 ∨ n = 4 := by
  interval_cases n
  · left; rfl
  · right; rfl

example (n : ℕ) (w₁ : n > 2) (w₂ : n ≤ 4) : n = 3 ∨ n = 4 := by
  interval_cases n
  · left; rfl
  · right; rfl

example (n : ℕ) (w₁ : 2 < n) (w₂ : 4 ≥ n) : n = 3 ∨ n = 4 := by
  interval_cases n
  · left; rfl
  · right; rfl

example (n : ℕ) (h1 : 4 < n) (h2 : n ≤ 6) : n < 20 := by
  interval_cases n
  · guard_target =ₛ 5 < 20; norm_num
  · guard_target =ₛ 6 < 20; norm_num

example (n : ℕ) (w₁ : n % 3 < 1) : n % 3 = 0 := by
  interval_cases h : n % 3
  · guard_hyp h : n % 3 = 0
    rfl

example (n : ℕ) (w₁ : n % 3 < 1) : n % 3 = 0 := by
  interval_cases n % 3
  rfl
  -- the Lean 3 version had a different goal state after the `interval_cases`
  -- the `n % 3` was not substituted, instead there was a hypothesis `h : n % 3 = 0` provided
  -- so the proof was:
  -- assumption

example (n : ℕ) (h1 : 4 ≤ n) (h2 : n < 10) : n < 20 := by
  interval_cases using h1, h2
  all_goals { norm_num }

-- example (n : ℕ+) (w₂ : n < 1) : False := by interval_cases n

-- example (n : ℕ+) (w₂ : n < 2) : n = 1 := by interval_cases n

-- example (n : ℕ+) (h1 : 4 ≤ n) (h2 : n < 5) : n = 4 := by interval_cases n

-- example (n : ℕ+) (w₁ : 2 < n) (w₂ : 4 ≥ n) : n = 3 ∨ n = 4 := by
--   interval_cases n,
--   { guard_target' (3 : ℕ+) = 3 ∨ (3 : ℕ+) = 4, left; rfl },
--   { guard_target' (4 : ℕ+) = 3 ∨ (4 : ℕ+) = 4, right; rfl },

-- example (n : ℕ+) (w₁ : 1 < n) (w₂ : n < 4) : n = 2 ∨ n = 3 := by
--   { interval_cases n, { left; rfl }, { right; rfl }, }

-- example (n : ℕ+) (w₂ : n < 3) : n = 1 ∨ n = 2 := by
--   { interval_cases n, { left; rfl }, { right; rfl }, }

-- example (n : ℕ+) (w₂ : n < 4) : n = 1 ∨ n = 2 ∨ n = 3 := by
--   { interval_cases n, { left; rfl }, { right, left; rfl }, { right, right; rfl }, }

example (z : ℤ) (h1 : z ≥ -3) (h2 : z < 2) : z < 20 := by
  interval_cases using h1, h2
  all_goals { norm_num }

example (z : ℤ) (h1 : z ≥ -3) (h2 : z < 2) : z < 20 := by
  interval_cases z
  · guard_target =ₛ (-3 : ℤ) < 20
    norm_num
  · guard_target =ₛ (-2 : ℤ) < 20
    norm_num
  · guard_target =ₛ (-1 : ℤ) < 20
    norm_num
  · guard_target =ₛ (0 : ℤ) < 20
    norm_num
  · guard_target =ₛ (1 : ℤ) < 20
    norm_num

example (n : ℕ) : n % 2 = 0 ∨ n % 2 = 1 := by
  set r := n % 2 with hr
  have h2 : r < 2 := by
    exact Nat.mod_lt _ (by decide)
  interval_cases hrv : r
  · left; exact hrv.symm.trans hrv
               --^ hover says `hrv : r = 0` and jumps to `hrv :` above
  · right; exact hrv.symm.trans hrv
               --^ hover says `hrv : r = 1` and jumps to `hrv :` above

/- https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/interval_cases.20bug -/
example {x : ℕ} (hx2 : x < 2) (h : False) : False := by
  have _this : x ≤ 1 := by
    -- `interval_cases` deliberately not focussed,
    -- this is testing that the `interval_cases` only acts on `have` side goal, not on both
    interval_cases x
    · exact zero_le_one
    · rfl -- done for free in the mathlib3 version
  exact h

/-
In Lean 3 this one didn't work! It reported:
  `deep recursion was detected at 'expression equality test'`
-/
example (n : ℕ) (w₁ : n > 1000000) (w₁ : n < 1000002) : n < 2000000 := by
  interval_cases n
  norm_num

section

variable (d : ℕ)

example (h : d ≤ 0) : d = 0 := by
  interval_cases d
  rfl

end
