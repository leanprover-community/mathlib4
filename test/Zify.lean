/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Robert Y. Lewis
-/

import Mathlib.Tactic.Zify
import Std.Tactic.GuardExpr
import Mathlib.Algebra.Group.Basic

-- Todo: These are verbatim copies of the tests from mathlib3. There

@[norm_cast] theorem ofNat_zero : Int.ofNat 0 = 0 := rfl

example (a b c x y z : ℕ) (h : ¬ x*y*z < 0) (h2 : (c : ℤ) < a + 3 * b) : a + 3*b > c := by
  zify at h ⊢
  push_cast at h
  -- fails because Int.ofNat_mul and Int.ofNat_zero are not flagged as `norm_cast`:
  --guard_hyp h : ¬↑x * ↑y * ↑z < (0 : ℤ)
  -- fails
  --guard_target =ₐ ↑c < (↑a : ℤ) + 3 * ↑b
  exact h2

example (a b : ℕ) (h : (a : ℤ) ≤ b) : a ≤ b := by
  zify
  guard_target == (a : ℤ) ≤ b
  exact h

/-example (a b : ℕ) (h : a = b ∧ b < a) : False := by
  zify at h
  rcases h with ⟨ha, hb⟩
  -- Preorder for `ℤ` is missing
  exact ne_of_lt hb ha-/

example (a b c : ℕ) (h : a - b < c) (hab : b ≤ a) : True := by
  zify [hab] at h
  -- fails because `Int.ofNat_sub` is not flagged as `norm_cast`
  --guard_hyp h : (a : ℤ) - b < c,
  trivial

example (a b c : ℕ) (h : a + b ≠ c) : True := by
  zify at h
  --guard_hyp h : (a + b : ℤ) ≠ c
  trivial
