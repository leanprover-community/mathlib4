import Mathlib.Tactic.Linter.FlexibleLinter

import Mathlib.Data.ENNReal.Operations
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

set_option linter.flexible true
set_option linter.unusedVariables false

/-! # Advanced tests for the flexible linter

This file contains tests for the flexible linter which require heavier imports, such as the
mathlib tactics `norm_num`, `ring`, `group`, `positivity` or `module`.
In essence, it verifies how certain mathlib tactics are treated.

-/

-- `norm_num` is allowed after `simp`.
#guard_msgs in
example : (0 + 2 : Rat) + 1 = 3 := by
  simp
  norm_num

/-- ## further flexible tactics -/
/--
warning: 'simp' is a flexible tactic modifying '⊢'…

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: … and 'rw [add_comm]' uses '⊢'!
-/
#guard_msgs in
-- `norm_num` is allowed after `simp`, but "passes along the stain".
example {a : Rat} : a + (0 + 2 + 1 : Rat) = 3 + a := by
  simp
  norm_num
  rw [add_comm]

#guard_msgs in
example {V : Type*} [AddCommMonoid V] {x y : V} : 0 + x + (y + x) = x + x + y := by
  simp
  module

-- `grind` is another flexible tactic, as is `cfc_tac`, `positivity` and `finiteness`.
#guard_msgs in
example {x y : ℕ} : 0 + x + (y + x) = x + x + y := by
  simp
  grind

#guard_msgs in
example (h : False) : False ∧ True := by
  simp
  cfc_tac

#guard_msgs in
example {k l : ℤ} : 0 ≤ k ^ 2 + 4 * l * 0 := by
  simp
  positivity

open scoped ENNReal
#guard_msgs in
example {a b c : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞) : a * b ≠ ∞ := by
  simp
  finiteness

--  `abel` and `abel!` are allowed `simp`-followers.
#guard_msgs in
example {a b : Nat} : a + b = b + a + 0 := by
  simp
  abel

#guard_msgs in
example {a b : Nat} : a + b = b + a + 0 := by
  simp
  abel!

--  `ring` and `ring!` are allowed `simp`-followers.
#guard_msgs in
example {a b : Nat} : a + b = b + a + 0 := by
  simp
  ring

#guard_msgs in
example {a b : Nat} : a + b = b + a + 0 := by
  simp
  ring!

-- Test that `linear_combination` is accepted as a follower of `simp`.
example {a b : ℤ} (h : a + 1 = b) : a + 1 + 0 = b := by
  simp
  linear_combination h

-- Test that `linarith` is accepted as a follower of `simp`.
#guard_msgs in
example {a b : ℤ} (h : a + 1 = b) : a + 1 + 0 = b := by
  simp
  linarith

-- Test that `nlinarith` is accepted as a follower of `simp`.
#guard_msgs in
example {a b : ℤ} (h : a + 1 = b) : a + 1 + 0 = b := by
  simp
  nlinarith

/-- ## followers/rigidifiers -/

--  `abel_nf` is a `rigidifier`: the "stain" of `simp` does not continue past `abel_nf`.
#guard_msgs in
example {a b : Nat} (h : a + b = a + (b + 1)) : a + b = b + a + 0 + 1 := by
  simp
  abel_nf
  assumption

-- So are `abel_nf!` and `group`.
#guard_msgs in
example {a b : Nat} (h : a + b = a + (b + 1)) : a + b = b + a + 0 + 1 := by
  simp
  abel_nf!
  assumption

#guard_msgs in
example {a b : Nat} (h : a + b = a + (b + 1)) : a + b = b + a + 0 + 1 := by
  simp
  group at h ⊢
  assumption

#guard_msgs in
example {a b : ℝ≥0∞} (ha : a = 0) (hb : b = a) : a + b + 3 < ∞ := by
  simp [hb]
  finiteness_nonterminal; simp [ha]

--  `ring_nf` is a `rigidifier`: the "stain" of `simp` does not continue past `ring_nf`.
-- So is `ring_nf!`.
#guard_msgs in
example {a b : Nat} (h : a + b = 1 + a + b) : a + b = b + a + 0 + 1 := by
  simp
  ring_nf
  assumption

#guard_msgs in
example {a b : Nat} (h : a + b = 1 + a + b) : a + b = b + a + 0 + 1 := by
  simp
  ring_nf!
  assumption
