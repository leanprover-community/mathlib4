import Mathlib.Tactic.Linter.FlexibleLinter

import Mathlib.Data.ENNReal.Operations
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Field
import Mathlib.Tactic.Finiteness
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.Topology.Continuous
import Mathlib.Topology.Instances.Nat

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

/-! ## further flexible tactics -/

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

-- `grind` is another flexible tactic, as are `cfc_tac` and `finiteness`.
#guard_msgs in
example {x y : ℕ} : 0 + x + (y + x) = x + x + y := by
  simp
  grind

#guard_msgs in
example (h : False) : False ∧ True := by
  simp
  cfc_tac

-- Currently, `positivity` is not marked as flexible (as it only applies to goals in a very
-- particular shape). We use this test to record the current behaviour.
/--
warning: 'simp' is a flexible tactic modifying '⊢'…

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: … and 'positivity' uses '⊢'!
-/
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

-- Test that `continuity` is also a flexible tactic: the goal must be solvable by continuity,
-- but require some simplication first.
example {X : Type*} [TopologicalSpace X] {f : X → ℕ} {g : ℕ → X}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x ↦ (f ∘ g) x + 0) := by
  simp
  continuity

-- Currently, `fun_prop` is *not* marked as flexible (as it is rather structural on the exact
-- shape of the goal, and e.g. changing the goal to a defeq one could break the proof).
-- This test documents this behaviour.
/--
warning: 'simp' is a flexible tactic modifying '⊢'…

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: … and 'fun_prop' uses '⊢'!
-/
#guard_msgs in
example {X : Type*} [TopologicalSpace X] {f : X → ℕ} {g : ℕ → X}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x ↦ (f ∘ g) x + 0) := by
  simp
  fun_prop

-- A similar example for the `measurability` tactic.
example {α : Type*} [MeasurableSpace α] {f : α → ℚ} (hf : Measurable f) :
    Measurable (fun x ↦ f x + 0) := by
  simp
  measurability

--  `ring`, `ring1`, `ring!` and `ring1!` are allowed `simp`-followers.
#guard_msgs in
example {a b : Nat} : a + b = b + a + 0 := by
  simp
  ring

#guard_msgs in
example {a b : Nat} : a + b = b + a + 0 := by
  simp
  ring!

#guard_msgs in
example {a b : Nat} : a + b = b + a + 0 := by
  simp
  ring1

#guard_msgs in
example {a b : Nat} : a + b = b + a + 0 := by
  simp
  ring1!

-- So are ring1_nf and ring1_nf!.
#guard_msgs in
example {a b : Nat} (h : a + b = 1 + a + b) : a + b = b + a + 0 := by
  simp
  ring1_nf

#guard_msgs in
example {a b : Nat} (h : a + b = 1 + a + b) : a + b = b + a + 0 := by
  simp
  ring1_nf!

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

-- Test that `field_simp` is accepted as a follower of `simp`.
#guard_msgs in
example {K : Type*} [Field K] (x y z : K) (hy : 1 - y ≠ 0) (h : z = y) :
    x / (1 - y) / (1 + y / (1 - z)) = x := by
  simp [h]
  field_simp
  simp

/-! ## followers/rigidifiers -/

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

-- `field_simp` is a rigidifier
#guard_msgs in
example {K : Type*} [Field K] (x y z : K) (hy : 1 - y ≠ 0) (h : x = z) (h' : (1 - y + y) = 1) :
    x / (1 - y) / (1 + y / (1 - y)) = z := by
  field_simp
  rw [h', one_mul, h]

example {K : Type*} [Field K] (x y : K) (h : x + y = x + (y + 1)) : x + y = y + x + 0 + 1 := by
  simp [h]
  field

--  `ring_nf` is a `rigidifier`: the "stain" of `simp` does not continue past `ring_nf`.
-- So are `ring_nf!`, `ring1_nf` and `ring1_nf!`.
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
