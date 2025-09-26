/-
Copyright (c) 2025 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Tactic.Isolate.Tagging
import Mathlib.Tactic.Positivity

-- We deliberately mock R here so that we don't have to import the deps
axiom Real : Type
notation "ℝ" => Real
@[instance] axiom Real.field : Field ℝ
@[instance] axiom Real.linearOrder : LinearOrder ℝ
@[instance] axiom Real.isStrictOrderedRing : IsStrictOrderedRing ℝ

private axiom test_sorry : ∀ {α}, α

set_option trace.debug true

example {x y z : ℝ} (_hy : 0 < y) : (x + 3) * y ^ 2 - 2 = z := by
  isolate x + 3
  guard_target = x + 3 = (z + 2) / y ^ 2
  exact test_sorry

example {x y z : ℝ} : (x + 3) * y ^ 2 - 2 = z := by
  isolate x + 3
  guard_target = x + 3 = (z + 2) / y ^ 2
  exact test_sorry
  guard_target = y ^ 2 ≠ 0
  exact test_sorry

example {x y z : ℝ} (_hy : 0 < y) : (x + 3) * y ^ 2 - 2 ≤ z := by
  isolate x + 3
  guard_target = x + 3 ≤ (z + 2) / y ^ 2
  exact test_sorry

example {x y z : ℝ} (_hy : 0 < y) : (x + 3) * y ^ 2 - 2 < z := by
  isolate x + 3
  guard_target = x + 3 < (z + 2) / y ^ 2
  exact test_sorry

example {x y z : ℝ} (_hy : 0 < y) : z ≤ (x + 3) * y ^ 2 - 2 := by
  isolate x + 3
  guard_target = (z + 2) / y ^ 2 ≤ x + 3
  exact test_sorry

example {x y z : ℝ} (_hy : 0 < y) : z < (x + 3) * y ^ 2 - 2 := by
  isolate x + 3
  guard_target = (z + 2) / y ^ 2 < x + 3
  exact test_sorry

set_option linter.unusedVariables false in
-- isolate term in a hypothesis
example {x y z : ℝ} (_hy : 0 < y) (H : z < (x + 3) * y ^ 2 - 2) : True := by
  isolate x + 3 at H
  guard_hyp H : (z + 2) / y ^ 2 < x + 3
  exact trivial

set_option linter.unusedVariables false in
-- isolate term in wildcard location
example {x y z : ℝ} (_hy : 0 < y) (H : z < (x + 3) * y ^ 2 - 2) : x + 3 - 4 < y := by
  isolate x + 3 at *
  guard_hyp H : (z + 2) / y ^ 2 < x + 3
  guard_target = x + 3 < y + 4
  exact test_sorry

-- isolate on the RHS of a symmetric relation
example {x y z : ℝ} (_hy : 0 < y) : z = (x + 3) * y ^ 2 - 2 := by
  isolate x + 3
  guard_target = x + 3 = (z + 2) / y ^ 2
  exact test_sorry

-- isolation of an expression will proceed as far as possible, even if the expression cannot be
-- fully isolated
example {x : ℕ} {y : ℚ} : ↑(x + 2) + 3 = y := by
  isolate x
  guard_target = ↑(x + 2) = y - 3
  exact test_sorry

-- a term can be "isolated" even if it doesn't contain free variables
example {x y : ℝ} : x + 3 = y := by
  isolate (3:ℝ)
  guard_target = 3 = y - x
  exact test_sorry

/-- error: x + 3 should appear in only one (not both) of x + 3 and (x + 3) * y ^ 2 - 2 -/
#guard_msgs in
example {x y z : ℝ} (_hy : 0 < y) : x + 3 < (x + 3) * y ^ 2 - 2 := by
  isolate x + 3

/-- error: x + 2 should appear in either z or (x + 3) * y ^ 2 - 2 -/
#guard_msgs in
example {x y z : ℝ} (_hy : 0 < y) : z < (x + 3) * y ^ 2 - 2 := by
  isolate x + 2

/-- error: No x + 2 term was found anywhere to isolate -/
#guard_msgs in
example {x y z : ℝ} (_hy : 0 < y) : z < (x + 3) * y ^ 2 - 2 := by
  isolate x + 2 at *

/-- error: x + 3 is already isolated in x + 3 = y -/
#guard_msgs in
example {x y : ℝ} : x + 3 = y := by
  isolate x + 3

/-- error: f is not an explicit function -/
#guard_msgs in
example (x : ℝ) (f : ℝ → ℝ) : f x = 12 := by
  isolate x

/-! ### Tagging -/

/-- info: [Mathlib.Tactic.Isolate.add_right_le_iff] -/
#guard_msgs in
#query_isolate_lemmas `LE.le `HAdd.hAdd 4 0

/-- error: Please rephrase this lemma in the symmetric form a + b ~ c ↔ _. -/
#guard_msgs in
@[isolate]
theorem add_right_eq_iff [AddGroup X] (a b c : X) : c = a + b ↔ a = c - b := test_sorry

/--
error: @[isolate] attribute only applies to lemmas proving f x ∼ y ↔ x ∼' g y.
 No relation with at least two arguments found in the conclusion a * (b + c) = a * b + a * c
-/
#guard_msgs in
attribute [isolate] mul_add

/--
error: @[isolate] attribute only applies to lemmas proving f x ∼ y ↔ x ∼' g y.
 Leading LHS function f is not a constant in the conclusion f a = b ↔ a = f b
-/
#guard_msgs in
@[isolate]
theorem foo (f : ℝ → ℝ) (a b : ℝ) : f a = b ↔ a = f b := test_sorry
