/-
Copyright (c) 2025 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Tactic.Isolate.Tagging
import Mathlib.Tactic.Positivity

private axiom test_sorry : ∀ {α}, α

-- set_option trace.debug true

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
example {x y z : ℝ} (_hy : 0 < y) (H : z < (x + 3) * y ^ 2 - 2 ) : True := by
  isolate x + 3 at H
  exact trivial

/-- error: x + 3 should appear in only one (not both) of x + 3 and (x + 3) * y ^ 2 - 2 -/
#guard_msgs in
example {x y z : ℝ} (_hy : 0 < y) (H : x + 3 < (x + 3) * y ^ 2 - 2 ) : True := by
  isolate x + 3 at H

/-- error: x + 2 should appear in either z or (x + 3) * y ^ 2 - 2 -/
#guard_msgs in
example {x y z : ℝ} (_hy : 0 < y) (H : z < (x + 3) * y ^ 2 - 2 ) : True := by
  isolate x + 2 at H

/-- error: No x + 2 term was found anywhere to isolate -/
#guard_msgs in
example {x y z : ℝ} (_hy : 0 < y) (H : z < (x + 3) * y ^ 2 - 2 ) : True := by
  isolate x + 2 at *

/-- info: [Mathlib.Tactic.Isolate.add_right_le_iff] -/
#guard_msgs in
#query_isolate_lemmas `LE.le `HAdd.hAdd 4 0
