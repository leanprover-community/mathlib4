import Mathlib.Tactic.Linter.Papercut
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.ENNReal.Basic
/--
warning: declaration uses 'sorry'
---
warning: Division by `0` is usually defined to be zero: e.g. `3 / 0 = 0`!
This is allowed (and often defined to be `0`) to avoid having to constantly
prove that denominators are non-zero.
note: this linter can be disabled with `set_option linter.papercut false`
-/
#guard_msgs in
set_option linter.papercut true in
example (x : Rat) : x / 0 = 0 := sorry

/--
warning: declaration uses 'sorry'
---
warning: Subtraction in ℕ is actually truncated subtraction: e.g. `1 - 2 = 0`!
This yields the 'expected' result only when you also prove the inequality
'y ≤ x'
note: this linter can be disabled with `set_option linter.papercut false`
-/
#guard_msgs in
set_option linter.papercut true in
example (x y : Nat) : x - y = 0 := sorry

open scoped ENNReal in
/--
warning: declaration uses 'sorry'
---
warning: Subtraction in ℝ≥0∞ is actually truncated subtraction: e.g. `e - π = 0`!
This yields the 'expected' result only when you also prove the inequality
'y ≤ x'
note: this linter can be disabled with `set_option linter.papercut false`
-/
#guard_msgs in
set_option linter.papercut true in
example (x y : ℝ≥0∞) : x - y = 0 := sorry

open scoped NNReal in
/--
warning: declaration uses 'sorry'
---
warning: Subtraction in ℝ≥0 is actually truncated subtraction: e.g. `e - π = 0`!
This yields the 'expected' result only when you also prove the inequality
'y ≤ x'
note: this linter can be disabled with `set_option linter.papercut false`
-/
#guard_msgs in
set_option linter.papercut true in
example (x y : ℝ≥0) : x - y = 0 := sorry

/--
warning: declaration uses 'sorry'
---
warning: Subtraction in ℚ≥0 is actually truncated subtraction: e.g. `2⁻¹ - 1 = 0`!
This yields the 'expected' result only when you also prove the inequality
'y ≤ x'
note: this linter can be disabled with `set_option linter.papercut false`
-/
#guard_msgs in
set_option linter.papercut true in
example (x y : ℚ≥0) : x - y = 0 := sorry

-- if `y ≤ x` is in context, then `x - y` does not trigger the linter
/-- warning: declaration uses 'sorry' -/
#guard_msgs in
set_option linter.papercut true in
example (x y : ℚ≥0) {hxy : y ≤ x} : x - y = 0 := sorry

/--
warning: declaration uses 'sorry'
---
warning: Division in ℕ is actually the floor of the division: e.g. `1 / 2 = 0`!
This yields the 'expected' result only when you also prove that 'y' divides 'x'
note: this linter can be disabled with `set_option linter.papercut false`
-/
#guard_msgs in
set_option linter.papercut true in
example (x y : Nat) : x / y = 0 := sorry

-- if `y ∣ x` is in context, then `x / y` does not trigger the linter
/-- warning: declaration uses 'sorry' -/
#guard_msgs in
set_option linter.papercut true in
example (x y : Nat) (_ : y ∣ x): x / y = 0 := sorry

-- the linter emits no warning if the proof is complete.
#guard_msgs in
set_option linter.papercut true in
example (x : Nat) : x / 0 = 0 := x.div_zero

/--
warning: declaration uses 'sorry'
---
warning: Division by `0` is usually defined to be zero: e.g. `3 / 0 = 0`!
This is allowed (and often defined to be `0`) to avoid having to constantly
prove that denominators are non-zero.
note: this linter can be disabled with `set_option linter.papercut false`
-/
#guard_msgs in
set_option linter.papercut true in
example (x : Nat) : x / 0 = 0 := sorry

/--
warning: declaration uses 'sorry'
---
warning: Division by `0` is usually defined to be zero: e.g. `3 / 0 = 0`!
This is allowed (and often defined to be `0`) to avoid having to constantly
prove that denominators are non-zero.
note: this linter can be disabled with `set_option linter.papercut false`
-/
#guard_msgs in
set_option linter.papercut true in
example (x : Int) : x / 0 = 0 := sorry

-- check that a missing `OfNat` instance does not make the linter produce an error
/-- warning: declaration uses 'sorry' -/
#guard_msgs in
set_option linter.papercut true in
example {R} [Zero R] [Div R] (x : R) : x / 0 = 0 := sorry
