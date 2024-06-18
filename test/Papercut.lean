import Mathlib.Tactic.Linter.Papercut
import Mathlib.Algebra.Field.Rat

/--
warning: Division by `0` is usually defined to be zero: e.g. `3 / 0 = 0`!
note: this linter can be disabled with `set_option linter.papercut false`
-/
#guard_msgs in
set_option linter.papercut true in
example (x : Rat) : x / 0 = 0 := div_zero x

/--
warning: Subtraction in ℕ is actually truncated subtraction: e.g. `1 - 2 = 0`!
note: this linter can be disabled with `set_option linter.papercut false`
-/
#guard_msgs in
set_option linter.papercut true in
example (x : Nat) : x - x = 0 := x.sub_self

/--
warning: Division by `0` is usually defined to be zero: e.g. `3 / 0 = 0`!
note: this linter can be disabled with `set_option linter.papercut false`
-/
#guard_msgs in
set_option linter.papercut true in
example (x : Nat) : x / 0 = 0 := x.div_zero

/--
warning: Division by `0` is usually defined to be zero: e.g. `3 / 0 = 0`!
note: this linter can be disabled with `set_option linter.papercut false`
-/
#guard_msgs in
set_option linter.papercut true in
example (x : Int) : x / 0 = 0 := x.ediv_zero
