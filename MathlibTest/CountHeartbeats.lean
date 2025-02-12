import Mathlib.Tactic.Ring

set_option linter.style.header false

/-- info: Used 7 heartbeats, which is less than the current maximum of 200000. -/
#guard_msgs in
#count_heartbeats in
example (a : Nat) : a = a := rfl

/-- info: Used 7 heartbeats, which is less than the minimum of 200000. -/
#guard_msgs in
guard_min_heartbeats in
example (a : Nat) : a = a := rfl

/-- info: Used 7 heartbeats, which is less than the minimum of 2000. -/
#guard_msgs in
guard_min_heartbeats 2000 in
example (a : Nat) : a = a := rfl

guard_min_heartbeats 1 in
example (a : Nat) : a = a := rfl

/-!
# Tests for the `countHeartbeats` linter
-/

section using_count_heartbeats

-- sets the `countHeartbeats` linter option to `true`
#count_heartbeats

mutual -- mutual declarations get ignored
theorem XY : True := trivial
end

/-- info: Used 4 heartbeats, which is less than the current maximum of 200000. -/
#guard_msgs in
-- we use two nested `set_option ... in` to test that the `heartBeats` linter enters both.
set_option linter.unusedTactic false in
set_option linter.unusedTactic false in
example : True := trivial

/-- info: Used 4 heartbeats, which is less than the current maximum of 200000. -/
#guard_msgs in
example : True := trivial

/-- info: 'YX' used 2 heartbeats, which is less than the current maximum of 200000. -/
#guard_msgs in
set_option linter.unusedTactic false in
set_option linter.unusedTactic false in
theorem YX : True := trivial

end using_count_heartbeats

section using_linter_option

set_option linter.countHeartbeats true

mutual -- mutual declarations get ignored
theorem XY' : True := trivial
end

/-- info: Used 4 heartbeats, which is less than the current maximum of 200000. -/
#guard_msgs in
-- we use two nested `set_option ... in` to test that the `heartBeats` linter enters both.
set_option linter.unusedTactic false in
set_option linter.unusedTactic false in
example : True := trivial

/-- info: Used 4 heartbeats, which is less than the current maximum of 200000. -/
#guard_msgs in
example : True := trivial

/-- info: 'YX'' used 2 heartbeats, which is less than the current maximum of 200000. -/
#guard_msgs in
set_option linter.unusedTactic false in
set_option linter.unusedTactic false in
theorem YX' : True := trivial

end using_linter_option
