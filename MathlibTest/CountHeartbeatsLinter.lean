import Mathlib.Util.CountHeartbeats

set_option linter.countHeartbeats true

-- sets the `countHeartbeats` linter option to `true`
#count_heartbeats

mutual -- mutual declarations get ignored
theorem XY : True := trivial
end

/-- info: Used 3 heartbeats, which is less than the current maximum of 200000. -/
#guard_msgs in
-- we use two nested `set_option ... in` to test that the `heartBeats` linter enters both.
set_option linter.unusedTactic false in
set_option linter.unusedTactic false in
example : True := trivial

/-- info: Used 3 heartbeats, which is less than the current maximum of 200000. -/
#guard_msgs in
example : True := trivial

/-- info: 'YX' used 2 heartbeats, which is less than the current maximum of 200000. -/
#guard_msgs in
set_option linter.unusedTactic false in
set_option linter.unusedTactic false in
theorem YX : True := trivial
