import Mathlib.Util.CountHeartbeats

-- sets the `countHeartbeats` linter option to `true`
#count_heartbeats

mutual -- mutual declarations get ignored
theorem XY : True := trivial
end

/-- info: Used 3 heartbeats, which is less than the current maximum of 200000. -/
#guard_msgs in
set_option linter.unusedTactic false in
set_option linter.unusedTactic false in
example : True := trivial

/-- info: Used 3 heartbeats, which is less than the current maximum of 200000. -/
#guard_msgs in
example : True := trivial
