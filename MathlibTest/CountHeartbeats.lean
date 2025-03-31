import Mathlib.Util.CountHeartbeats
import Mathlib.Util.SleepHeartbeats

set_option linter.style.header false

guard_min_heartbeats 1 in
example (a : Nat) : a = a := rfl

/-!
# Tests for the `countHeartbeats` linter
-/

section using_count_heartbeats

-- sets the `countHeartbeats` both linter option and the `approximate` option to `true`
#count_heartbeats approximately

mutual -- mutual declarations get ignored
theorem XY : True := trivial
end

/-- info: Used approximately 1000 heartbeats, which is less than the current maximum of 200000. -/
#guard_msgs in
-- we use two nested `set_option ... in` to test that the `heartBeats` linter enters both.
set_option linter.unusedTactic false in
set_option linter.unusedTactic false in
example : True := by
  sleep_heartbeats 1000 -- on top of these heartbeats, a few more are used by the rest of the proof
  trivial

/-- info: Used approximately 0 heartbeats, which is less than the current maximum of 200000. -/
#guard_msgs in
example : True := trivial

/-- info: 'YX' used approximately 0 heartbeats, which is less than the current maximum of 200000. -/
#guard_msgs in
set_option linter.unusedTactic false in
set_option linter.unusedTactic false in
theorem YX : True := trivial

end using_count_heartbeats

section using_linter_option

set_option linter.countHeartbeats true
set_option linter.countHeartbeatsApprox true

mutual -- mutual declarations get ignored
theorem XY' : True := trivial
end

/-- info: Used approximately 0 heartbeats, which is less than the current maximum of 200000. -/
#guard_msgs in
-- we use two nested `set_option ... in` to test that the `heartBeats` linter enters both.
set_option linter.unusedTactic false in
set_option linter.unusedTactic false in
example : True := trivial

/-- info: Used approximately 0 heartbeats, which is less than the current maximum of 200000. -/
#guard_msgs in
example : True := trivial

/--
info: 'YX'' used approximately 0 heartbeats, which is less than the current maximum of 200000.
-/
#guard_msgs in
set_option linter.unusedTactic false in
set_option linter.unusedTactic false in
theorem YX' : True := trivial

end using_linter_option
