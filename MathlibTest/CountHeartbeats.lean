import Mathlib.Util.CountHeartbeats
import Mathlib.Util.SleepHeartbeats

set_option linter.style.header false

/-- info: Used approximately 0 heartbeats, which is less than the current maximum of 200000. -/
#guard_msgs in
#count_heartbeats approximately in
example (a : Nat) : a = a := rfl

/-- info: Used approximately 0 heartbeats, which is less than the minimum of 200000. -/
#guard_msgs in
guard_min_heartbeats approximately in
example (a : Nat) : a = a := rfl

/-- info: Used approximately 0 heartbeats, which is less than the minimum of 2000. -/
#guard_msgs in
guard_min_heartbeats approximately 2000 in
example (a : Nat) : a = a := rfl

guard_min_heartbeats approximately 1 in
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

-- Test it goes into local `open in`
/-- info: 'a' used approximately 0 heartbeats, which is less than the current maximum of 200000. -/
#guard_msgs in
open Lean Meta in
theorem a : True := trivial

/-- info: 'b' used approximately 0 heartbeats, which is less than the current maximum of 200000. -/
#guard_msgs in
variable (n : Nat) in
open Lean in
theorem b : n ≥ 0 := by
  simp only [ge_iff_le, Nat.zero_le]

-- Test that local namespaces work:

/--
info: 'MyNamespace.helper' used approximately 0 heartbeats, which is less than the current maximum of 200000.
-/
#guard_msgs in
theorem MyNamespace.helper (m n : Nat) : m + n = n + m := Nat.add_comm m n
/--
info: 'MyNamespace.dependent' used approximately 0 heartbeats, which is less than the current maximum of 200000.
-/
#guard_msgs in
theorem MyNamespace.dependent (m n : Nat) : m + n = n + m := helper m n

-- -- Test: ideally this should not be marked, but in the current implementation
-- -- it is decided that this is okay.
-- open Nat in
-- set_option trace.Meta.Tactic.simp.heads true

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

/-- info: 'XX' used approximately 0 heartbeats, which is less than the current maximum of 200000. -/
#guard_msgs in
theorem XX : 3 + 4 + 5 = 12 := by
  decide


-- Don't want the try-this blocks of `#count_heartbeats in`
/--
info: 'too_slow' used approximately 0 heartbeats, which is greater than the current maximum of 89.
-/
#guard_msgs in
set_option maxHeartbeats 89 in
theorem too_slow : 3 + 4 + 5 = 12 := by
  decide


end using_linter_option


/-
Test: `#count_heartbeats in` and `set_option linter.countHeartbeats true` should return
the same result.
-/

/-- info: Used 3 heartbeats, which is less than the current maximum of 200000. -/
#guard_msgs in
#count_heartbeats in
theorem YX'₂ : True := trivial

/-- info: Used 93 heartbeats, which is less than the current maximum of 200000. -/
#guard_msgs in
#count_heartbeats in
theorem XX₂ : 3 + 4 + 5 = 12 := by
  decide
