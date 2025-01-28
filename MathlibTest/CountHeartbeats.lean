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

/-- info: 'YX' used 4 heartbeats, which is less than the current maximum of 200000. -/
#guard_msgs in
set_option linter.unusedTactic false in
set_option linter.unusedTactic false in
theorem YX : True := trivial

-- Test it goes into local `open in`
/-- info: 'a' used 8 heartbeats, which is less than the current maximum of 200000. -/
#guard_msgs in
open Lean Meta in
theorem a : True := trivial

/-- info: 'b' used 56 heartbeats, which is less than the current maximum of 200000. -/
#guard_msgs in
variable (n : Nat) in
open Lean in
theorem b : n ≥ 0 := by
  simp only [ge_iff_le, zero_le]

-- -- Test that local namespaces work:
--
-- /--
-- info: 'MyNamespace.helper' used 32 heartbeats, which is less than the current maximum of 200000.
-- -/
-- #guard_msgs in
-- theorem MyNamespace.helper (m n : Nat) : m + n = n + m := Nat.add_comm m n
-- /--
-- info: 'MyNamespace.dependent' used 32 heartbeats, which is less than the current maximum of 200000.
-- -/
-- #guard_msgs in
-- theorem MyNamespace.dependent (m n : Nat) : m + n = n + m := helper m n
--
-- -- Test: this shouldn't be measured, I think
-- open Nat in
-- set_option trace.Meta.Tactic.simp.heads true

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

/-- info: 'YX'' used 4 heartbeats, which is less than the current maximum of 200000. -/
#guard_msgs in
set_option linter.unusedTactic false in
set_option linter.unusedTactic false in
theorem YX' : True := trivial

/-- info: 'XX' used 182 heartbeats, which is less than the current maximum of 200000. -/
#guard_msgs in
theorem XX (a : ℤ) : (3 : ℤ) + 4 + 5 + a - a = 12 := by
  ring

end using_linter_option


/-
Test: `#count_heartbeats in` and `set_option linter.countHeartbeats true` should return
the same result.
-/

/-- info: Used 4 heartbeats, which is less than the current maximum of 200000. -/
#guard_msgs in
#count_heartbeats in
theorem YX'₂ : True := trivial

/-- info: Used 182 heartbeats, which is less than the current maximum of 200000. -/
#guard_msgs in
#count_heartbeats in
theorem XX₂ (a : ℤ): (3 : ℤ) + 4 + 5 + a - a = 12 := by
  ring
