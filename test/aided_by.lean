import Mathlib.Tactic
import Mathlib.Tactic.AidedBy

set_option aided_by.delay 400

-- Solving in the background
/--
info: Try this: by simp_all only
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : 2 ≤ 3 := by#
  sorry

/--
info: Try this: simp_all only
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : 2 ≤ 2 := by
  aided_by aesop? do
  sorry


-- Solving as soon as `aesop?` can complete the proof
opaque sillyN : Nat

axiom silly : sillyN = 2

/--
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : sillyN ≤ 3 := by#
  sorry

/--
info: Try this: by
  rw [silly]
  simp_all only
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : sillyN ≤ 4 := by#
  rw [silly]
  sorry

-- Ensuring reset of the cache
-- #eval clearCache

-- Showing that the task runs in the background
/--
info: Try this: by
  skip
  sleep 100
  simp_all only
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
set_option aided_by.delay 0 in
example : 2 ≤ 3 := by#
  skip
  sleep 100
  sorry

-- Messages tried after each steps
/--
info: Try this: by simp_all only
---
info: Try this: by
  skip
  simp_all only
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : 2 ≤ 2 := by#
   skip
   sorry

-- Using `apply?` in place of `aesop?`
macro "by!" tacs:tacticSeq : term =>
  `(by
  aided_by from_by apply? do $tacs)

macro "by!"  : term =>
  `(by
  aided_by from_by apply? do)

-- Added to make sure that the discriminant tree is loaded.
example : 2 ≤ 3 := by apply?

/--
info: Try this: by exact Nat.AtLeastTwo.prop
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : 2 ≤ 4 := by!
  sorry


def prop := 2 ≤ 3

example : prop := by
  rw [prop]
  exact Nat.AtLeastTwo.prop

example : 1 = 1 := by!
  sorry

/--
info: Try this: by
  rw [silly]
  simp_all only
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : sillyN ≤ 4 := by#
  rw [silly]
  sorry
