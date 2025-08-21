import Mathlib.Util.PrintSorries

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
theorem thm1 : 1 = 2 := by sorry

/-- info: thm1 has sorry -/
#guard_msgs in
#print sorries thm1

theorem thm2 : 1 = 2 := thm1

/-- info: thm1 has sorry -/
#guard_msgs in
#print sorries thm2

/-- info: thm1 has sorry -/
#guard_msgs in
#print sorries

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
def f (n : Nat) : Nat := sorry
theorem thm3 : f 1 = f 2 := rfl -- (!) This is since it's a fixed `sorry : Nat`

/-- info: f has sorry -/
#guard_msgs in
#print sorries thm3

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
def f' : Nat → Nat := sorry
/--
error: Not a definitional equality: the left-hand side
  f' 1
is not definitionally equal to the right-hand side
  f' 2
---
error: Type mismatch
  rfl
has type
  ?m.7 = ?m.7
but is expected to have type
  f' 1 = f' 2
-/
#guard_msgs in
theorem thm3' : f' 1 = f' 2 := rfl -- fails as expected, it's an unknown `sorry : Nat → Nat`

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
theorem thm : True := by
  let f : Nat → Nat := sorry
  have : f 1 = f 2 := sorry
  unfold f at this
  change id _ at this
  trivial

-- Would print 4 sorries if there weren't `seenSorriesRef`.
-- /--
-- info: thm has sorry
-- thm has sorry
-- -/
-- #guard_msgs in
#print sorries thm

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
theorem thm' : True := sorryAx _ false

/-- info: thm' has sorryAx -/
#guard_msgs in
#print sorries thm'
