import Mathlib.Tactic.AssumptionQuestion

/--
info: Try this:
  [apply] exact h
-/
#guard_msgs in
example (h : 1 = 1) : 1 = 1 := by
  assumption?

/--
info: Try this:
  [apply] exact this
-/
#guard_msgs in
example : 1 = 1 := by
  have : 1 = 1 := by rfl
  assumption?

/--
info: Try this:
  [apply] exact this
-/
#guard_msgs in
example : 1 = 1 := by
  let : 1 = 1 := by rfl
  assumption?

/--
info: Try this:
  [apply] exact h
-/
#guard_msgs in
example : 1 = 1 := by
  have h : 1 = 1 := by rfl
  assumption?

/--
info: Try this:
  [apply] exact h
-/
#guard_msgs in
example : 1 = 1 := by
  let h : 1 = 1 := by rfl
  assumption?

/--
info: Try this:
  [apply] (expose_names; exact inst_1)
-/
#guard_msgs in
example [Nonempty a] [Decidable a] : Decidable a := by
  assumption?
