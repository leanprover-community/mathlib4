import Mathlib.Tactic.ClearUnneeded

set_option linter.unusedTactic false
set_option linter.unusedVariables false

-- Clears hypotheses of Nonempty types with no forward deps.
example (a : Bool) : Bool := by
  let b : Bool := true
  clear_unneeded
  fail_if_success exact a
  fail_if_success exact b
  exact true

-- Does not clear `a` because `b` depends on it via its type.
example : Bool := by
  let a : Bool := true
  let b : a = true := by rfl
  clear_unneeded
  exact a

-- Does not clear `a` because `b` depends on it via its value.
example : Bool := by
  let a : Bool := true
  let b : Bool := a
  clear_unneeded
  exact a

-- Does not clear `a` because `true = true` has no Nonempty instance.
example : true = true := by
  let a : true = true := by rfl
  clear_unneeded
  exact a

-- Clears `a` (Nonempty α) but keeps `b` (no Nonempty β).
noncomputable example [h : Nonempty α] (a : α) (b : β) : α := by
  guard_hyp a
  clear_unneeded
  fail_if_success guard_hyp a
  guard_hyp b
  exact Classical.choice h

-- Clears `a` (Inhabited α implies Nonempty α) but keeps `b`.
example [h : Inhabited α] (a : α) (b : β) : α := by
  guard_hyp a
  clear_unneeded
  fail_if_success guard_hyp a
  guard_hyp b
  exact default
