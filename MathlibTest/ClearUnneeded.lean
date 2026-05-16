import Mathlib.Tactic.ClearUnneeded

set_option linter.unusedTactic false
set_option linter.unusedVariables false

-- removes both `a` and `b`
example (a : Bool) : Bool := by
  let b : Bool := true
  clear_unneeded
  fail_if_success assumption
  fail_if_success exact a
  fail_if_success exact b
  exact true

-- does not remove `a`, because `b` depends on it (via its type)
example : Bool := by
  let a : Bool := true
  let b : a = true := by rfl
  clear_unneeded
  exact a

-- does not remove `a`, because `b` depends on it (via its value)
example : Bool := by
  let a : Bool := true
  let b : Bool := a
  clear_unneeded
  exact a

-- does not remove `a`, because we don't have `Nonempty` for `(true = true)`
example : true = true := by
  let a : true = true := by rfl
  clear_unneeded
  exact a

noncomputable example [h : Nonempty α] (a : α) (b : β) : α := by
  guard_hyp a
  clear_unneeded
  fail_if_success guard_hyp a
  guard_hyp b
  exact Classical.choice h

example [h : Inhabited α] (a : α) (b : β) : α := by
  guard_hyp a
  clear_unneeded
  fail_if_success guard_hyp a
  guard_hyp b
  exact default
