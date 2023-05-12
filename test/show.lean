import Mathlib.Tactic.Basic
import Std.Tactic.GuardExpr

example (h : x = y) (h' : z = w) : x = y ∧ z = w := by
  constructor
  fail_if_success show z = z
  show z = _
  · exact h'
  exact h

example (h : x = y) (h' : z = w) : x = y ∧ z = w := by
  constructor
  case : z = _ =>
    exact h'
  case left =>
    exact h

example (h : x = y) (h' : z = w) : x = y ∧ z + 0 = w := by
  constructor
  case : z = _ =>
    guard_target =ₛ z = w
    exact h'
  case left =>
    exact h
