import Mathlib.Tactic.IntroAt
import Std.Tactic.GuardExpr

example (h : let x := 1; x = x) : True := by
  intro y at h
  guard_hyp y : Nat := 1
  guard_hyp h :ₛ y = y
  trivial

example : True := by
  let h : (let x := 1; x = x) := rfl
  intro y at h
  guard_hyp y : Nat := 1
  guard_hyp h :ₛ y = y := rfl
  trivial

example (h : let x := 1; let y := 2; x + 1 = y) : True := by
  intro x y at h
  guard_hyp x : Nat := 1
  guard_hyp y : Nat := 2
  guard_hyp h :ₛ x + 1 = y
  trivial

example (h : let x := 1; let y := 2; x + 1 = y) : True := by
  intro x at h
  guard_hyp x : Nat := 1
  guard_hyp h :ₛ let y := 2; x + 1 = y
  trivial
