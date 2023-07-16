import Mathlib.Tactic.ExtractLets
import Std.Tactic.GuardExpr

example (h : let x := 1; x = x) : True := by
  extract_lets y at h
  fail_if_success extract_lets a at h
  extract_lets at h
  guard_hyp y : Nat := 1
  guard_hyp h :ₛ y = y
  trivial

example : True := by
  let h : (let x := 1; x = x) := rfl
  extract_lets y at h
  guard_hyp y : Nat := 1
  guard_hyp h :ₛ y = y := rfl
  trivial

example (h : let x := 1; let y := 2; x + 1 = y) : True := by
  extract_lets x y at h
  guard_hyp x : Nat := 1
  guard_hyp y : Nat := 2
  guard_hyp h :ₛ x + 1 = y
  trivial

example (h : let x := 1; let y := 2; x + 1 = y) : True := by
  extract_lets at h
  rename_i a b
  guard_hyp a : Nat := 1
  guard_hyp b : Nat := 2
  guard_hyp h :ₛ a + 1 = b
  trivial

example (h : let x := 1; let y := 2; x + 1 = y) : True := by
  extract_lets x at h
  intros
  guard_hyp x : Nat := 1
  guard_hyp h :ₛ let y := 2; x + 1 = y
  trivial

example (h : let x := 1; let y := 2; x + 1 = y) : let _z := 3; ∀ (_ : Nat), True := by
  extract_lets at *
  guard_hyp h : _ + 1 = _
  fail_if_success extract_lets x at h
  guard_target =ₛ ∀ (_ : Nat), True
  intro
  trivial
