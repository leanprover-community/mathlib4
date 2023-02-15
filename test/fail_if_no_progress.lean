import Mathlib.Tactic.FailIfNoProgress
import Mathlib.Data.List.Basic

section success

example : 1 = 1 := by fail_if_no_progress rfl

example (h : 1 = 1) : True := by
  fail_if_no_progress simp at h
  trivial

example (x : ℕ) (h : 1 - 1 = x) : True := by
  fail_if_no_progress (config := { eqKind := .defEq }) simp at h
  trivial

end success

section failure

example (x : Bool) (h : x = true) : x = true := by
  fail_if_success
    fail_if_no_progress simp
  exact h

example (x : Bool) (h : x = true) : True := by
  fail_if_success
    fail_if_no_progress simp at h
  trivial

end failure

section config

def foo (x : ℕ) := x

@[reducible] def fooR (x : ℕ) := x

-- Progress is not made at reducible transparency when unfolding fooR
example (h : fooR x = y) : True := by
  fail_if_success
    fail_if_no_progress simp only [fooR] at h
  trivial

-- Progress is made at reducible transparency when unfolding foo
example (x : ℕ) (h : foo x = y) : True := by
  fail_if_no_progress simp only [foo] at h
  trivial

-- Progress is not made at default transparency when unfolding foo
example (x : ℕ) (h : foo x = y) : True := by
  fail_if_success
    fail_if_no_progress (config := { transparency := .default }) simp only [foo] at h
  trivial

-- Progress is made with `==` when unfolding fooR
example (x : ℕ) (h : fooR x = y) : True := by
  fail_if_no_progress (config := { eqKind := .beq }) simp only [fooR] at h
  trivial

end config
