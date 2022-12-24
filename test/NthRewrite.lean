import Mathlib.Tactic.NthRewrite
import Mathlib.Algebra.Group.Defs

example [AddZeroClass G] {a : G} (h : a = a): a = (a + 0) := by
  nth_rewrite 2 [←add_zero a] at h
  exact h

example [AddZeroClass G] {a : G} : a + a = a + (a + 0) := by
  nth_rw 2 [←add_zero a]

-- Porting note: Port all tests from mathlib3 once `data.nat.basic` and `data.vector` are ported
