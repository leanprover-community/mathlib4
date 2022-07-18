import Mathlib.Tactic.Constructor

structure foo :=
(a : Type)
(x : List a)

example : foo := by
  fconstructor
  exact Nat
  exact [0,1,2]
