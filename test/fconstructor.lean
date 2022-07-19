import Mathlib.Tactic.Constructor

structure Foo where
  a : Type
  x : List a

example : foo := by
  fconstructor
  exact Nat
  exact [0,1,2]
