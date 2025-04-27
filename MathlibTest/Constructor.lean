import Mathlib.Tactic.Constructor

structure Foo where
  a : Type
  x : List a

-- fconstructor
example : Foo := by
  fconstructor
  exact Nat
  exact [0,1,2]

-- econstructor
example : Foo := by
  econstructor
  exact [0,1,2]
