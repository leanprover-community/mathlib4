import Mathlib.Tactic.Ext
import Mathlib.Init.Logic

structure A (n : Nat) where
  a : Nat

structure B (n) extends A n where
  b : Nat
  h : b > 0
  i : Fin b

@[ext] structure C (n) extends B n where
  c : Nat

example (a b : C n) : a = b := by
  ext
  guard_target == a.a = b.a; admit
  guard_target == a.b = b.b; admit
  guard_target == HEq a.i b.i; admit
  guard_target == a.c = b.c; admit

example (f g : Nat × Nat → Nat) : f = g := by
  ext (x, y)
  guard_target == f (x, y) = g (x, y); admit
