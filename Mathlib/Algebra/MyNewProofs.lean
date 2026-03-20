import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Basic

theorem my_add_comm (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b
