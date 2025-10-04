import Mathlib.Tactic.Reap.Tactic.Syntax
import Mathlib.Tactic.Reap.Tactic.Search

example : (a b : Nat) → a = b → b = a := by
  intro a b h
  subst h
  simp_all only

example : (a b c : Nat) → a = b → b = c → a = c := by
  intro a b c a_1 a_2
  subst a_1 a_2
  simp_all only
