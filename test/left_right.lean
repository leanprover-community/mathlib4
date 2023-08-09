import Mathlib.Tactic.LeftRight

def zero : Nat := by
  left

#eval zero -- 0

def two : Nat := by
  right
  exact 1

#eval two -- 2

example : Sum Nat (List Nat) := by
  left
  exact zero

example : Sum Nat (List Nat) := by
  right
  exact [0]

example : (1 = 1) ∨ (2 = 3) := by
  left
  rfl

example : (1 = 2) ∨ (3 = 3) := by
  right
  rfl
