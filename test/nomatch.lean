import Mathlib.Tactic.NoMatch

example : False → α := fun.
example : False → α := by intro.
example : ¬ False := fun.
example : ¬ False := by intro.
example : ¬ ¬ 0 = 0 := fun.
example : ¬ ¬ 0 = 0 := @fun x => match x with.
example : ¬ ¬ 0 = 0 := (match · with.)

example (h : False) : α := fun.
example (h : False) : α := match with.
example (h : False) : α := match h with.

example (h : Nat → False) : Nat := match h 1 with.

def ComplicatedEmpty : Bool → Type
  | false => Empty
  | true => PEmpty

example (h : ComplicatedEmpty b) : α := match b, h with.
example (h : Nat → ComplicatedEmpty b) : α := match b, h 1 with.
