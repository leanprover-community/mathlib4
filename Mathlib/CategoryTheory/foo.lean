def α : Type := sorry
def inv : α → α := sorry
def mul : α → α → α := sorry
def one : α := sorry

theorem inv_eq {a b : α} (w : mul a b = one) : inv a = b := sorry

attribute [grind] inv_eq

example {a b : α} (w : mul a b = one) : inv a = b := by grind

structure S where
  f : Bool → α
  h : mul (f true) (f false) = one
  h' : mul (f false) (f true) = one

attribute [grind =] S.h S.h'

example (s : S) : inv (s.f true) = s.f false := by grind
