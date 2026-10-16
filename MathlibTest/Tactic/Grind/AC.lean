section CCAC1

example (a b c : Nat) (f : Nat → Nat) : f (a + b + c) = f (c + b + a) := by
  grind

example (a b c : Nat) (f : Nat → Nat) : a + b = c → f (c + c) = f (a + b + c) := by
  grind

end CCAC1

section CCAC2

example (a b c d : Nat) (f : Nat → Nat → Nat) : b + a = d → f (a + b + c) a = f (c + d) a := by
  grind

end CCAC2

section CCAC3

example (a b c d e : Nat) (f : Nat → Nat → Nat) :
    b + a = d → b + c = e → f (a + b + c) (a + b + c) = f (c + d) (a + e) := by
  grind

example (a b c d e : Nat) (f : Nat → Nat → Nat) :
    b + a = d + d → b + c = e + e → f (a + b + c) (a + b + c) = f (c + d + d) (e + a + e) := by
  grind

section
universe u
variable {α : Type u}
variable (op : α → α → α)
variable [Std.Associative op]
variable [Std.Commutative op]

example (a b c d e : α) (f : α → α → α) :
    op b a = op d d → op b c = op e e →
    f (op a (op b c)) (op (op a b) c) = f (op (op c d) d) (op e (op a e)) := by
  grind [Std.Associative, Std.Commutative]
end

end CCAC3
