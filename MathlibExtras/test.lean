import Mathlib

example : 4 = 2+2 := by
  rw??

example {α} [CommGroup α] (g h : α) : g⁻¹ * g * (g * (fun x => x) h * g⁻¹) = h := by
  rw??


example (p : Nat → Nat → Prop) : (∀ x, ∃ y, p x y) = ∃ y : _ → _, ∀ x, p x (y x) := by
  rw??


example {α} [Field α] (a b : α) : (a + b)^2 = a^2+a*b+a*b+b^2 := by
  rw??
