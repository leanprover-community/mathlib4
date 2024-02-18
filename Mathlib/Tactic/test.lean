import Mathlib

elab "build_cache" : command => Lean.Elab.Command.liftTermElabM do
  _ ← Mathlib.Tactic.LibraryRewrite.getRewriteLemmas

build_cache

example : 4 = 2+2 := by
  rw??

example {α} [CommGroup α] (g h : α) : g⁻¹ * g * (g * (fun x => x) h * g⁻¹) = h := by
  rw??


example (p : Nat → Nat → Prop) : (∀ x, ∃ y, p x y) = ∃ y : _ → _, ∀ x, p x (y x) := by
  rw??


example {α} [Field α] (a b : α) : (a + b)^2 = a^2+a*b+a*b+b^2 := by
  rw [add_sq a b]
  rw [add_left_inj (b ^ 2)]
  rw [mul_assoc 2 a b]
  rw [two_mul (a * b)]
  rw?? 5
