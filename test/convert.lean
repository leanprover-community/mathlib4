import Mathlib.Tactic.Convert
import Std.Tactic.GuardExpr
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Set.Image

example (P : Prop) (h : P) : P := by convert h

example (α β : Type) (h : α = β) (b : β) : α := by
  convert b

example (α β : Type) (h : ∀ α β : Type, α = β) (b : β) : α := by
  convert b
  apply h

example (α β : Type) (h : α = β) (b : β) : Nat × α := by
  convert (37, b)

example (α β : Type) (h : β = α) (b : β) : Nat × α := by
  convert ← (37, b)

example (α β : Type) (h : α = β) (b : β) : Nat × Nat × Nat × α := by
  convert (37, 57, 2, b)

example (α β : Type) (h : α = β) (b : β) : Nat × Nat × Nat × α := by
  convert (37, 57, 2, b) using 2
  guard_target = (Nat × α) = (Nat × β)
  congr

example (α β : Type) (h : α = β) (b : β) : Nat × Nat × Nat × α := by
  convert (37, 57, 2, b) using 3

example {f : β → α} {x y : α} (h : x ≠ y) : f ⁻¹' {x} ∩ f ⁻¹' {y} = ∅ :=
by
  have : {x} ∩ {y} = (∅ : Set α) := by simpa [ne_comm] using h
  convert Set.preimage_empty (f := f) -- porting note: mathlib3 didn't need to specify `f`
  rw [←Set.preimage_inter, this]

section convert_to

example {α} [AddCommMonoid α] {a b c d : α} (H : a = c) (H' : b = d) : a + b = d + c := by
  convert_to c + d = _ using 2
  rw [add_comm]

example {α} [AddCommMonoid α] {a b c d : α} (H : a = c) (H' : b = d) : a + b = d + c := by
  convert_to c + d = _ using 1
  congr 2
  rw [add_comm]

example {α} [AddCommMonoid α] {a b c d : α} (H : a = c) (H' : b = d) : a + b = d + c := by
  convert_to c + d = _ -- defaults to `using 1`
  congr 2
  rw [add_comm]

end convert_to
