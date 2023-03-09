import Mathlib.Tactic.Congr!


def Set (α : Type _) := α → Prop
def Set.image (f : α → β) (s : Set α) : Set β := fun y => ∃ x, s x ∧ f x = y

set_option trace.congr! true
example (s t : Set α) (f g : α → β) : Set.image f s = Set.image g t := by
  congr!
  sorry -- congr doesn't do anything

opaque partiallyApplied (p : Prop) [Decidable p] : Nat → Nat

example : partiallyApplied (True ∧ True) = partiallyApplied True := by
  simp

example : partiallyApplied (True ∧ True) = partiallyApplied True := by
  congr!
  decide

example (f g : α → β) (x y : α) : f x = g y := by
  congr!

example (β : α → Type) (f g : (x : α) → β x) (x y : α) : HEq (f x) (g y) := by
  congr!

inductive walk (α : Type) : α → α → Type
| nil (n : α) : walk α n n

def walk.map (f : α → β) (w : walk α x y) : walk β (f x) (f y) :=
  match x, y, w with
  | _, _, .nil n => .nil (f n)

example (w : walk α x y) (w' : walk α x' y') (f : α → β) : HEq (w.map f) (w'.map f) := by
  congr!
  -- get x = y and y = y' in context for `HEq w w'` goal.

example (p q : Prop) (h : p) (h' : q) : (⟨p, PLift.up h⟩ : (r : Prop) × PLift r) = ⟨q, .up h'⟩ := by
  congr! 1
