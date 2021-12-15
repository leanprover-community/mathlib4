import Mathlib.Mathport.Syntax

namespace Test

def Filter (α : Type) : Type := (α → Prop) → Prop
def Filter.atTop [Preorder α] : Filter α := fun _ => True
def Filter.eventually (p : α → Prop) (f : Filter α) := f p

notation3 "∀ᶠ " (...) " in " f ", " r:(scoped p => Filter.eventually p f) => r

#check ∀ᶠ x y _ : Nat in Filter.atTop, x < y
#check ∀ᶠ x y in Filter.atTop, x < y
