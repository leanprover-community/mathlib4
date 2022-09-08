import Mathlib.Mathport.Syntax

namespace Test

def Filter (α : Type) : Type := (α → Prop) → Prop
def Filter.atTop [Preorder α] : Filter α := fun _ => True
def Filter.eventually (p : α → Prop) (f : Filter α) := f p

notation3 "∀ᶠ " (...) " in " f ", " r:(scoped p => Filter.eventually p f) => r

#check ∀ᶠ (x : Nat) (y) in Filter.atTop, x < y
#check ∀ᶠ x in Filter.atTop, x < 3


notation3 "∃' " (...) ", " r:(scoped p => Exists p) => r
#check ∃' x < 3, x < 3


notation3 "~{" (x";"* => foldl (a b => (a, b)) ()) "}~" => x
#check ~{1; true; ~{2}~}~
#check ~{}~

notation3 "%[" (x","* => foldr (a b => a :: b) []) "]" => x
#check %[1, 2, 3]
