/-
The theory of even and odd Numbers
-/
import Mathlib.Tactic

def even (n : Nat) : Prop := ∃ d, n = 2 * d
def odd (n : Nat) : Prop := ∃ d, n = 2 * d + 1

/- ## interaction with 0 -/

lemma even_zero : even 0 := sorry

/- ## interaction with succ -/

lemma even_add_one {n : Nat} : even n -> odd (n+1)
lemma odd_add_one {n : Nat} : odd n -> odd (n+1)

/- ## interaction with add -/
