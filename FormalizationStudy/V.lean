import Mathlib

/-
A quick count on paper gives me 11 options:
If both dominos are vertical, then we have 3 options.
If one of the dominoes is horizontal, we have 4 options.
If both are horizontal, we have 4 options.

It should be possible to get Lean do count this by `decide`.
Because each domino has 7 positions, and there are 2 dominoes.
And we singleton pieces then simply slot into place.

Hmm, there is an ambiguity in the question, namely whether the different
dominos are considered identical - I'm assuming that they are considered identical.

Let's use `Fin 2 × Fin 3` to describe the board.

And a domino can be a quadruple of numbers (a,b,c,d) such that `{a - b, c - d} = {1, 2}`
-/

structure Tile where
  (a b : Fin 2) (hab : a ≤ b)
  (c d : Fin 3) (hcd : c ≤ d)

def Tile.height (t : Tile) : Nat := t.b.val - t.a.val
def Tile.width (t : Tile) : Nat := t.d.val - t.c.val

def Tile.toSet (t : Tile) : Set (Fin 2 × Fin 3) :=
  Set.Icc t.a t.b ×ˢ Set.Icc t.c t.d

def Tile.shape (t : Tile) : ℕ × ℕ := (min t.height t.width, max t.height t.width)

-- def Tile.ofShape (shape : ℕ × ℕ) : Set Tile :=
--   { t | t.height = shape.1 ∧ t.width = shape.2 ∨ t.height = shape.2 ∧ t.width = shape.1 }

def shapes : Multiset (ℕ × ℕ) := [(1,1), (1,1), (1,2), (1,2)]
#check Multiset
/-
I need to somehow say in Lean that of all of the kinds of dominos, I have a collection s.t.
mapping the function `Tile.shape` gives the result `shapes`.
-/

open Finset

#check Set.ncard

example : (11 : ENat) = (11 : Nat) := by
  show_term bound

theorem V : Set.encard {ts : Multiset Tile | ts.map Tile.shape = shapes} = 11 := by
  rw [show (11 : ENat) = (11 : Nat) from rfl, ← ENat.toNat_eq_iff_eq_coe, ← Set.ncard_def]
  sorry
