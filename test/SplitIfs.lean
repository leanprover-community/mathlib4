import Mathlib.Tactic.SplitIfs

example (x : Nat) (p : Prop) [Decidable p] : x = if p then x else x :=
 by split_ifs with h1
    · rfl
    · rfl

example (x y : Nat) (p : Prop) [Decidable p] (h : if p then x = y else y = x) : x = y :=
 by split_ifs at h
    · exact h
    · exact h.symm

example (x : Nat) (p q : Prop) [Decidable p] [Decidable q] :
      x = if p then (if q then x else x) else x :=
 by split_ifs
    · rfl
    · rfl
    · rfl

example (x : Nat) (p : Prop) [Decidable p] :
      x = if (if p then False else True) then x else x :=
 by split_ifs
    · rfl
    · rfl
    · rfl

example (p : Prop) [Decidable p] : if if ¬p then p else True then p else ¬p :=
by split_ifs with h1 h2
   · assumption
   · assumption

example (p q : Prop) [Decidable p] [Decidable q] :
    if if if p then ¬p else q then p else q then q else ¬p ∨ ¬q :=
by split_ifs with h1 h2 h3
   · exact h2
   · exact Or.inr h2
   · exact Or.inl h1
   · exact Or.inr h3
