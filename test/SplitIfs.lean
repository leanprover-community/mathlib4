import Mathlib.Tactic.SplitIfs
example (x : Nat) (p : Prop) [Decidable p] : x = if p then x else x := by
  split_ifs with h1
  · rfl
  · rfl

example (x y : Nat) (p : Prop) [Decidable p] (h : if p then x = y else y = x) : x = y := by
  split_ifs at h
  · exact h
  · exact h.symm

example (x : Nat) (p q : Prop) [Decidable p] [Decidable q] :
    x = if p then (if q then x else x) else x := by
  split_ifs
  · rfl
  · rfl
  · rfl

example (x : Nat) (p : Prop) [Decidable p] :
    x = if (if p then False else True) then x else x := by
  split_ifs
  · rfl
  · rfl
  · rfl

example (p : Prop) [Decidable p] : if if ¬p then p else True then p else ¬p := by
  split_ifs with h
  · exact h
  · exact h

theorem foo (p q : Prop) [Decidable p] [Decidable q] :
    if if if p then ¬p else q then p else q then q else ¬p ∨ ¬q := by
  split_ifs with h1 h2 h3
  · exact h2
  · exact Or.inr h2
  · exact Or.inl h1
  · exact Or.inr h3
/-- info: 'foo' does not depend on any axioms -/
#guard_msgs in #print axioms foo

example (p : Prop) [Decidable p] (h : (if p then 1 else 2) > 3) : False := by
  split_ifs at h
  cases h
  · case pos.step h => cases h
  · case neg h =>
    cases h
    case step h =>
      cases h
      case step h => cases h

example (p : Prop) [Decidable p] (x : Nat) (h : (if p then 1 else 2) > x) :
     x < (if ¬p then 1 else 0) + 1 := by
   split_ifs at * <;> assumption

example (p : Prop) [Decidable p] : if if ¬p then p else True then p else ¬p := by
  split_ifs <;>
  assumption

example (p q : Prop) [Decidable p] [Decidable q] :
     if if if p then ¬p else q then p else q then q else ¬p ∨ ¬q := by
  split_ifs <;>
  simp [*]

example : True := by
  fail_if_success { split_ifs }
  trivial

open scoped Classical in
example (P Q : Prop) (w : if P then (if Q then true else true) else true = true) : true := by
  split_ifs at w
  -- check that we've fully split w into three subgoals
  · trivial
  · trivial
  · trivial
