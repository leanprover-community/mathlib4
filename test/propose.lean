import Std.Data.List.Basic
import Mathlib.Tactic.Propose

-- set_option trace.Tactic.propose true
-- set_option trace.Meta.Tactic.solveByElim true

theorem foo (L M : List α) (w : L.Disjoint M) (m : a ∈ L) : a ∉ M := fun h => w m h

example (K L M : List α) (w : L.Disjoint M) (m : K ⊆ L) : True := by
  propose using w
  have : K.Disjoint M := by assumption
  trivial

example (K L M : List α) (w : L.Disjoint M) (m : a ∈ L) : True := by
  propose using w
  have : a ∉ M := by assumption
  trivial
