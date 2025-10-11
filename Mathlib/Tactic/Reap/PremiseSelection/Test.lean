import Lean
import Reap.PremiseSelection.Syntax

set_premise_selector psSelector

example (a b : Nat) : a + b = b + a := by
  suggest_premises
  sorry
