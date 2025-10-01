import Mathlib.Tactic.Reap.Options
import Mathlib.Tactic.Reap.PremiseSelection.API

open Lean

/--
Construct a `Selector` (which acts on an `MVarId`)
from a function which takes the pretty printed goal.
-/
def PremiseSelection.ppSelector (selector : String → Config → MetaM (Array Suggestion)) (g : MVarId) (c : Config) :
    MetaM (Array Suggestion) := do
  selector (toString (← Meta.ppGoal g)) c

def psSelector : Lean.PremiseSelection.Selector :=
  fun mvarId _ => do
  let pp ← Meta.ppGoal mvarId
  let rs ← PremiseSelectionClient.getPremises (toString pp)
  return rs.map fun x => {name := x.formal_name.toName, score := 1.0}
