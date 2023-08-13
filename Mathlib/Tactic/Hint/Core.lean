/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Data.List.Sort

/-!
# Hint tactic
-/

namespace Mathlib.Tactic.Hint

open Lean Elab Tactic MessageData Std.Tactic TryThis

initialize hintExtension : SimplePersistentEnvExtension Syntax.Tactic (List Syntax.Tactic) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := List.concat
    addImportedFn := Array.foldl (fun l a => a.toList ++ l) []
  }

/-- `add_hint_tactic t` runs the tactic `t` whenever `hint` is invoked.
The typical use case is `add_hint_tactic foo` for some interactive tactic `foo`.
-/
elab (name := addHintTactic) "add_hint_tactic " tac:tactic : command =>
  modifyEnv fun env => hintExtension.addEntry env tac

initialize
  Std.Linter.UnreachableTactic.ignoreTacticKindsRef.modify fun s => s.insert ``addHintTactic

/-- Report a list of tactics that can make progress against the current goal,
and for each such tactic, the number of remaining goals afterwards.
-/
def tryHint : TacticM (List (Syntax.Tactic × Nat)) := do
  let tacs ← hintExtension.getState <$> getEnv
  let l ← focus <| tacs.filterMapM fun (tac : Syntax.Tactic) => do
    let st ← saveState
    try
      let goal ← getMainGoal
      let goals ← runAndFailIfNoProgress goal (evalTactic tac)
      return some (tac, goals.length)
    catch _ =>
      return none
    finally
      restoreState st
  return l.mergeSort (fun p₁ p₂ => p₁.2 < p₂.2)

/--
`hint` lists possible tactics which will make progress (that is, not fail) against the current goal.

```lean
example {P Q : Prop} (p : P) (h : P → Q) : Q := by
  hint
  /-
  the following tactics solve the goal:
    tauto
    solve_by_elim
  -/
  solve_by_elim
```

You can add a tactic to the list that `hint` tries by using
`add_hint_tactic my_tactic`, where `my_tactic` is arbitrary `tactic` syntax.
-/
elab "hint" : tactic => do
  let hints ← tryHint
  if hints.isEmpty then throwError "no hints available"
  else
    let nl := hints.map Prod.snd |>.dedup
    let tl := nl.map fun n => (n, hints.filterMap (fun p => if p.2 == n then some p.1 else none))
    let ml := tl.map fun (n, ts) =>
      nest 2
        (joinSep
          ((if n = 0 then
              m!"the following tactics solve the goal:"
            else
              m!"the following tactics make {n} goal(s):") :: ts.map toMessageData)
          (ofFormat Format.line))
    logInfo (joinSep ml (ofFormat Format.line))

end Mathlib.Tactic.Hint
