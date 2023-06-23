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
  /- the following tactics make progress:
       solve_by_elim
       finish
       tauto
  -/
  solve_by_elim
```

You can add a tactic to the list that `hint` tries by using
`add_hint_tactic my_tactic`, specifying a string which works as an tactic.
-/
elab "hint" : tactic => do
  let hints ← tryHint
  if hints.isEmpty then throwError "no hints available"
  else
    let (ts, tp) := hints.partitionMap fun (t, n) => if n = 0 then Sum.inl t else Sum.inr t
    let ms := if ts.isEmpty then [] else
      [nest 2
        (joinSep (m!"the following tactics solve the goal:" :: ts.map toMessageData)
          (ofFormat Format.line))]
    let mp := if tp.isEmpty then [] else
      [nest 2
        (joinSep (m!"the following tactics make progress:" :: tp.map toMessageData)
          (ofFormat Format.line))]
    logInfo (joinSep (ms ++ mp) (ofFormat Format.line))

end Mathlib.Tactic.Hint
