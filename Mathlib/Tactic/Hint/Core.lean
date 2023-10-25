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

initialize hintExtension : SimplePersistentEnvExtension Syntax.Tactic (Array Syntax.Tactic) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := Array.foldl (fun a₁ a₂ => a₂ ++ a₁) #[]
  }

syntax (name := addHintTactic) "add_hint_tactic " tactic : command

/-- `add_hint_tactic t` runs the tactic `t` whenever `hint` is invoked.
The typical use case is `add_hint_tactic foo` for some interactive tactic `foo`.
-/
elab_rules : command
  | `(command| add_hint_tactic $tac:tactic) =>
    let tac : Syntax.Tactic := ⟨tac.raw.copyHeadTailInfoFrom .missing⟩
    modifyEnv fun env => hintExtension.addEntry env tac

initialize
  Std.Linter.UnreachableTactic.ignoreTacticKindsRef.modify fun s => s.insert ``addHintTactic

/-- Report a list of tactics that can make progress against the current goal,
and for each such tactic, the number of remaining goals afterwards.
-/
def tryHint : TacticM (Array (Syntax.Tactic × Nat)) := do
  let tacs ← hintExtension.getState <$> getEnv
  let a ← focus <| tacs.filterMapM fun (tac : Syntax.Tactic) => do
    let st ← saveState
    try
      let goal ← getMainGoal
      let goals ← runAndFailIfNoProgress goal (evalTactic tac)
      return some (tac, goals.length)
    catch _ =>
      return none
    finally
      restoreState st
  return a.qsort (fun p₁ p₂ => Nat.blt p₁.2 p₂.2)

/--
`hint` lists possible tactics which will make progress (that is, not fail) against the current goal.

```lean
example {P Q : Prop} (p : P) (h : P → Q) : Q := by
  hint
  /-
  Try these:
  • tauto goals: 0
  • solve_by_elim goals: 0
  -/
  solve_by_elim
```

You can add a tactic to the list that `hint` tries by using
`add_hint_tactic my_tactic`, where `my_tactic` is arbitrary `tactic` syntax.
-/
elab "hint" : tactic => do
  let hints ← tryHint
  let suggestions : Array Suggestion :=
    hints.map fun (s, n) =>
      { suggestion := s
        postInfo? := some s!" goals: {n}" }
  addSuggestions (← getRef) suggestions

end Mathlib.Tactic.Hint
