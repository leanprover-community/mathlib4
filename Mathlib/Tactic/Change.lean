/-
Copyright (c) 2023 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Lean.Elab.Tactic.ElabTerm

/-!

# Tactic `change? _`

This tactic is used to replace the goal with a definitionally equal one.
The `_` is a general term and is intended to be used to guide which unfolding you want
Lean to perform.
-/

/--  `change? term?` unifies the optional `term?` with the current goal, defaulting to the
goal, if `term?` is not present.
It then prints in the infoView the unified term.
This is useful to replace the main goal after a `dsimp`.
```lean
example : (fun x : Nat => x) 0 = 1 := by
  change? 0 = _  -- `change 0 = 1`
```
-/
syntax "change?" (ppSpace colGt term)? : tactic

open Lean Meta Elab.Tactic in
elab_rules : tactic
| `(tactic| change? $[$h]?) => do
  let expr := ← match h with
    | none => getMainTarget
    | some ex => do
      let ex := ← elabTerm ex none
      let defeq? := ← isDefEq ex (← getMainTarget)
      if ! defeq? then throwError "The given term is not DefEq to the goal"
      instantiateMVars ex
  logInfo m!"change {expr}"
