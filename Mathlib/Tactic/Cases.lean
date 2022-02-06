/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean
import Mathlib.Tactic.OpenPrivate
import Mathlib.Data.List.Defs

/-!

# Backward compatible implementation of lean 3 `cases` tactic

This tactic is similar to the `cases` tactic in lean 4 core, but the syntax for giving
names is different:

```
example (h : p ∨ q) : q ∨ p := by
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

example (h : p ∨ q) : q ∨ p := by
  cases' h with hp hq
  · exact Or.inr hp
  · exact Or.inl hq

example (h : p ∨ q) : q ∨ p := by
  rcases h with hp | hq
  · exact Or.inr hp
  · exact Or.inl hq
```

Prefer `cases` or `rcases` when possible, because these tactics promote structured proofs.
-/

namespace Lean.Parser.Tactic
open Meta Elab.Tactic

open private getElimNameInfo getAltNumFields in evalCases ElimApp.evalAlts.go in
elab (name := cases') "cases' " tgts:(casesTarget,+) usingArg:(" using " ident)?
  withArg:(" with " (colGt binderIdent)+)? : tactic => do
  let targets ← elabCasesTargets tgts.getSepArgs
  let (elimName, elimInfo) ← getElimNameInfo usingArg targets (induction := false)
  let g ← getMainGoal
  withMVarContext g do
    let targets ← addImplicitTargets elimInfo targets
    let result ← withRef tgts <| ElimApp.mkElimApp elimName elimInfo targets (← getMVarTag g)
    let elimArgs := result.elimApp.getAppArgs
    let targets ← elimInfo.targetsPos.mapM (instantiateMVars elimArgs[·])
    let motive := elimArgs[elimInfo.motivePos]
    let g ← generalizeTargetsEq g (← inferType motive) targets
    let (targetsNew, g) ← introN g targets.size
    withMVarContext g do
      ElimApp.setMotiveArg g motive.mvarId! targetsNew
      assignExprMVar g result.elimApp
      let mut names := if withArg.isNone then [] else
        withArg[1].getArgs.map (getNameOfIdent' ·[0]) |>.toList
      let mut subgoals := #[]
      for (altName, g) in result.alts do
        let numFields ← getAltNumFields elimInfo altName
        let (altVarNames, names') := names.splitAtD numFields `_
        names := names'
        let (_, g) ← introN g numFields altVarNames
        let some (g, _) ← Cases.unifyEqs targets.size g {} | pure ()
        subgoals := subgoals.push g
      setGoals subgoals.toList
