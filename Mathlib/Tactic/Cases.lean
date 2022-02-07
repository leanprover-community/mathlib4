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
open Meta Elab Elab.Tactic

open private getAltNumFields in evalCases ElimApp.evalAlts.go in
def ElimApp.evalNames (elimInfo : ElimInfo) (alts : Array (Name × MVarId)) (withArg : Syntax)
    (numEqs := 0) (numGeneralized := 0) (toClear : Array FVarId := #[]) :
    TermElabM (Array MVarId) := do
  let mut names := if withArg.isNone then [] else
    withArg[1].getArgs.map (getNameOfIdent' ·[0]) |>.toList
  let mut subgoals := #[]
  for (altName, g) in alts do
    let numFields ← getAltNumFields elimInfo altName
    let (altVarNames, names') := names.splitAtD numFields `_
    names := names'
    let (_, g) ← introN g numFields altVarNames
    let some (g, _) ← Cases.unifyEqs numEqs g {} | pure ()
    let (_, g) ← introNP g numGeneralized
    let g ← liftM $ toClear.foldlM tryClear g
    subgoals := subgoals.push g
  pure subgoals

open private getElimNameInfo generalizeTargets generalizeVars in evalInduction in
elab (name := induction') tk:"induction' " tgts:(casesTarget,+)
    usingArg:(" using " ident)?
    withArg:(" with " (colGt binderIdent)+)?
    genArg:(" generalizing " (colGt ident)+)? : tactic => do
  let targets ← elabCasesTargets tgts.getSepArgs
  let (elimName, elimInfo) ← getElimNameInfo usingArg targets (induction := true)
  let g ← getMainGoal
  withMVarContext g do
    let targets ← addImplicitTargets elimInfo targets
    evalInduction.checkTargets targets
    let targetFVarIds := targets.map (·.fvarId!)
    withMVarContext g do
      let genArgs ← if genArg.isNone then pure #[] else getFVarIds genArg[1].getArgs
      let forbidden ← mkGeneralizationForbiddenSet targets
      let mut s ← getFVarSetToGeneralize targets forbidden
      for v in genArgs do
        if forbidden.contains v then
          throwError "variable cannot be generalized because target depends on it{indentExpr (mkFVar v)}"
        if s.contains v then
          throwError "unnecessary 'generalizing' argument, variable '{mkFVar v}' is generalized automatically"
        s := s.insert v
      let (fvarIds, g) ← Meta.revert g (← sortFVarIds s.toArray)
      let result ← withRef tgts <| ElimApp.mkElimApp elimName elimInfo targets (← getMVarTag g)
      let elimArgs := result.elimApp.getAppArgs
      ElimApp.setMotiveArg g elimArgs[elimInfo.motivePos].mvarId! targetFVarIds
      assignExprMVar g result.elimApp
      let subgoals ← ElimApp.evalNames elimInfo result.alts withArg
        (numGeneralized := fvarIds.size) (toClear := targetFVarIds)
      setGoals (subgoals ++ result.others).toList

open private getElimNameInfo in evalCases in
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
      let subgoals ← ElimApp.evalNames elimInfo result.alts withArg
         (numEqs := targets.size) (toClear := targetsNew)
      setGoals subgoals.toList
