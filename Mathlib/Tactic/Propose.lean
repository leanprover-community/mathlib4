/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Scott Morrison
-/
import Std.Tactic.TryThis
import Mathlib.Lean.Expr.Basic
import Mathlib.Lean.Meta
import Mathlib.Tactic.Cache
import Mathlib.Tactic.Core
import Mathlib.Tactic.SolveByElim

/-!
# Library search

This file defines a tactic `library_search`
and a term elaborator `library_search%`
that tries to find a lemma
solving the current goal
(subgoals are solved using `solveByElim`).

```
example : x < x + 1 := library_search%
example : Nat := by library_search
```
-/

namespace Lean.Meta.DiscrTree

def insertIfSpecific {α : Type} {s : Bool} [BEq α] (d : DiscrTree α s)
    (keys : Array (DiscrTree.Key s)) (v : α) : DiscrTree α s :=
  if keys == #[Key.star] || keys == #[Key.const `Eq 3, Key.star, Key.star, Key.star] then
    d
  else
    d.insertCore keys v

end Lean.Meta.DiscrTree

namespace Mathlib.Tactic.Propose

open Lean Meta Std.Tactic.TryThis

initialize registerTraceClass `Tactic.propose

-- from Lean.Server.Completion
private def isBlackListed (declName : Name) : MetaM Bool := do
  if declName == ``sorryAx then return true
  if declName matches .str _ "inj" then return true
  if declName matches .str _ "noConfusionType" then return true
  let env ← getEnv
  pure $ declName.isInternal'
   || isAuxRecursor env declName
   || isNoConfusion env declName
  <||> isRec declName <||> isMatcher declName

initialize proposeLemmas : DeclCache (DiscrTree Name true) ←
  DeclCache.mk "librarySearch: init cache" {} fun name constInfo lemmas => do
    if constInfo.isUnsafe then return lemmas
    if ← isBlackListed name then return lemmas
    withNewMCtxDepth do withReducible do
      let (mvars, _, _) ← forallMetaTelescope constInfo.type
      let mut lemmas := lemmas
      for m in mvars do
        lemmas := lemmas.insertIfSpecific (← DiscrTree.mkPath (← inferType m)) name
      pure lemmas

/-- Shortcut for calling `solveByElim`. -/
def solveByElim (orig : MVarId) (goals : Array MVarId) (use : List Expr) (required : List Expr) (depth) := do
  let cfg : SolveByElim.Config := { maxDepth := depth, exfalso := true, symm := true }
  let test : MetaM Bool := do
    let r ← instantiateMVars (.mvar orig)
    pure <| required.all fun e => e.occurs r
  let cfg := if !required.isEmpty then cfg.testSolutions (fun _ => test) else cfg
  _ ← SolveByElim.solveByElim cfg (use.map pure) (pure (← getLocalHyps).toList) goals.toList

def propose (goal : MVarId) (lemmas : DiscrTree Name s) (required : List Expr)
    (hyp : FVarId) (solveByElimDepth := 15) : MetaM (Array (Name × Expr)) := goal.withContext do
  let ty ← whnfR (← instantiateMVars (← hyp.getDecl).type)
  let candidates ← lemmas.getMatch ty
  candidates.filterMapM fun lem : Name => do
    try
      let Expr.mvar g ← mkFreshExprMVar (← mkFreshTypeMVar) | failure
      let e ← mkConstWithFreshMVarLevels lem
      let (args, _, _) ← forallMetaTelescope (← inferType e)
      g.assign (mkAppN e args)
      solveByElim g (args.map fun a => a.mvarId!) [] required solveByElimDepth
      pure <| some (lem, ← instantiateMVars (.mvar g))
    catch _ => pure none

open Lean.Parser.Tactic

syntax (name := propose') "propose" (" using " (colGt term)) : tactic

open Elab.Tactic Elab Tactic in
elab_rules : tactic | `(tactic| propose using $hyp:ident) => do
  let goal ← getMainGoal
  goal.withContext do
    let fvar ← getFVarId hyp
    let required := [.fvar fvar]
    let proposals ← propose goal (← proposeLemmas.get) required fvar
    let mut g := goal
    for p in proposals.toList.take 10 do
      (_, g) ← g.let p.1 p.2
    replaceMainGoal [g]
