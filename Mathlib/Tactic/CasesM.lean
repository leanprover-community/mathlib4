/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean

/-!
# `casesm` and `cases_type` tactics

These tactics implement repeated `cases` on anything satisfying a predicate.
-/

namespace Mathlib.Tactic
open Lean Meta Elab Tactic

/--
Core tactic for `casesm` and `cases_type`. Calls `cases` on all fvars in `g` for which
`matcher ldecl.type` returns true.
* `recursive`: if true, it calls itself repeatedly on the resulting subgoals
* `allowSplit`: if false, it will skip any hypotheses where `cases` returns more than one subgoal.
-/
partial def casesMatching (g : MVarId) (matcher : Expr → MetaM Bool)
    (recursive := false) (allowSplit := true) : MetaM (List MVarId) := return (← go g).toList where
  /-- Auxiliary for `casesMatching`. Accumulates generated subgoals in `acc`. -/
  go (g : MVarId) (acc : Array MVarId := #[]) : MetaM (Array MVarId) :=
    g.withContext do
      for ldecl in ← getLCtx do
        if ← matcher ldecl.type then
          let mut acc := acc
          let subgoals ← if allowSplit then
            g.cases ldecl.fvarId
          else
            let s ← saveState
            let subgoals ← g.cases ldecl.fvarId
            if subgoals.size > 1 then
              s.restore
              continue
            else
              pure subgoals
          for subgoal in subgoals do
            if recursive then
              acc ← go subgoal.mvarId acc
            else
              acc := acc.push subgoal.mvarId
          return acc
      return (acc.push g)

/--
* `casesm p` applies the `cases` tactic to a hypothesis `h : type`
  if `type` matches the pattern `p`.
* `casesm p_1, ..., p_n` applies the `cases` tactic to a hypothesis `h : type`
  if `type` matches one of the given patterns.
* `casesm* p` is a more efficient and compact version of `· repeat casesm p`.
  It is more efficient because the pattern is compiled once.

Example: The following tactic destructs all conjunctions and disjunctions in the current context.
```
casesm* _ ∨ _, _ ∧ _
```
-/
elab (name := casesM) "casesm" recursive:"*"? ppSpace pats:term,+ : tactic => do
  let patterns ←
    withTheReader Term.Context (fun ctx => { ctx with ignoreTCFailures := true }) <|
    Term.withoutErrToSorry <|
    pats.getElems.mapM fun p => Term.withoutModifyingElabMetaStateWithInfo do
      withRef p <| abstractMVars (← Term.elabTerm p none)
  let matcher ty := patterns.anyM fun p =>
    return (← Conv.matchPattern? p ty) matches some (_, #[])
  liftMetaTactic (casesMatching · matcher recursive.isSome)

/-- Common implementation of `cases_type` and `cases_type!`. -/
def elabCasesType (heads : Array Ident)
    (recursive := false) (allowSplit := true) : TacticM Unit := do
  let heads ← heads.mapM resolveGlobalConstNoOverloadWithInfo
  let matcher ty := pure <|
    if let .const n .. := ty.headBeta.getAppFn then heads.contains n else false
  liftMetaTactic (casesMatching · matcher recursive allowSplit)

/--
* `cases_type I` applies the `cases` tactic to a hypothesis `h : (I ...)`
* `cases_type I_1 ... I_n` applies the `cases` tactic to a hypothesis
  `h : (I_1 ...)` or ... or `h : (I_n ...)`
* `cases_type* I` is shorthand for `· repeat cases_type I`
* `cases_type! I` only applies `cases` if the number of resulting subgoals is <= 1.

Example: The following tactic destructs all conjunctions and disjunctions in the current goal.
```
cases_type* Or And
```
-/
elab (name := casesType) "cases_type" recursive:"*"? ppSpace heads:(colGt ident)+ : tactic =>
  elabCasesType heads recursive.isSome true

@[inheritDoc casesType]
elab (name := casesType!) "cases_type!" recursive:"*"? ppSpace heads:(colGt ident)+ : tactic =>
  elabCasesType heads recursive.isSome false
