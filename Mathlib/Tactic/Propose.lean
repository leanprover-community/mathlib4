/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Lean.Expr.Basic
import Mathlib.Lean.Meta
import Mathlib.Lean.Meta.Basic
import Mathlib.Lean.Meta.DiscrTree
import Mathlib.Tactic.Cache
import Mathlib.Tactic.Core
import Mathlib.Tactic.SolveByElim
import Mathlib.Tactic.TryThis

/-!
# Propose

This file defines a tactic `have? using a, b, c`
that tries to find a lemma which makes use of each of the local hypotheses `a, b, c`.

The variant `have? : t using a, b, c` restricts to lemmas with type `t` (which may contain `_`).

Note that in either variant `have?` does not look at the current goal at all.
It is a relative of `apply?` but for *forward reasoning* (i.e. looking at the hypotheses)
rather than backward reasoning.

```
import Std.Data.List.Basic
import Mathlib.Tactic.Propose

example (K L M : List α) (w : L.Disjoint M) (m : K ⊆ L) : True := by
  have? using w, m -- Try this: `List.disjoint_of_subset_left m w`
  trivial
```
-/

set_option autoImplicit true

namespace Mathlib.Tactic.Propose

open Lean Meta Std.Tactic.TryThis

initialize registerTraceClass `Tactic.propose

initialize proposeLemmas : DeclCache (DiscrTree Name true) ←
  DeclCache.mk "have?: init cache" {} fun name constInfo lemmas => do
    if constInfo.isUnsafe then return lemmas
    if ← name.isBlackListed then return lemmas
    withNewMCtxDepth do withReducible do
      let (mvars, _, _) ← forallMetaTelescope constInfo.type
      let mut lemmas := lemmas
      for m in mvars do
        lemmas := lemmas.insertIfSpecific (← DiscrTree.mkPath (← inferType m)) name
      pure lemmas

/-- Shortcut for calling `solveByElim`. -/
def solveByElim (orig : MVarId) (goals : Array MVarId) (use : Array Expr) (required : Array Expr)
    (depth) := do
  let cfg : SolveByElim.Config := { maxDepth := depth, exfalso := true, symm := true }
  let cfg := if !required.isEmpty then
    cfg.testSolutions (fun _ => do
    let r ← instantiateMVars (.mvar orig)
    pure <| required.all fun e => e.occurs r)
  else
    cfg
  let cfg := cfg.synthInstance
  _ ← SolveByElim.solveByElim cfg (use.toList.map pure) (pure (← getLocalHyps).toList) goals.toList

/--
Attempts to find lemmas which use all of the `required` expressions as arguments, and
can be unified with the given `type` (which may contain metavariables, which we avoid assigning).
We look up candidate lemmas from a discrimination tree using the first such expression.

Returns an array of pairs, containing the names of found lemmas and the resulting application.
-/
def propose (lemmas : DiscrTree Name s) (type : Expr) (required : Array Expr)
    (solveByElimDepth := 15) : MetaM (Array (Name × Expr)) := do
  guard !required.isEmpty
  let ty ← whnfR (← instantiateMVars (← inferType required[0]!))
  let candidates ← lemmas.getMatch ty
  candidates.filterMapM fun lem : Name =>
    try
      trace[Tactic.propose] "considering {lem}"
      let Expr.mvar g ← mkFreshExprMVar type | failure
      let e ← mkConstWithFreshMVarLevels lem
      let (args, _, _) ← forallMetaTelescope (← inferType e)
      let .true ← preservingMCtx <| withAssignableSyntheticOpaque <|
        isDefEq type (← inferType (mkAppN e args)) | failure
      g.assign (mkAppN e args)
      let use := required.filterMap fun e => match e with | .fvar _ => none | _ => some e
      solveByElim g (args.map fun a => a.mvarId!) use required solveByElimDepth
      trace[Tactic.propose] "successfully filled in arguments for {lem}"
      pure <| some (lem, ← instantiateMVars (.mvar g))
    catch _ => pure none

open Lean.Parser.Tactic

/--
* `have? using a, b, c` tries to find a lemma
which makes use of each of the local hypotheses `a, b, c`,
and reports any results via trace messages.
* `have? : h using a, b, c` only returns lemmas whose type matches `h` (which may contain `_`).
* `have?! using a, b, c` will also call `have` to add results to the local goal state.

Note that `have?` (unlike `apply?`) does not inspect the goal at all,
only the types of the lemmas in the `using` clause.

`have?` should not be left in proofs; it is a search tool, like `apply?`.

Suggestions are printed as `have := f a b c`.
-/
syntax (name := propose') "have?" "!"? (" : " term)? " using " (colGt term),+ : tactic

open Elab.Tactic Elab Tactic in
elab_rules : tactic
  | `(tactic| have?%$tk $[!%$lucky]? $[ : $type:term]? using $[$terms:term],*) => do
    let stx ← getRef
    let goal ← getMainGoal
    goal.withContext do
      let required ← terms.mapM (elabTerm · none)
      let type ← match type with
      | some stx => elabTermWithHoles stx none (← getMainTag) true <&> (·.1)
      | none => mkFreshTypeMVar
      let proposals ← propose (← proposeLemmas.get) type required
      if proposals.isEmpty then
        throwError "propose could not find any lemmas using the given hypotheses"
      -- TODO we should have `proposals` return a lazy list, to avoid unnecessary computation here.
      for p in proposals.toList.take 10 do
        addHaveSuggestion tk (← inferType p.2) p.2 stx
      if lucky.isSome then
        let mut g := goal
        for p in proposals.toList.take 10 do
          (_, g) ← g.let p.1 p.2
        replaceMainGoal [g]

@[inherit_doc propose'] syntax "have?!" (" : " term)? " using " (colGt term),+ : tactic
@[inherit_doc propose'] syntax "have!?" (" : " term)? " using " (colGt term),+ : tactic
macro_rules
  | `(tactic| have?!%$tk $[: $type]? using $terms,*) =>
    `(tactic| have?%$tk ! $[: $type]? using $terms,*)
  | `(tactic| have!?%$tk $[: $type]? using $terms,*) =>
    `(tactic| have?%$tk ! $[: $type]? using $terms,*)
