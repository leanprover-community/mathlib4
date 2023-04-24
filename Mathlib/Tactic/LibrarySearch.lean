/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Scott Morrison
-/
import Mathlib.Tactic.TryThis
import Mathlib.Lean.Expr.Basic
import Mathlib.Lean.Meta.DiscrTree
import Mathlib.Tactic.Cache
import Mathlib.Tactic.Core
import Mathlib.Tactic.SolveByElim
import Mathlib.Data.ListM.Heartbeats
import Mathlib.Control.Basic

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

namespace Mathlib.Tactic.LibrarySearch

open Lean Meta Std.Tactic.TryThis

initialize registerTraceClass `Tactic.librarySearch

/--
A "modifier" for a declaration.
* `none` indicates the original declaration,
* `symm` indicates that (possibly after binders) the declaration is an `=`,
  and we want to consider the symmetric version,
* `mp` indicates that (possibly after binders) the declaration is an `iff`,
  and we want to consider the forward direction,
* `mpr` similarly, but for the backward direction.
-/
inductive DeclMod
| none | symm | mp | mpr
deriving DecidableEq

initialize librarySearchLemmas : DeclCache (DiscrTree (Name × DeclMod) true) ←
  DeclCache.mk "librarySearch: init cache" {} fun name constInfo lemmas => do
    if constInfo.isUnsafe then return lemmas
    if ← name.isBlackListed then return lemmas
    withNewMCtxDepth do withReducible do
      let (_, _, type) ← forallMetaTelescopeReducing constInfo.type
      let keys ← DiscrTree.mkPath type
      let lemmas := lemmas.insertIfSpecific keys (name, .none)
      match type.getAppFnArgs with
      | (``Eq, #[_, lhs, rhs]) => do
        let keys_symm ← DiscrTree.mkPath (← mkEq rhs lhs)
        pure (lemmas.insertIfSpecific keys_symm (name, .symm))
      | (``Iff, #[lhs, rhs]) => do
        let keys_mp ← DiscrTree.mkPath rhs
        let keys_mpr ← DiscrTree.mkPath lhs
        pure <| (lemmas.insertIfSpecific keys_mp (name, .mp)).insertIfSpecific keys_mpr (name, .mpr)
      | _ => pure lemmas

/-- Shortcut for calling `solveByElim`. -/
def solveByElim (goals : List MVarId) (required : List Expr) (depth) := do
  -- There is only a marginal decrease in performance for using the `symm` and `exfalso`
  -- options for `solveByElim`.
  -- (measured via `lake build && time lake env lean test/librarySearch.lean`).
  let cfg : SolveByElim.Config := { maxDepth := depth, exfalso := true, symm := true }
  let cfg := if !required.isEmpty then cfg.requireUsingAll required else cfg
  _ ← SolveByElim.solveByElim.processSyntax cfg false false [] [] #[] goals

/--
Try applying the given lemma (with symmetry modifer) to the goal,
then try to close subsequent goals using `solveByElim`.
If `solveByElim` succeeds, we return `[]` as the list of new subgoals,
otherwise the full list of subgoals.

We do not allow the `MetavarContext` to be modified.
Instead, if the lemma application succeeds we collect the resulting `MetavarContext`
and return it explicitly.
-/
def librarySearchLemma (lem : Name) (mod : DeclMod) (required : List Expr) (solveByElimDepth := 6)
    (goal : MVarId) : MetaM (MetavarContext × List MVarId) :=
  withTraceNode `Tactic.librarySearch (return m!"{·.emoji} trying {lem}") do
  withoutModifyingState do
    let lem ← mkConstWithFreshMVarLevels lem
    let lem ← match mod with
    | .none => pure lem
    | .symm => mapForallTelescope (fun e => mkAppM ``Eq.symm #[e]) lem
    | .mp => mapForallTelescope (fun e => mkAppM ``Iff.mp #[e]) lem
    | .mpr => mapForallTelescope (fun e => mkAppM ``Iff.mpr #[e]) lem
    let newGoals ← goal.apply lem
    try
      solveByElim newGoals required solveByElimDepth
      pure (← getMCtx, [])
    catch _ =>
      pure (← getMCtx, newGoals)

/--
Returns a lazy list of the results of applying a library lemma,
then calling `solveByElim` on the resulting goals.
-/
def librarySearchCore (goal : MVarId) (lemmas : DiscrTree (Name × DeclMod) s)
    (required : List Expr) (solveByElimDepth := 6) : ListM MetaM (MetavarContext × List MVarId) :=
  .squash do
    let ty ← goal.getType
    let lemmas := ListM.ofList ((← lemmas.getMatch ty).toList)
    return lemmas.filterMapM fun (lem, mod) =>
      try? <| librarySearchLemma lem mod required solveByElimDepth goal

/--
Try to solve the goal either by:
* calling `solveByElim`
* or applying a library lemma then calling `solveByElim` on the resulting goals.

If it successfully closes the goal, returns `none`.
Otherwise, it returns `some a`, where `a : Array (MetavarContext × List MVarId)`,
with an entry for each library lemma which was successfully applied,
containing the metavariable context after the application, and a list of the subsidiary goals.

(Always succeeds, and the metavariable context stored in the monad is reverted,
unless the goal was completely solved.)

(Note that if `solveByElim` solves some but not all subsidiary goals,
this is not currently tracked.)
-/
def librarySearch (goal : MVarId) (lemmas : DiscrTree (Name × DeclMod) s) (required : List Expr)
    (solveByElimDepth := 6) : MetaM (Option (Array (MetavarContext × List MVarId))) := do
  let librarySearchEmoji := fun
    | .error _ => bombEmoji
    | .ok (some _) => crossEmoji
    | .ok none => checkEmoji
  withTraceNode `Tactic.librarySearch (return m!"{librarySearchEmoji ·} {← goal.getType}") do
  profileitM Exception "librarySearch" (← getOptions) do
  (do
    solveByElim [goal] required solveByElimDepth
    return none) <|>
  (do
    let results ← librarySearchCore goal lemmas required solveByElimDepth
      -- Don't use too many heartbeats.
      |>.whileAtLeastHeartbeatsPercent 10
      -- Stop if we find something that closes the goal
      |>.takeUpToFirst (·.2.isEmpty)
      |>.asArray
    match results.find? (·.2.isEmpty) with
    | none => return results
    | some (ctx, _) => do
      setMCtx ctx
      return none)

/-- Log a message if it looks like we ran out of time. -/
def reportOutOfHeartbeats (stx : Syntax) : MetaM Unit := do
  if (← heartbeatsPercent) ≥ 90 then
    logInfoAt stx ("`library_search` stopped because it was running out of time.\n" ++
      "You may get better results using `set_option maxHeartbeats 0`.")

open Lean.Parser.Tactic

-- TODO: implement the additional options for `library_search` from Lean 3,
-- in particular including additional lemmas
-- with `library_search [X, Y, Z]` or `library_search with attr`.
syntax (name := librarySearch') "library_search" (config)? (simpArgs)?
  (" using " (colGt term),+)? : tactic
syntax (name := librarySearch!) "library_search!" (config)? (simpArgs)?
  (" using " (colGt term),+)? : tactic

-- For now we only implement the basic functionality.
-- The full syntax is recognized, but will produce a "Tactic has not been implemented" error.

open Elab.Tactic Elab Tactic in
elab_rules : tactic | `(tactic| library_search%$tk $[using $[$required:term],*]?) => do
  let mvar ← getMainGoal
  let (_, goal) ← (← getMainGoal).intros
  goal.withContext do
    let required := (← (required.getD #[]).mapM getFVarId).toList.map .fvar
    if let some suggestions ← librarySearch goal (← librarySearchLemmas.get) required then
      reportOutOfHeartbeats tk
      for suggestion in suggestions do
        withMCtx suggestion.1 do
          addExactSuggestion tk (← instantiateMVars (mkMVar mvar)).headBeta
      if suggestions.isEmpty then logError "library_search didn't find any relevant lemmas"
      admitGoal goal
    else
      addExactSuggestion tk (← instantiateMVars (mkMVar mvar)).headBeta

open Elab Term in
elab tk:"library_search%" : term <= expectedType => do
  let goal ← mkFreshExprMVar expectedType
  let (_, introdGoal) ← goal.mvarId!.intros
  introdGoal.withContext do
    if let some suggestions ← librarySearch introdGoal (← librarySearchLemmas.get) [] then
      reportOutOfHeartbeats tk
      for suggestion in suggestions do
        withMCtx suggestion.1 do
          addTermSuggestion tk (← instantiateMVars goal).headBeta
      if suggestions.isEmpty then logError "library_search didn't find any relevant lemmas"
      mkSorry expectedType (synthetic := true)
    else
      addTermSuggestion tk (← instantiateMVars goal).headBeta
      instantiateMVars goal

/-- `observe hp : p` asserts the proposition `p`, and tries to prove it using `library_search`.
If no proof is found, the tactic fails.
In other words, this tactic is equivalent to `have hp : p := by library_search`.

If `hp` is omitted, then the placeholder `this` is used.

The variant `observe? hp : p` will emit a trace message of the form `have hp : p := proof_term`.
This may be particularly useful to speed up proofs. -/
syntax (name := observe) "observe" "?"? (ident)? ":" term (" using " (colGt term),+)? : tactic

open Elab.Tactic Elab Tactic in
elab_rules : tactic |
  `(tactic| observe%$tk $[?%$trace]? $[$n?:ident]? : $t:term $[using $[$required:term],*]?) => do
  let name : Name := match n? with
    | none   => `this
    | some n => n.getId
  withMainContext do
    let (type, _) ← elabTermWithHoles t none (← getMainTag) true
    let .mvar goal ← mkFreshExprMVar type | failure
    if let some _ ← librarySearch goal (← librarySearchLemmas.get) [] then
      reportOutOfHeartbeats tk
      throwError "observe did not find a solution"
    else
      let v := (← instantiateMVars (mkMVar goal)).headBeta
      if trace.isSome then
        -- TODO: we should be allowed to pass an identifier to `addHaveSuggestion`.
        addHaveSuggestion tk type v
      let (_, newGoal) ← (← getMainGoal).note name v
      replaceMainGoal [newGoal]

@[inherit_doc observe] macro "observe?" h:(ident)? ":" t:term : tactic =>
  `(tactic| observe ? $[$h]? : $t)

@[inherit_doc observe]
macro "observe?" h:(ident)? ":" t:term " using " terms:(colGt term),+ : tactic =>
  `(tactic| observe ? $[$h]? : $t using $[$terms],*)
