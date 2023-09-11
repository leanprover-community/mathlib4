/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Scott Morrison
-/
import Std.Tactic.TryThis
import Mathlib.Lean.Expr.Basic
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

/--
Inserts a new key into a discrimination tree,
but only if it is not of the form `#[*]` or `#[=, *, *, *]`.
-/
def insertIfSpecific {α : Type} {s : Bool} [BEq α] (d : DiscrTree α s)
    (keys : Array (DiscrTree.Key s)) (v : α) : DiscrTree α s :=
  if keys == #[Key.star] || keys == #[Key.const `Eq 3, Key.star, Key.star, Key.star] then
    d
  else
    d.insertCore keys v

end Lean.Meta.DiscrTree

namespace Mathlib.Tactic.LibrarySearch

open Lean Meta Std.Tactic.TryThis

initialize registerTraceClass `Tactic.librarySearch

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
    if ← isBlackListed name then return lemmas
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
    (solveByElimDepth := 6) : MetaM <| Option (Array <| MetavarContext × List MVarId) := do
  profileitM Exception "librarySearch" (← getOptions) do
  let ty ← goal.getType
  withTraceNode `Tactic.librarySearch (return m!"{exceptOptionEmoji ·} {ty}") do

  let mut suggestions := #[]

  let state0 ← get

  try
    solveByElim [goal] required solveByElimDepth
    return none
  catch _ =>
    set state0

  for (lem, mod) in ← lemmas.getMatch ty do
    trace[Tactic.librarySearch] "{lem}"
    let result ← withTraceNode `Tactic.librarySearch (return m!"{exceptOptionEmoji ·} trying {lem}")
      try
        let lem ← mkConstWithFreshMVarLevels lem
        let lem ← match mod with
        | .none => pure lem
        | .symm => mapForallTelescope (fun e => mkAppM ``Eq.symm #[e]) lem
        | .mp => mapForallTelescope (fun e => mkAppM ``Iff.mp #[e]) lem
        | .mpr => mapForallTelescope (fun e => mkAppM ``Iff.mpr #[e]) lem
        let newGoals ← goal.apply lem
        (try
          for newGoal in newGoals do
            trace[Tactic.librarySearch] "proving {← addMessageContextFull (mkMVar newGoal)}"
          solveByElim newGoals required solveByElimDepth
          pure $ some $ Sum.inr ()
        catch _ =>
          let res := some $ Sum.inl (← getMCtx, newGoals)
          set state0
          return res)
    catch _ =>
      set state0
      pure none
    match result with
    | none => pure ()
    | some (Sum.inr ()) => return none
    | some (Sum.inl suggestion) => suggestions := suggestions.push suggestion

  pure $ some suggestions

def lines (ls : List MessageData) :=
  MessageData.joinSep ls (MessageData.ofFormat Format.line)

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
      for suggestion in suggestions do
        withMCtx suggestion.1 do
          addExactSuggestion tk (← instantiateMVars (mkMVar mvar)).headBeta
      admitGoal goal
    else
      addExactSuggestion tk (← instantiateMVars (mkMVar mvar)).headBeta

open Elab Term in
elab tk:"library_search%" : term <= expectedType => do
  let goal ← mkFreshExprMVar expectedType
  let (_, introdGoal) ← goal.mvarId!.intros
  introdGoal.withContext do
    if let some suggestions ← librarySearch introdGoal (← librarySearchLemmas.get) [] then
      for suggestion in suggestions do
        withMCtx suggestion.1 do
          addTermSuggestion tk (← instantiateMVars goal).headBeta
      mkSorry expectedType (synthetic := true)
    else
      addTermSuggestion tk (← instantiateMVars goal).headBeta
      instantiateMVars goal
