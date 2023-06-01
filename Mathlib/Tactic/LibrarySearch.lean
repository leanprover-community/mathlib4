/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Scott Morrison
-/
import Mathlib.Tactic.TryThis
import Mathlib.Util.Pickle
import Mathlib.Lean.Expr.Basic
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
initialize registerTraceClass `Tactic.librarySearch.lemmas

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
deriving DecidableEq, Ord

instance : ToString DeclMod where
  toString m := match m with | .none => "" | .symm => "symm" | .mp => "mp" | .mpr => "mpr"

/-- Prepare the discrimination tree entries for a lemma. -/
def processLemma (name : Name) (constInfo : ConstantInfo) :
    MetaM (Array (Array (DiscrTree.Key true) × (Name × DeclMod))) := do
  if constInfo.isUnsafe then return #[]
  if ← name.isBlackListed then return #[]
  withNewMCtxDepth do withReducible do
    let (_, _, type) ← forallMetaTelescope constInfo.type
    let keys ← DiscrTree.mkPath type
    let mut r := #[(keys, (name, .none))]
    match type.getAppFnArgs with
    | (``Eq, #[_, lhs, rhs]) => do
      let keys_symm ← DiscrTree.mkPath (← mkEq rhs lhs)
      return r.push (keys_symm, (name, .symm))
    | (``Iff, #[lhs, rhs]) => do
      let keys_mp ← DiscrTree.mkPath rhs
      let keys_mpr ← DiscrTree.mkPath lhs
      return r.push (keys_mp, (name, .mp)) |>.push (keys_mpr, (name, .mpr))
    | _ => return r

/-- Insert a lemma into the discrimination tree. -/
-- Recall that `library_search` caches the discrimination tree on disk.
-- If you are modifying this file, you will probably want to delete
-- `build/lib/MathlibExtras/LibrarySearch.extra`
-- so that the cache is rebuilt.
def addLemma (name : Name) (constInfo : ConstantInfo)
    (lemmas : DiscrTree (Name × DeclMod) true) : MetaM (DiscrTree (Name × DeclMod) true) := do
  let mut lemmas := lemmas
  for (key, value) in ← processLemma name constInfo do
    lemmas := lemmas.insertIfSpecific key value
  return lemmas

/-- Construct the discrimination tree of all lemmas. -/
def buildDiscrTree : IO (DiscrTreeCache (Name × DeclMod)) :=
  DiscrTreeCache.mk "librarySearch: init cache" processLemma
    -- Sort so lemmas with longest names come first.
    -- This is counter-intuitive, but the way that `DiscrTree.getMatch` returns results
    -- means that the results come in "batches", with more specific matches *later*.
    -- Thus we're going to call reverse on the result of `DiscrTree.getMatch`,
    -- so if we want to try lemmas with shorter names first,
    -- we need to put them into the `DiscrTree` backwards.
    (post? := some fun A =>
      A.map (fun (n, m) => (n.toString.length, n, m)) |>.qsort (fun p q => p.1 > q.1) |>.map (·.2))

open System (FilePath)

def cachePath : IO FilePath :=
  try
    return (← findOLean `MathlibExtras.LibrarySearch).withExtension "extra"
  catch _ =>
    return "build" / "lib" / "MathlibExtras" / "LibrarySearch.extra"

initialize cachedData : CachedData (Name × DeclMod) ← unsafe do
  let path ← cachePath
  if (← path.pathExists) then
    let (d, r) ← unpickle (DiscrTree (Name × DeclMod) true) path
    return ⟨r, ← DiscrTreeCache.mk "librarySearch: using cache" processLemma (init := some d)⟩
  else
    return ⟨none, ← buildDiscrTree⟩

/--
Retrieve the current current of lemmas.
-/
def librarySearchLemmas : DiscrTreeCache (Name × DeclMod) := cachedData.cache

/-- Shortcut for calling `solveByElim`. -/
def solveByElim (goals : List MVarId) (required : List Expr) (exfalso := false) (depth) := do
  -- There is only a marginal decrease in performance for using the `symm` option for `solveByElim`.
  -- (measured via `lake build && time lake env lean test/librarySearch.lean`).
  let cfg : SolveByElim.Config :=
    { maxDepth := depth, exfalso := exfalso, symm := true, commitIndependentGoals := true }
  let cfg := if !required.isEmpty then cfg.requireUsingAll required else cfg
  SolveByElim.solveByElim.processSyntax cfg false false [] [] #[] goals

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
      let subgoals ← solveByElim newGoals required (exfalso := false) (depth := solveByElimDepth)
      pure (← getMCtx, subgoals)
    catch _ =>
      pure (← getMCtx, newGoals)

/--
Returns a lazy list of the results of applying a library lemma,
then calling `solveByElim` on the resulting goals.
-/
def librarySearchCore (goal : MVarId)
    (required : List Expr) (solveByElimDepth := 6) : ListM MetaM (MetavarContext × List MVarId) :=
  .squash do
    let ty ← goal.getType
    let lemmas := (← librarySearchLemmas.getMatch ty).toList
    trace[Tactic.librarySearch.lemmas] m!"Candidate library_search lemmas:\n{lemmas}"
    return (ListM.ofList lemmas).filterMapM fun (lem, mod) =>
      try? <| librarySearchLemma lem mod required solveByElimDepth goal

/-- A type synonym for our subgoal ranking algorithm. -/
def subgoalRankType : Type := Bool × Nat × Int
  deriving ToString

instance : Ord subgoalRankType :=
  have : Ord (Nat × Int) := lexOrd
  lexOrd

/-- Returns a tuple:
* are there no remaining goals?
* how many local hypotheses were used?
* how many goals remain, negated?

Larger values (i.e. no remaining goals, more local hypotheses, fewer remaining goals)
are better.
-/
def subgoalRanking (goal : MVarId) (subgoals : List MVarId) : MetaM subgoalRankType := do
  return (subgoals.isEmpty, ← countLocalHypsUsed (.mvar goal), - subgoals.length)

/-- Sort the incomplete results from `library_search` according to
* the number of local hypotheses used (the more the better) and
* the number of remaining subgoals (the fewer the better).
-/
def sortResults (goal : MVarId) (R : Array (MetavarContext × List MVarId)) :
    MetaM (Array (MetavarContext × List MVarId)) := do
  let R' ← R.mapM fun (ctx, gs) => do
    return (← withMCtx ctx (subgoalRanking goal gs), ctx, gs)
  let R'' := R'.qsort fun a b => compare a.1 b.1 = Ordering.gt
  return R''.map (·.2)

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
def librarySearch (goal : MVarId) (required : List Expr)
    (solveByElimDepth := 6) : MetaM (Option (Array (MetavarContext × List MVarId))) := do
  let librarySearchEmoji := fun
    | .error _ => bombEmoji
    | .ok (some _) => crossEmoji
    | .ok none => checkEmoji
  withTraceNode `Tactic.librarySearch (return m!"{librarySearchEmoji ·} {← goal.getType}") do
  profileitM Exception "librarySearch" (← getOptions) do
  (do
    _ ← solveByElim [goal] required (exfalso := true) (depth := solveByElimDepth)
    return none) <|>
  (do
    let results ← librarySearchCore goal required solveByElimDepth
      -- Don't use too many heartbeats.
      |>.whileAtLeastHeartbeatsPercent 10
      -- Stop if we find something that closes the goal
      |>.takeUpToFirst (·.2.isEmpty)
      |>.asArray
    match results.find? (·.2.isEmpty) with
    | none => return (← sortResults goal results)
    | some (ctx, _) => do
      setMCtx ctx
      return none)

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
    if let some suggestions ← librarySearch goal required then
      reportOutOfHeartbeats `library_search tk
      for suggestion in suggestions do
        withMCtx suggestion.1 do
          addExactSuggestion tk (← instantiateMVars (mkMVar mvar)).headBeta (addSubgoalsMsg := true)
      if suggestions.isEmpty then logError "library_search didn't find any relevant lemmas"
      admitGoal goal
    else
      addExactSuggestion tk (← instantiateMVars (mkMVar mvar)).headBeta

open Elab Term in
elab tk:"library_search%" : term <= expectedType => do
  let goal ← mkFreshExprMVar expectedType
  let (_, introdGoal) ← goal.mvarId!.intros
  introdGoal.withContext do
    if let some suggestions ← librarySearch introdGoal [] then
      reportOutOfHeartbeats `library_search tk
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
    if let some _ ← librarySearch goal [] then
      reportOutOfHeartbeats `library_search tk
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
