/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Scott Morrison
-/
import Std.Util.Pickle
import Std.Util.Cache
import Mathlib.Tactic.SolveByElim
import Std.Data.MLList.Heartbeats
import Mathlib.Lean.Name

/-!
# Library search

This file defines tactics `exact?` and `apply?`,
(formerly known as `library_search`)
and a term elaborator `exact?%`
that tries to find a lemma
solving the current goal
(subgoals are solved using `solveByElim`).

```
example : x < x + 1 := exact?%
example : Nat := by exact?
```
-/

namespace Mathlib.Tactic.LibrarySearch

open Lean Meta Std.Tactic TryThis

initialize registerTraceClass `Tactic.librarySearch
initialize registerTraceClass `Tactic.librarySearch.lemmas

/-- Configuration for `DiscrTree`. -/
def discrTreeConfig : WhnfCoreConfig := {}

/--
A "modifier" for a declaration.
* `none` indicates the original declaration,
* `mp` indicates that (possibly after binders) the declaration is an `↔`,
  and we want to consider the forward direction,
* `mpr` similarly, but for the backward direction.
-/
inductive DeclMod
  | none | mp | mpr
deriving DecidableEq, Ord

instance : ToString DeclMod where
  toString m := match m with | .none => "" | .mp => "mp" | .mpr => "mpr"

/-- Prepare the discrimination tree entries for a lemma. -/
def processLemma (name : Name) (constInfo : ConstantInfo) :
    MetaM (Array (Array DiscrTree.Key × (Name × DeclMod))) := do
  if constInfo.isUnsafe then return #[]
  if ← name.isBlackListed then return #[]
  withNewMCtxDepth do withReducible do
    let (_, _, type) ← forallMetaTelescope constInfo.type
    let keys ← DiscrTree.mkPath type discrTreeConfig
    let mut r := #[(keys, (name, .none))]
    match type.getAppFnArgs with
    | (``Iff, #[lhs, rhs]) => do
      return r.push (← DiscrTree.mkPath rhs discrTreeConfig, (name, .mp))
        |>.push (← DiscrTree.mkPath lhs discrTreeConfig, (name, .mpr))
    | _ => return r

/-- Insert a lemma into the discrimination tree. -/
-- Recall that `apply?` caches the discrimination tree on disk.
-- If you are modifying this file, you will probably want to delete
-- `build/lib/MathlibExtras/LibrarySearch.extra`
-- so that the cache is rebuilt.
def addLemma (name : Name) (constInfo : ConstantInfo)
    (lemmas : DiscrTree (Name × DeclMod)) : MetaM (DiscrTree (Name × DeclMod)) := do
  let mut lemmas := lemmas
  for (key, value) in ← processLemma name constInfo do
    lemmas := lemmas.insertIfSpecific key value discrTreeConfig
  return lemmas

/-- Construct the discrimination tree of all lemmas. -/
def buildDiscrTree : IO (DiscrTreeCache (Name × DeclMod)) :=
  DiscrTreeCache.mk "apply?: init cache" processLemma
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

/--
Retrieve the current current of lemmas.
-/
initialize librarySearchLemmas : DiscrTreeCache (Name × DeclMod) ← unsafe do
  let path ← cachePath
  if (← path.pathExists) then
    let (d, _r) ← unpickle (DiscrTree (Name × DeclMod)) path
    -- We can drop the `CompactedRegion` value; we do not plan to free it
    DiscrTreeCache.mk "apply?: using cache" processLemma (init := some d)
  else
    buildDiscrTree

/-- Shortcut for calling `solveByElim`. -/
def solveByElim (goals : List MVarId) (required : List Expr) (exfalso := false) (depth) := do
  -- There is only a marginal decrease in performance for using the `symm` option for `solveByElim`.
  -- (measured via `lake build && time lake env lean test/librarySearch.lean`).
  let cfg : SolveByElim.Config :=
    { maxDepth := depth, exfalso := exfalso, symm := true, commitIndependentGoals := true }
  let cfg := if !required.isEmpty then cfg.requireUsingAll required else cfg
  SolveByElim.solveByElim.processSyntax cfg false false [] [] #[] goals

/--
Try applying the given lemma (with symmetry modifier) to the goal,
then try to close subsequent goals using `solveByElim`.
If `solveByElim` succeeds, we return `[]` as the list of new subgoals,
otherwise the full list of subgoals.
-/
def librarySearchLemma (lem : Name) (mod : DeclMod) (required : List Expr) (solveByElimDepth := 6)
    (goal : MVarId) : MetaM (List MVarId) :=
  withTraceNode `Tactic.librarySearch (return m!"{·.emoji} trying {lem}") do
    let lem ← mkConstWithFreshMVarLevels lem
    let lem ← match mod with
    | .none => pure lem
    | .mp => mapForallTelescope (fun e => mkAppM ``Iff.mp #[e]) lem
    | .mpr => mapForallTelescope (fun e => mkAppM ``Iff.mpr #[e]) lem
    let newGoals ← goal.apply lem { allowSynthFailures := true }
    try
      let subgoals ← solveByElim newGoals required (exfalso := false) (depth := solveByElimDepth)
      pure subgoals
    catch _ =>
      if required.isEmpty then
        pure newGoals
      else
        failure

/--
Returns a lazy list of the results of applying a library lemma,
then calling `solveByElim` on the resulting goals.
-/
def librarySearchCore (goal : MVarId)
    (required : List Expr) (solveByElimDepth := 6) : Nondet MetaM (List MVarId) :=
  .squash fun _ => do
    let ty ← goal.getType
    let lemmas := (← librarySearchLemmas.getMatch ty).toList
    trace[Tactic.librarySearch.lemmas] m!"Candidate library_search lemmas:\n{lemmas}"
    return (Nondet.ofList lemmas).filterMapM fun (lem, mod) =>
      observing? <| librarySearchLemma lem mod required solveByElimDepth goal

/--
Run `librarySearchCore` on both the goal and `symm` applied to the goal.
-/
def librarySearchSymm (goal : MVarId)
    (required : List Expr) (solveByElimDepth := 6) :
    Nondet MetaM (List MVarId) :=
  (librarySearchCore goal required solveByElimDepth) <|>
  .squash fun _ => do
    if let some symm ← observing? goal.applySymm then
      return librarySearchCore symm required solveByElimDepth
    else
      return .nil

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

/-- Sort the incomplete results from `librarySearchCore` according to
* the number of local hypotheses used (the more the better) and
* the number of remaining subgoals (the fewer the better).
-/
def sortResults (goal : MVarId) (R : Array (List MVarId × MetavarContext)) :
    MetaM (Array (List MVarId × MetavarContext)) := do
  let R' ← R.mapM fun (gs, ctx) => do
    return (← withMCtx ctx (subgoalRanking goal gs), gs, ctx)
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
    (solveByElimDepth := 6) (leavePercentHeartbeats : Nat := 10) :
    MetaM (Option (Array (List MVarId × MetavarContext))) := do
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
    let results ← librarySearchSymm goal required solveByElimDepth
      |>.mapM (fun x => do pure (x, ← getMCtx))
      |>.toMLList'
      -- Don't use too many heartbeats.
      |>.whileAtLeastHeartbeatsPercent leavePercentHeartbeats
      -- Stop if we find something that closes the goal
      |>.takeUpToFirst (·.1.isEmpty)
      |>.asArray
    match results.find? (·.1.isEmpty) with
    | none => return (← sortResults goal results)
    | some (_, ctx) => do
      setMCtx ctx
      return none)

open Lean.Parser.Tactic

-- TODO: implement the additional options for `library_search` from Lean 3,
-- in particular including additional lemmas
-- with `exact? [X, Y, Z]` or `exact? with attr`.
syntax (name := exact?') "exact?" (config)? (simpArgs)?
  (" using " (colGt term),+)? : tactic
syntax (name := exact?!) "exact?!" (config)? (simpArgs)?
  (" using " (colGt term),+)? : tactic
syntax (name := exact!?) "exact!?" (config)? (simpArgs)?
  (" using " (colGt term),+)? : tactic

syntax (name := apply?') "apply?" (config)? (simpArgs)?
  (" using " (colGt term),+)? : tactic

-- For now we only implement the basic functionality.
-- The full syntax is recognized, but will produce a "Tactic has not been implemented" error.

open Elab.Tactic Elab Tactic

def exact? (tk : Syntax) (required : Option (Array (TSyntax `term))) (requireClose : Bool) :
    TacticM Unit := do
  let mvar ← getMainGoal
  let (_, goal) ← (← getMainGoal).intros
  goal.withContext do
    let required := (← (required.getD #[]).mapM getFVarId).toList.map .fvar
    if let some suggestions ← librarySearch goal required then
      if requireClose then
        throwError "`exact?` could not close the goal. Try `apply?` to see partial suggestions."
      reportOutOfHeartbeats `library_search tk
      for suggestion in suggestions do
        withMCtx suggestion.2 do
          addExactSuggestion tk (← instantiateMVars (mkMVar mvar)).headBeta (addSubgoalsMsg := true)
      if suggestions.isEmpty then logError "apply? didn't find any relevant lemmas"
      admitGoal goal
    else
      addExactSuggestion tk (← instantiateMVars (mkMVar mvar)).headBeta

elab_rules : tactic | `(tactic| exact? $[using $[$required],*]?) => do
  exact? (← getRef) required true

elab_rules : tactic | `(tactic| apply? $[using $[$required],*]?) => do
  exact? (← getRef) required false

elab tk:"library_search" : tactic => do
  logWarning ("`library_search` has been renamed to `apply?`" ++
    " (or `exact?` if you only want solutions closing the goal)")
  exact? tk none false

open Elab Term in
elab tk:"exact?%" : term <= expectedType => do
  let goal ← mkFreshExprMVar expectedType
  let (_, introdGoal) ← goal.mvarId!.intros
  introdGoal.withContext do
    if let some suggestions ← librarySearch introdGoal [] then
      reportOutOfHeartbeats `library_search tk
      for suggestion in suggestions do
        withMCtx suggestion.2 do
          addTermSuggestion tk (← instantiateMVars goal).headBeta
      if suggestions.isEmpty then logError "exact? didn't find any relevant lemmas"
      mkSorry expectedType (synthetic := true)
    else
      addTermSuggestion tk (← instantiateMVars goal).headBeta
      instantiateMVars goal
