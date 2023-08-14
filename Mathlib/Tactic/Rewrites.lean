/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Util.Pickle
import Mathlib.Data.MLList.Heartbeats
import Mathlib.Lean.Meta.DiscrTree
import Mathlib.Tactic.Cache
import Mathlib.Tactic.SolveByElim
import Mathlib.Tactic.TryThis
import Mathlib.Control.Basic

/-!
# The `rewrites` tactic.

`rw?` tries to find a lemma which can rewrite the goal.

`rw?` should not be left in proofs; it is a search tool, like `apply?`.

Suggestions are printed as `rw [h]` or `rw [←h]`.

## Future work

We could try discharging side goals via `assumption` or `solve_by_elim`.

-/

namespace Mathlib.Tactic.Rewrites

open Lean Meta Std.Tactic.TryThis

initialize registerTraceClass `Tactic.rewrites
initialize registerTraceClass `Tactic.rewrites.lemmas

/-- Prepare the discrimination tree entries for a lemma. -/
def processLemma (name : Name) (constInfo : ConstantInfo) :
    MetaM (Array (Array (DiscrTree.Key true) × (Name × Bool × Nat))) := do
  if constInfo.isUnsafe then return #[]
  if ← name.isBlackListed then return #[]
  -- We now remove some injectivity lemmas which are not useful to rewrite by.
  if name matches .str _ "injEq" then return #[]
  if name matches .str _ "sizeOf_spec" then return #[]
  match name with
  | .str _ n => if n.endsWith "_inj" ∨ n.endsWith "_inj'" then return #[]
  | _ => pure ()
  let forwardWeight := 2
  let backwardWeight := 1
  withNewMCtxDepth do withReducible do
    let (_, _, type) ← forallMetaTelescopeReducing constInfo.type
    match type.getAppFnArgs with
    | (``Eq, #[_, lhs, rhs]) => do
      let lhsKey ← DiscrTree.mkPath lhs
      let rhsKey ← DiscrTree.mkPath rhs
      return #[(lhsKey, (name, false, forwardWeight * lhsKey.size)),
        (rhsKey, (name, true, backwardWeight * rhsKey.size))]
    | (``Iff, #[lhs, rhs]) => do
      let lhsKey ← DiscrTree.mkPath lhs
      let rhsKey ← DiscrTree.mkPath rhs
      return #[(lhsKey, (name, false, forwardWeight * lhsKey.size)),
        (rhsKey, (name, true, backwardWeight * rhsKey.size))]
    | _ => return #[]

/-- Insert a lemma into the discrimination tree. -/
-- Recall that `rw?` caches the discrimination tree on disk.
-- If you are modifying this file, you will probably want to delete
-- `build/lib/MathlibExtras/Rewrites.extra`
-- so that the cache is rebuilt.
def addLemma (name : Name) (constInfo : ConstantInfo)
    (lemmas : DiscrTree (Name × Bool × Nat) true) : MetaM (DiscrTree (Name × Bool × Nat) true) := do
  let mut lemmas := lemmas
  for (key, value) in ← processLemma name constInfo do
    lemmas := lemmas.insertIfSpecific key value
  return lemmas

/-- Construct the discrimination tree of all lemmas. -/
def buildDiscrTree : IO (DiscrTreeCache (Name × Bool × Nat)) :=
  DiscrTreeCache.mk "rw?: init cache" processLemma
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
    return (← findOLean `MathlibExtras.Rewrites).withExtension "extra"
  catch _ =>
    return "build" / "lib" / "MathlibExtras" / "Rewrites.extra"

initialize cachedData : CachedData (Name × Bool × Nat) ← unsafe do
  let path ← cachePath
  if (← path.pathExists) then
    let (d, r) ← unpickle (DiscrTree (Name × Bool × Nat) true) path
    return ⟨r, ← DiscrTreeCache.mk "rw?: using cache" processLemma (init := some d)⟩
  else
    return ⟨none, ← buildDiscrTree⟩

/--
Retrieve the current cache of lemmas.
-/
def rewriteLemmas : DiscrTreeCache (Name × Bool × Nat) := cachedData.cache

/-- Data structure recording a potential rewrite to report from the `rw?` tactic. -/
structure RewriteResult where
  name : Name
  symm : Bool
  weight : Nat
  result : Meta.RewriteResult
  /-- Can the new goal in `result` be closed by `with_reducible rfl`? -/
  -- This is an `Option` so that it can be computed lazily.
  rfl? : Option Bool

/-- Update a `RewriteResult` by filling in the `rfl?` field if it is currently `none`,
to reflect whether the remaining goal can be closed by `with_reducible rfl`. -/
def RewriteResult.computeRfl (r : RewriteResult) : MetaM RewriteResult := do
  if let some _ := r.rfl? then
    return r
  try
    (← mkFreshExprMVar r.result.eNew).mvarId!.rfl
    pure { r with rfl? := some true }
  catch _ =>
    pure { r with rfl? := some false }

/--
Find lemmas which can rewrite the goal.

This core function returns a monadic list, to allow the caller to decide how long to search.
See also `rewrites` for a more convenient interface.
-/
def rewritesCore (lemmas : DiscrTree (Name × Bool × Nat) s × DiscrTree (Name × Bool × Nat) s)
    (goal : MVarId) (target : Expr) : MLList MetaM RewriteResult := MLList.squash fun _ => do

  -- Get all lemmas which could match some subexpression
  let candidates := (← lemmas.1.getSubexpressionMatches target)
    ++ (← lemmas.2.getSubexpressionMatches target)

  -- Sort them by our preferring weighting
  -- (length of discriminant key, doubled for the forward implication)

  let candidates := candidates.insertionSort fun r s => r.2.2 > s.2.2

  trace[Tactic.rewrites.lemmas] m!"Candidate rewrite lemmas:\n{candidates}"

  -- Lift to a monadic list, so the caller can decide how much of the computation to run.
  let candidates := MLList.ofList candidates.toList
  pure <| candidates.filterMapM fun ⟨lem, symm, weight⟩ => do
    trace[Tactic.rewrites] "considering {if symm then "←" else ""}{lem}"
    let some result ← try? do goal.rewrite target (← mkConstWithFreshMVarLevels lem) symm
      | return none
    return if result.mvarIds.isEmpty then
      some ⟨lem, symm, weight, result, none⟩
    else
      -- TODO Perhaps allow new goals? Try closing them with solveByElim?
      none

/-- Find lemmas which can rewrite the goal. -/
def rewrites (lemmas : DiscrTree (Name × Bool × Nat) s × DiscrTree (Name × Bool × Nat) s)
    (goal : MVarId) (target : Expr) (stop_at_rfl : Bool := False) (max : Nat := 20)
    (leavePercentHeartbeats : Nat := 10) : MetaM (List RewriteResult) := do
  let results ← rewritesCore lemmas goal target
    -- Don't use too many heartbeats.
    |>.whileAtLeastHeartbeatsPercent leavePercentHeartbeats
    -- Stop if we find a rewrite after which `with_reducible rfl` would succeed.
    |>.mapM RewriteResult.computeRfl -- TODO could simply not compute this if stop_at_rfl is False
    |>.takeUpToFirst (fun r => stop_at_rfl && r.rfl? = some true)
    -- Bound the number of results.
    |>.takeAsList max
  return match results.filter (fun r => stop_at_rfl && r.rfl? = some true) with
  | [] =>
    -- TODO consider sorting the results,
    -- e.g. if we use solveByElim to fill arguments,
    -- prefer results using local hypotheses.
    results
  | results => results

open Lean.Parser.Tactic

/--
`rw?` tries to find a lemma which can rewrite the goal.

`rw?` should not be left in proofs; it is a search tool, like `apply?`.

Suggestions are printed as `rw [h]` or `rw [←h]`.
`rw?!` is the "I'm feeling lucky" mode, and will run the first rewrite it finds.
-/
syntax (name := rewrites') "rw?" "!"? (ppSpace location)? : tactic

open Elab.Tactic Elab Tactic in
elab_rules : tactic |
    `(tactic| rw?%$tk $[!%$lucky]? $[$loc]?) => do
  let lems ← rewriteLemmas.get
  reportOutOfHeartbeats `rewrites tk
  let goal ← getMainGoal
  -- TODO fix doc of core to say that * fails only if all failed
  withLocation (expandOptLocation (Lean.mkOptionalNode loc))
    fun f => do
      let some a ← f.findDecl? | return
      if a.isImplementationDetail then return
      let target ← instantiateMVars (← f.getType)
      let results ← rewrites lems goal target (stop_at_rfl := false)
      reportOutOfHeartbeats `rewrites tk
      if results.isEmpty then
        throwError "Could not find any lemmas which can rewrite the hypothesis {
          ← f.getUserName}"
      for r in results do
        addRewriteSuggestion tk [(← mkConstWithFreshMVarLevels r.name, r.symm)]
          r.result.eNew (loc? := .some (.fvar f)) (origSpan? := ← getRef)
      if lucky.isSome then
        match results[0]? with
        | some r => do
            let replaceResult ← goal.replaceLocalDecl f r.result.eNew r.result.eqProof
            replaceMainGoal (replaceResult.mvarId :: r.result.mvarIds)
        | _ => failure
    -- See https://github.com/leanprover/lean4/issues/2150
    do withMainContext do
      let target ← instantiateMVars (← goal.getType)
      let results ← rewrites lems goal target (stop_at_rfl := true)
      reportOutOfHeartbeats `rewrites tk
      if results.isEmpty then
        throwError "Could not find any lemmas which can rewrite the goal"
      for r in results do
        let newGoal := if r.rfl? = some true then Expr.lit (.strVal "no goals") else r.result.eNew
        addRewriteSuggestion tk [(← mkConstWithFreshMVarLevels r.name, r.symm)]
          newGoal (origSpan? := ← getRef)
      if lucky.isSome then
        match results[0]? with
        | some r => do
            replaceMainGoal
              ((← goal.replaceTargetEq r.result.eNew r.result.eqProof) :: r.result.mvarIds)
            evalTactic (← `(tactic| try rfl))
        | _ => failure
    (λ _ => throwError "Failed to find a rewrite for some location")

@[inherit_doc rewrites'] macro "rw?!" h:(ppSpace location)? : tactic =>
  `(tactic| rw? ! $[$h]?)
@[inherit_doc rewrites'] macro "rw!?" h:(ppSpace location)? : tactic =>
  `(tactic| rw? ! $[$h]?)
