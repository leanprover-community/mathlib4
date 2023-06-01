/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Util.Pickle
import Mathlib.Data.ListM.Heartbeats
import Mathlib.Lean.Meta.DiscrTree
import Mathlib.Tactic.Cache
import Mathlib.Tactic.SolveByElim
import Mathlib.Tactic.TryThis
import Mathlib.Control.Basic

/-!
# The `rewrites` tactic.

`rewrites` tries to find a lemma which can rewrite the goal.

`rewrites` should not be left in proofs; it is a search tool, like `library_search`.

Suggestions are printed as `rw [h]` or `rw [←h]`.

## Future work
It would be nice to have `rewrites at h`.

We could also try discharging side goals via `assumption` or `solve_by_elim`.

-/

namespace Mathlib.Tactic.Rewrites

open Lean Meta Std.Tactic.TryThis

initialize registerTraceClass `Tactic.rewrites

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
-- Recall that `rewrites` caches the discrimination tree on disk.
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
  DiscrTreeCache.mk "rewrites: init cache" processLemma
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
    return ⟨r, ← DiscrTreeCache.mk "rewrites: using cache" processLemma (init := some d)⟩
  else
    return ⟨none, ← buildDiscrTree⟩

/--
Retrieve the current cache of lemmas.
-/
def rewriteLemmas : DiscrTreeCache (Name × Bool × Nat) := cachedData.cache

/-- Data structure recording a potential rewrite to report from the `rewrites` tactic. -/
structure RewriteResult where
  name : Name
  symm : Bool
  weight : Nat
  result : Meta.RewriteResult
  /-- Can the new goal in `result` be closed by `with_reducible rfl`? -/
  -- This is an `Option` so that it can be computed lazily.
  refl? : Option Bool

/-- Update a `RewriteResult` by filling in the `refl?` field if it is currently `none`,
to reflect whether the remaining goal can be closed by `with_reducible rfl`. -/
def RewriteResult.computeRefl (r : RewriteResult) : MetaM RewriteResult := do
  if let some _ := r.refl? then
    return r
  try
    (← mkFreshExprMVar r.result.eNew).mvarId!.refl
    pure { r with refl? := some true }
  catch _ =>
    pure { r with refl? := some false }

/--
Find lemmas which can rewrite the goal.

This core function returns a monadic list, to allow the caller to decide how long to search.
See also `rewrites` for a more convenient interface.
-/
def rewritesCore (lemmas : DiscrTree (Name × Bool × Nat) s × DiscrTree (Name × Bool × Nat) s)
    (goal : MVarId) : ListM MetaM RewriteResult := ListM.squash do
  let type ← instantiateMVars (← goal.getType)

  -- Get all lemmas which could match some subexpression
  -- DiscrTree.getSubexpressionMatches
  let candidates := (← lemmas.1.getSubexpressionMatches type)
    ++ (← lemmas.2.getSubexpressionMatches type)

  -- TODO the sort used below should be optimized.
  -- Remember also that the discrimination tree returns most specific results last,
  -- so simply reversing might be sufficient.

  -- Sort them by our preferring weighting
  -- (length of discriminant key, doubled for the forward implication)

  -- let candidates := candidates.insertionSort fun r s => r.2.2 > s.2.2
  -- Lift to a monadic list, so the caller can decide how much of the computation to run.
  let candidates := ListM.ofList candidates.toList
  pure <| candidates.filterMapM fun ⟨lem, symm, weight⟩ => do
    trace[Tactic.rewrites] "considering {if symm then "←" else ""}{lem}"
    let result ← try
      goal.rewrite type (← mkConstWithFreshMVarLevels lem) symm
    catch _ => return none
    return if result.mvarIds.isEmpty then
      some ⟨lem, symm, weight, result, none⟩
    else
      -- TODO Perhaps allow new goals? Try closing them with solveByElim?
      none

/-- Find lemmas which can rewrite the goal. -/
def rewrites (lemmas : DiscrTree (Name × Bool × Nat) s × DiscrTree (Name × Bool × Nat) s)
    (goal : MVarId) (max : Nat := 10) (leavePercentHeartbeats : Nat := 10) :
    MetaM (List RewriteResult) :=
rewritesCore lemmas goal
  -- Don't use too many heartbeats.
  |>.whileAtLeastHeartbeatsPercent leavePercentHeartbeats
  -- Stop if we find a rewrite after which `with_reducible rfl` would succeed.
  |>.mapM RewriteResult.computeRefl
  |>.takeUpToFirst (fun r => r.refl? = some true)
  -- Bound the number of results.
  |>.takeAsList max
  -- TODO consider sorting the successful results,
  -- e.g. if we use solveByElim to fill arguments,
  -- prefer results using local hypotheses.

open Lean.Parser.Tactic

/--
`rewrites` tries to find a lemma which can rewrite the goal.

`rewrites` should not be left in proofs; it is a search tool, like `library_search`.

Suggestions are printed as `rw [h]` or `rw [←h]`.
`rewrites!` is the "I'm feeling lucky" mode, and will run the first rewrite it finds.
-/
syntax (name := rewrites') "rewrites" "!"? : tactic

open Elab.Tactic Elab Tactic in
elab_rules : tactic |
    `(tactic| rewrites%$tk $[!%$lucky]?) => do
  let goal ← getMainGoal
  goal.withContext do
    let results ← rewrites (← rewriteLemmas.get) goal
    reportOutOfHeartbeats `rewrites tk
    if results.isEmpty then
      throwError "rewrites could not find any lemmas which can rewrite the goal"
    for r in results do
      let newGoal := if r.refl? = some true then Expr.lit (.strVal "no goals") else r.result.eNew
      addRewriteSuggestion tk (← mkConstWithFreshMVarLevels r.name) r.symm newGoal
    if lucky.isSome then
      match results[0]? with
      | some r => do
          replaceMainGoal
            ((← goal.replaceTargetEq r.result.eNew r.result.eqProof) :: r.result.mvarIds)
          evalTactic (← `(tactic| rfl))
      | _ => failure

@[inherit_doc rewrites'] macro "rewrites!" : tactic =>
  `(tactic| rewrites !)
