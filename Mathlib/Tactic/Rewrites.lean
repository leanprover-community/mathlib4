/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Std.Util.Pickle
import Std.Data.MLList.Heartbeats
import Mathlib.Data.MLList.Dedup
import Mathlib.Lean.Meta.DiscrTree
import Mathlib.Tactic.Cache
import Mathlib.Lean.Meta
import Mathlib.Tactic.Relation.Rfl
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

set_option autoImplicit true

namespace Mathlib.Tactic.Rewrites

open Lean Meta Std.Tactic.TryThis

initialize registerTraceClass `Tactic.rewrites
initialize registerTraceClass `Tactic.rewrites.lemmas

/-- Weight to multiply the "specificity" of a rewrite lemma by when rewriting forwards. -/
def forwardWeight := 2
/-- Weight to multiply the "specificity" of a rewrite lemma by when rewriting backwards. -/
def backwardWeight := 1

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
  withNewMCtxDepth do withReducible do
    let (_, _, type) ← forallMetaTelescopeReducing constInfo.type
    match type.getAppFnArgs with
    | (``Eq, #[_, lhs, rhs])
    | (``Iff, #[lhs, rhs]) => do
      let lhsKey ← DiscrTree.mkPath lhs
      let rhsKey ← DiscrTree.mkPath rhs
      return #[(lhsKey, (name, false, forwardWeight * lhsKey.size)),
        (rhsKey, (name, true, backwardWeight * rhsKey.size))]
    | _ => return #[]

/-- Select `=` and `↔` local hypotheses. -/
def localHypotheses (except : List FVarId := []) : MetaM (Array (Expr × Bool × Nat)) := do
  let r ← getLocalHyps
  let mut result := #[]
  for h in r do
    if except.contains h.fvarId! then continue
    let (_, _, type) ← forallMetaTelescopeReducing (← inferType h)
    match type.getAppFnArgs with
    | (``Eq, #[_, lhs, rhs])
    | (``Iff, #[lhs, rhs]) => do
      let lhsKey : Array (DiscrTree.Key true) ← DiscrTree.mkPath lhs
      let rhsKey : Array (DiscrTree.Key true) ← DiscrTree.mkPath rhs
      result := result.push (h, false, forwardWeight * lhsKey.size)
        |>.push (h, true, backwardWeight * rhsKey.size)
    | _ => pure ()
  return result

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
  /-- The lemma we rewrote by.
  This is `Expr`, not just a `Name`, as it may be a local hypothesis. -/
  expr : Expr
  /-- `True` if we rewrote backwards (i.e. with `rw [← h]`). -/
  symm : Bool
  /-- The "weight" of the rewrite. This is calculated based on how specific the rewrite rule was. -/
  weight : Nat
  /-- The result from the `rw` tactic. -/
  result : Meta.RewriteResult
  /-- Can the new goal in `result` be closed by `with_reducible rfl`? -/
  -- This is an `Option` so that it can be computed lazily.
  rfl? : Option Bool
  /-- The metavariable context after the rewrite.
  This needs to be stored as part of the result so we can backtrack the state. -/
  mctx : MetavarContext

/-- Update a `RewriteResult` by filling in the `rfl?` field if it is currently `none`,
to reflect whether the remaining goal can be closed by `with_reducible rfl`. -/
def RewriteResult.computeRfl (r : RewriteResult) : MetaM RewriteResult := do
  if let some _ := r.rfl? then
    return r
  try
    withoutModifyingState <| withMCtx r.mctx do
      -- We use `withReducible` here to follow the behaviour of `rw`.
      withReducible (← mkFreshExprMVar r.result.eNew).mvarId!.rfl
      -- We do not need to record the updated `MetavarContext` here.
      pure { r with rfl? := some true }
  catch _ =>
    pure { r with rfl? := some false }

/--
Find lemmas which can rewrite the goal.

This core function returns a monadic list, to allow the caller to decide how long to search.
See also `rewrites` for a more convenient interface.
-/
-- We need to supply the current `MetavarContext` (which will be reused for each lemma application)
-- because `MLList.squash` executes lazily,
-- so there is no opportunity for `← getMCtx` to record the context at the call site.
def rewritesCore (hyps : Array (Expr × Bool × Nat))
    (lemmas : DiscrTree (Name × Bool × Nat) s × DiscrTree (Name × Bool × Nat) s)
    (ctx : MetavarContext) (goal : MVarId) (target : Expr) :
    MLList MetaM RewriteResult := MLList.squash fun _ => do
  -- Get all lemmas which could match some subexpression
  let candidates := (← lemmas.1.getSubexpressionMatches target)
    ++ (← lemmas.2.getSubexpressionMatches target)

  -- Sort them by our preferring weighting
  -- (length of discriminant key, doubled for the forward implication)
  let candidates := candidates.insertionSort fun r s => r.2.2 > s.2.2

  -- Now deduplicate. We can't use `Array.deduplicateSorted` as we haven't completely sorted,
  -- and in fact want to keep some of the residual ordering from the discrimination tree.
  let mut forward : NameSet := ∅
  let mut backward : NameSet := ∅
  let mut deduped := #[]
  for (l, s, w) in candidates do
    if s then
      if ¬ backward.contains l then
        deduped := deduped.push (l, s, w)
        backward := backward.insert l
    else
      if ¬ forward.contains l then
        deduped := deduped.push (l, s, w)
        forward := forward.insert l

  trace[Tactic.rewrites.lemmas] m!"Candidate rewrite lemmas:\n{deduped}"

  -- Lift to a monadic list, so the caller can decide how much of the computation to run.
  let hyps := MLList.ofArray <| hyps.map fun ⟨hyp, symm, weight⟩ => (Sum.inl hyp, symm, weight)
  let lemmas := MLList.ofArray <| deduped.map fun ⟨lem, symm, weight⟩ => (Sum.inr lem, symm, weight)

  pure <| (hyps |>.append fun _ => lemmas).filterMapM fun ⟨lem, symm, weight⟩ => withMCtx ctx do
    let some expr ← (match lem with
    | .inl hyp => pure (some hyp)
    | .inr lem => try? <| mkConstWithFreshMVarLevels lem) | return none
    trace[Tactic.rewrites] m!"considering {if symm then "←" else ""}{expr}"
    let some result ← try? do goal.rewrite target expr symm
      | return none
    return if result.mvarIds.isEmpty then
      some ⟨expr, symm, weight, result, none, ← getMCtx⟩
    else
      -- TODO Perhaps allow new goals? Try closing them with solveByElim?
      -- A challenge is knowing what suggestions to print if we do so!
      none

/-- Find lemmas which can rewrite the goal. -/
def rewrites (hyps : Array (Expr × Bool × Nat))
    (lemmas : DiscrTree (Name × Bool × Nat) s × DiscrTree (Name × Bool × Nat) s)
    (goal : MVarId) (target : Expr) (stopAtRfl : Bool := false) (max : Nat := 20)
    (leavePercentHeartbeats : Nat := 10) : MetaM (List RewriteResult) := do
  let results ← rewritesCore hyps lemmas (← getMCtx) goal target
    -- Don't report duplicate results.
    -- (TODO: we later pretty print results; save them here?)
    -- (TODO: a config flag to disable this,
    -- if distinct-but-pretty-print-the-same results are desirable?)
    |>.dedupBy (fun r => do pure <| (← ppExpr r.result.eNew).pretty)
    -- Stop if we find a rewrite after which `with_reducible rfl` would succeed.
    |>.mapM RewriteResult.computeRfl -- TODO could simply not compute this if `stopAtRfl` is False
    |>.takeUpToFirst (fun r => stopAtRfl && r.rfl? = some true)
    -- Don't use too many heartbeats.
    |>.whileAtLeastHeartbeatsPercent leavePercentHeartbeats
    -- Bound the number of results.
    |>.takeAsList max
  return match results.filter (fun r => stopAtRfl && r.rfl? = some true) with
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
-/
syntax (name := rewrites') "rw?" (ppSpace location)? : tactic

open Elab.Tactic Elab Tactic in
elab_rules : tactic |
    `(tactic| rw?%$tk $[$loc]?) => do
  let lems ← rewriteLemmas.get
  reportOutOfHeartbeats `rewrites tk
  let goal ← getMainGoal
  -- TODO fix doc of core to say that * fails only if all failed
  withLocation (expandOptLocation (Lean.mkOptionalNode loc))
    fun f => do
      let some a ← f.findDecl? | return
      if a.isImplementationDetail then return
      let target ← instantiateMVars (← f.getType)
      let hyps ← localHypotheses (except := [f])
      let results ← rewrites hyps lems goal target (stopAtRfl := false)
      reportOutOfHeartbeats `rewrites tk
      if results.isEmpty then
        throwError "Could not find any lemmas which can rewrite the hypothesis {
          ← f.getUserName}"
      for r in results do withMCtx r.mctx do
        addRewriteSuggestion tk [(r.expr, r.symm)]
          r.result.eNew (loc? := .some (.fvar f)) (origSpan? := ← getRef)
      if let some r := results[0]? then
        setMCtx r.mctx
        let replaceResult ← goal.replaceLocalDecl f r.result.eNew r.result.eqProof
        replaceMainGoal (replaceResult.mvarId :: r.result.mvarIds)
    -- See https://github.com/leanprover/lean4/issues/2150
    do withMainContext do
      let target ← instantiateMVars (← goal.getType)
      let hyps ← localHypotheses
      let results ← rewrites hyps lems goal target (stopAtRfl := true)
      reportOutOfHeartbeats `rewrites tk
      if results.isEmpty then
        throwError "Could not find any lemmas which can rewrite the goal"
      for r in results do withMCtx r.mctx do
        let newGoal := if r.rfl? = some true then Expr.lit (.strVal "no goals") else r.result.eNew
        addRewriteSuggestion tk [(r.expr, r.symm)]
          newGoal (origSpan? := ← getRef)
      if let some r := results[0]? then
        setMCtx r.mctx
        replaceMainGoal
          ((← goal.replaceTargetEq r.result.eNew r.result.eqProof) :: r.result.mvarIds)
        evalTactic (← `(tactic| try rfl))
    (fun _ => throwError "Failed to find a rewrite for some location")
