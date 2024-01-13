/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Std.Util.Pickle
import Std.Data.MLList.Heartbeats
import Std.Tactic.Relation.Rfl
import Mathlib.Data.MLList.Dedup
import Mathlib.Lean.Meta.DiscrTree
import Std.Util.Cache
import Mathlib.Lean.Meta
import Mathlib.Tactic.TryThis
import Mathlib.Control.Basic
import Mathlib.Tactic.SolveByElim

/-!
# The `rewrites` tactic.

`rw?` tries to find a lemma which can rewrite the goal.

`rw?` should not be left in proofs; it is a search tool, like `apply?`.

Suggestions are printed as `rw [h]` or `rw [← h]`.

-/

set_option autoImplicit true

namespace Lean.Meta

/-- Extract the lemma, with arguments, that was used to produce a `RewriteResult`. -/
-- This assumes that `r.eqProof` was constructed as:
-- `mkAppN (mkConst ``Eq.ndrec [u1, u2]) #[α, a, motive, h₁, b, h₂]`
-- and we want `h₂`.
def RewriteResult.by? (r : RewriteResult) : Option Expr :=
  if r.eqProof.isAppOfArity ``Eq.ndrec 6 then
    r.eqProof.getArg! 5
  else
    none

end Lean.Meta

namespace Mathlib.Tactic.Rewrites

open Lean Meta Std.Tactic TryThis

initialize registerTraceClass `Tactic.rewrites
initialize registerTraceClass `Tactic.rewrites.lemmas

/-- Weight to multiply the "specificity" of a rewrite lemma by when rewriting forwards. -/
def forwardWeight := 2
/-- Weight to multiply the "specificity" of a rewrite lemma by when rewriting backwards. -/
def backwardWeight := 1

/-- Configuration for `DiscrTree`. -/
def discrTreeConfig : WhnfCoreConfig := {}

open Lean.Meta.DiscrTree (keysSpecific)

/-- Prepare the discrimination tree entries for a lemma. -/
def processLemma (name : Name) (constInfo : ConstantInfo) :
    MetaM (Array (Array DiscrTree.Key × (Name × Bool × Nat))) := do
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
      let lhsKey ← DiscrTree.mkPath lhs discrTreeConfig
      let rhsKey ← DiscrTree.mkPath rhs discrTreeConfig
      return #[(lhsKey, (name, false, forwardWeight * lhsKey.size)),
        (rhsKey, (name, true, backwardWeight * rhsKey.size))].filter fun t => keysSpecific t.1
    | _ => return #[]

/-- Select `=` and `↔` local hypotheses. -/
def localHypotheses (except : List FVarId := []) : MetaM (Array (Expr × Bool × Nat)) := do
  let r ← getLocalHyps
  let mut result := #[]
  for h in r do
    if except.contains h.fvarId! then continue
    let (_, _, type) ← forallMetaTelescopeReducing (← inferType h)
    let type ← whnfR type
    match type.getAppFnArgs with
    | (``Eq, #[_, lhs, rhs])
    | (``Iff, #[lhs, rhs]) => do
      let lhsKey : Array DiscrTree.Key ← DiscrTree.mkPath lhs discrTreeConfig
      let rhsKey : Array DiscrTree.Key ← DiscrTree.mkPath rhs discrTreeConfig
      result := result.push (h, false, forwardWeight * lhsKey.size)
        |>.push (h, true, backwardWeight * rhsKey.size)
    | _ => pure ()
  return result

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
    return ".lake" / "build" / "lib" / "MathlibExtras" / "Rewrites.extra"

/--
Retrieve the current cache of lemmas.
-/
initialize rewriteLemmas : DiscrTreeCache (Name × Bool × Nat) ← unsafe do
  let path ← cachePath
  if (← path.pathExists) then
    -- We can drop the `CompactedRegion` value from `unpickle`; we do not plan to free it
    let d := (·.1) <$> unpickle (DiscrTree (Name × Bool × Nat)) path
    DiscrTreeCache.mk "rw?: using cache" processLemma (init := d)
  else
    buildDiscrTree

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
  /-- Pretty-printed result. -/
  -- This is an `Option` so that it can be computed lazily.
  ppResult? : Option String
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
      withReducible (← mkFreshExprMVar r.result.eNew).mvarId!.applyRfl
      -- We do not need to record the updated `MetavarContext` here.
      pure { r with rfl? := some true }
  catch _ =>
    pure { r with rfl? := some false }

/-- Pretty print the result of the rewrite, and store it for later use. -/
def RewriteResult.prepare_ppResult (r : RewriteResult) : MetaM RewriteResult := do
  if let some _ := r.ppResult? then
    return r
  else
    return { r with ppResult? := some ((← ppExpr r.result.eNew).pretty) }

/--
Pretty print the result of the rewrite.
If this will be done more than once you should use `prepare_ppResult`
-/
def RewriteResult.ppResult (r : RewriteResult) : MetaM String :=
  if let some pp := r.ppResult? then
    return pp
  else
    return (← ppExpr r.result.eNew).pretty

/-- Shortcut for calling `solveByElim`. -/
def solveByElim (goals : List MVarId) (depth : Nat := 6) : MetaM PUnit := do
  -- There is only a marginal decrease in performance for using the `symm` option for `solveByElim`.
  -- (measured via `lake build && time lake env lean test/librarySearch.lean`).
  let cfg : SolveByElim.Config :=
    { maxDepth := depth, exfalso := false, symm := true }
  let [] ← SolveByElim.solveByElim.processSyntax cfg false false [] [] #[] goals
    | failure

/-- Should we try discharging side conditions? If so, using `assumption`, or `solve_by_elim`? -/
inductive SideConditions
| none
| assumption
| solveByElim

/--
Find lemmas which can rewrite the goal.

This core function returns a monadic list, to allow the caller to decide how long to search.
See also `rewrites` for a more convenient interface.
-/
-- We need to supply the current `MetavarContext` (which will be reused for each lemma application)
-- because `MLList.squash` executes lazily,
-- so there is no opportunity for `← getMCtx` to record the context at the call site.
def rewritesCore (hyps : Array (Expr × Bool × Nat))
    (lemmas : DiscrTree (Name × Bool × Nat) × DiscrTree (Name × Bool × Nat))
    (ctx : MetavarContext) (goal : MVarId) (target : Expr)
    (forbidden : NameSet := ∅)
    (side : SideConditions := .solveByElim) :
    MLList MetaM RewriteResult := MLList.squash fun _ => do
  -- Get all lemmas which could match some subexpression
  let candidates := (← lemmas.1.getSubexpressionMatches target discrTreeConfig)
    ++ (← lemmas.2.getSubexpressionMatches target discrTreeConfig)

  -- Sort them by our preferring weighting
  -- (length of discriminant key, doubled for the forward implication)
  let candidates := candidates.insertionSort fun r s => r.2.2 > s.2.2

  -- Now deduplicate. We can't use `Array.deduplicateSorted` as we haven't completely sorted,
  -- and in fact want to keep some of the residual ordering from the discrimination tree.
  let mut forward : NameSet := ∅
  let mut backward : NameSet := ∅
  let mut deduped := #[]
  for (l, s, w) in candidates do
    if forbidden.contains l then continue
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
    trace[Tactic.rewrites] m!"considering {if symm then "← " else ""}{expr}"
    let some result ← try? do goal.rewrite target expr symm
      | return none
    if result.mvarIds.isEmpty then
      return some ⟨expr, symm, weight, result, none, none, ← getMCtx⟩
    else
      -- There are side conditions, which we try to discharge using local hypotheses.
      match (← match side with
        | .none => pure none
        | .assumption => try? do _ ← result.mvarIds.mapM fun m => m.assumption
        | .solveByElim => try? do solveByElim result.mvarIds) with
      | none => return none
      | some _ =>
        -- If we succeed, we need to reconstruct the expression to report that we rewrote by.
        let some expr := result.by? | return none
        let expr ← instantiateMVars expr
        let (expr, symm) := if expr.isAppOfArity ``Eq.symm 4 then
            (expr.getArg! 3, true)
          else
            (expr, false)
        return some ⟨expr, symm, weight, result, none, none, ← getMCtx⟩

/--
Find lemmas which can rewrite the goal, and deduplicate based on pretty-printed results.
Note that this builds a `HashMap` containing the results, and so may consume significant memory.
-/
def rewritesDedup (hyps : Array (Expr × Bool × Nat))
    (lemmas : DiscrTree (Name × Bool × Nat) × DiscrTree (Name × Bool × Nat))
    (mctx : MetavarContext) (goal : MVarId) (target : Expr)
    (forbidden : NameSet := ∅) (side : SideConditions := .solveByElim) :
    MLList MetaM RewriteResult :=
  rewritesCore hyps lemmas mctx goal target forbidden side
    -- Don't report duplicate results.
    -- (TODO: a config flag to disable this,
    -- if distinct-but-pretty-print-the-same results are desirable?)
    |>.mapM (fun r => r.prepare_ppResult)
    |>.dedupBy (fun r => pure r.ppResult?)

/-- Find lemmas which can rewrite the goal. -/
def rewrites (hyps : Array (Expr × Bool × Nat))
    (lemmas : DiscrTree (Name × Bool × Nat) × DiscrTree (Name × Bool × Nat))
    (goal : MVarId) (target : Expr)
    (forbidden : NameSet := ∅) (side : SideConditions := .solveByElim)
    (stopAtRfl : Bool := false) (max : Nat := 20)
    (leavePercentHeartbeats : Nat := 10) : MetaM (List RewriteResult) := do
  let results ← rewritesDedup hyps lemmas (← getMCtx) goal target forbidden side
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
Syntax for excluding some names, e.g. `[-my_lemma, -my_theorem]`.
-/
-- TODO: allow excluding local hypotheses.
syntax forbidden := " [" (("-" ident),*,?) "]"

/--
`rw?` tries to find a lemma which can rewrite the goal.

`rw?` should not be left in proofs; it is a search tool, like `apply?`.

Suggestions are printed as `rw [h]` or `rw [← h]`.

You can use `rw? [-my_lemma, -my_theorem]` to prevent `rw?` using the named lemmas.
-/
syntax (name := rewrites') "rw?" (ppSpace location)? (forbidden)? : tactic

open Elab.Tactic Elab Tactic in
elab_rules : tactic |
    `(tactic| rw?%$tk $[$loc]? $[[ $[-$forbidden],* ]]?) => do
  let lems ← rewriteLemmas.get
  let forbidden : NameSet :=
    ((forbidden.getD #[]).map Syntax.getId).foldl (init := ∅) fun s n => s.insert n
  reportOutOfHeartbeats `rewrites tk
  let goal ← getMainGoal
  -- TODO fix doc of core to say that * fails only if all failed
  withLocation (expandOptLocation (Lean.mkOptionalNode loc))
    fun f => do
      let some a ← f.findDecl? | return
      if a.isImplementationDetail then return
      let target ← instantiateMVars (← f.getType)
      let hyps ← localHypotheses (except := [f])
      let results ← rewrites hyps lems goal target (stopAtRfl := false) forbidden
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
      let results ← rewrites hyps lems goal target (stopAtRfl := true) forbidden
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
