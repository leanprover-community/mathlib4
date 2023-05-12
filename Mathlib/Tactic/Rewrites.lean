/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
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

initialize rewriteLemmas : DeclCache (DiscrTree (Name × Bool × Nat) true) ←
  DeclCache.mk "rewrites: init cache" {} fun name constInfo lemmas => do
    if constInfo.isUnsafe then return lemmas
    if ← name.isBlackListed then return lemmas
    if name matches .str _ "injEq" then return lemmas
    if name matches .str _ "sizeOf_spec" then return lemmas
    match name with
    | .str _ n => if n.endsWith "_inj" ∨ n.endsWith "_inj'" then return lemmas
    | _ => pure ()
    let forwardWeight := 2
    let backwardWeight := 1
    withNewMCtxDepth do withReducible do
      let (_, _, type) ← forallMetaTelescopeReducing constInfo.type
      match type.getAppFnArgs with
      | (``Eq, #[_, lhs, rhs]) => do
        let lhsKey ← DiscrTree.mkPath lhs
        let rhsKey ← DiscrTree.mkPath rhs
        pure <| lemmas.insertIfSpecific lhsKey (name, false, forwardWeight * lhsKey.size)
          |>.insertIfSpecific rhsKey (name, true, backwardWeight * rhsKey.size)
      | (``Iff, #[lhs, rhs]) => do
        let lhsKey ← DiscrTree.mkPath lhs
        let rhsKey ← DiscrTree.mkPath rhs
        pure <| lemmas.insertIfSpecific lhsKey (name, false, forwardWeight * lhsKey.size)
          |>.insertIfSpecific rhsKey (name, true, backwardWeight * rhsKey.size)
      | _ => pure lemmas

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
def rewritesCore (lemmas : DiscrTree (Name × Bool × Nat) s) (goal : MVarId) :
    ListM MetaM RewriteResult := ListM.squash do
  let type ← instantiateMVars (← goal.getType)
  -- Get all lemmas which could match some subexpression
  let candidates ← lemmas.getSubexpressionMatches type
  -- Sort them by our preferring weighting
  -- (length of discriminant key, doubled for the forward implication)
  let candidates := candidates.insertionSort fun r s => r.2.2 > s.2.2
  -- Lift to a monadic list, so the caller can decide how much of the computation to run.
  let candidates := ListM.ofList candidates.toList
  pure <| candidates.filterMapM fun ⟨lem, symm, weight⟩ => do
    trace[Tactic.rewrites] "considering {if symm then "←" else ""}{lem}"
    let some result ← try? <| goal.rewrite type (← mkConstWithFreshMVarLevels lem) symm
      | return none
    return if result.mvarIds.isEmpty then
      some ⟨lem, symm, weight, result, none⟩
    else
      -- TODO Perhaps allow new goals? Try closing them with solveByElim?
      none

/-- Find lemmas which can rewrite the goal. -/
def rewrites (lemmas : DiscrTree (Name × Bool × Nat) s) (goal : MVarId)
    (max : Nat := 10) (leavePercentHeartbeats : Nat := 10) : MetaM (List RewriteResult) :=
rewritesCore lemmas goal
  -- Don't use too many heartbeats.
  |>.whileAtLeastHeartbeatsPercent leavePercentHeartbeats
  -- Stop if we find a rewrite after which `with_reducible rfl` would succeed.
  |>.mapM RewriteResult.computeRefl
  |>.takeUpToFirst (fun r => r.refl? = some true)
  -- Bound the number of results.
  |>.takeAsList max

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
