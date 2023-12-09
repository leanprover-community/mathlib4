/-
Copyright (c) 2023 Sebastian Zimmer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Zimmer, Mario Carneiro, Heather Macbeth
-/
import Mathlib.Tactic.Core
import Std.Tactic.LabelAttr
import Mathlib.Tactic.GCongr.Core
import Mathlib.Data.Prod.Basic

/-!
# GRW Tactic

This module defines the core of the `grw` tactic.

-/

open Lean Meta Std.Tactic.LabelAttr Elab Tactic

namespace Mathlib.Tactic.GRW

initialize registerTraceClass `GRW

/--
Lemmas marked `@[grw]` are used by the `grw` tactic to use a relation to rewrite an expression.

The lemma is used to rewrite its first explicit argument into the result type. The other arguments
are then filled in using the `gcongr` tactic.

For example, this lemma shows `grw` how to convert `a < b` into `c < d`.

```lean
@[grw]
lemma rewrite_lt {α : Type} [Preorder α] {a b c d : α} (h₁ : a < b) (h₂ : c ≤ a) (h₃ : b ≤ d) :
    c < d := lt_of_le_of_lt h₂ (lt_of_lt_of_le h₁ h₃)
```

These lemmas can do more than just use transitivity. This lemma shows `grw` to to rewrite `a ∈ X`
into `a ∈ Y`.

```lean
@[grw]
lemma rewrite_mem {α : Type} {a : α} {X Y: Set α} (h₁ : a ∈ X) (h₂ : X ⊆ Y) : a ∈ Y := h₂ h₁
```
-/
initialize ext : LabelExtension ← (
  let descr := "A lemma describing how to convert the first argument into the target type, possibly
introducing side goals. These side goals will be solved with `gcongr`"
  let grw := `grw
  registerLabelAttr grw descr grw)

open GCongr

/-- Given `relationType := R a b`, returns `(a, b)` -/
def getNeedleReplacement (relationType : Expr) : MetaM (Expr × Expr) := do
  let args := relationType.getAppArgs
  if args.size < 2 then
    throwError "Expecting relation but got {relationType}"
  return (args[args.size - 2]!, args[args.size - 1]!)

/--
Constructs the new expression after rewriting occurrences of the LHS of `rule` with the RHS
in `oldExpr` (or vice versa when `rev` is true). Returns `(template, newExpr)` where `newExpr` is
the replaced expression and `template` is the rewrite motive with the bound variable replaced with
a fresh mvar (used as input to gcongr).
-/
def getNewExpr (rule : Expr) (rev : Bool) (oldExpr : Expr) : MetaM (Expr × Expr) := do
  let ruleType ← instantiateMVars (← inferType rule)
  let (needle, replacement) ← if rev then
    Prod.swap <$> getNeedleReplacement ruleType
  else
    getNeedleReplacement ruleType
  trace[GRW] "Got needle = {needle} replacement = {replacement}"
  let abst ← withReducible <| kabstract oldExpr needle
  if !abst.hasLooseBVars then
    throwError "Could not find pattern {needle} in {oldExpr}"
  let newExpr := abst.instantiate1 replacement
  trace[GRW] "old expr {oldExpr} new expr {newExpr}"
  let template := abst.instantiate1 (← mkFreshExprSyntheticOpaqueMVar ruleType)
  return (← whnfR template, newExpr)

/-- Try to discharge the goal `goal` using `gcongr` using the provided `template` and using only
`rule` for discharging the main subgoals. -/
def useRule (template rule : Expr) (goal : MVarId) : MetaM (Array MVarId) := do
  let template ← instantiateMVars template
  try
    if template.hasExprMVar then failure
    goal.applyRfl
    trace[GRW] "used reflexivity"
    return #[]
  catch _ => pure ()
  try
    let (_, _, subgoals) ← goal.gcongr template [] (failIfMainsUnsolved := true)
      (mainGoalDischarger := fun g => g.gcongrForward #[rule])

    trace[GRW] "Got proof {← instantiateMVars (.mvar goal)}"
    return subgoals
  catch e =>
    throwError "failed to prove {← goal.getType} with gcongr, error was: {e.toMessageData}"

/--
Use the relation `rule : x ~ y` to rewrite the type of an mvar. Assigns the mvar and returns a new
mvar of type either `p[x/y]` or `p[y/x]` depending on the value of the `rev` parameter

Parameters:
* `goal` The mvar for the current goal
* `expr` the expression to rewrite in
* `rule` An expression of type `x ~ y` where `~` is some relation
* `rev` if true, we will rewrite `expr` to `newExpr := expr[y/x]`, otherwise `newExpr := expr[x/y]`
* `isTarget` if true we are proving `newExpr → expr` otherwise we are proving `expr → newExpr`

Returns:
* `newExpr` The rewritten version of `expr`
* `proof` if `isTarget` is true this is a value of type `newExpr → expr`,
  otherwise it has type `expr → newExpr`
* `subgoals` list of side goals created by `gcongr`. This does not include the goals
  successfully filled by `gcongr_discharger`
-/
def _root_.Lean.MVarId.grw (goal : MVarId) (expr rule : Expr) (rev isTarget : Bool) :
    MetaM (Expr × Expr × Array MVarId) := do
  let oldExpr ← instantiateMVars expr
  let (ruleArgs, _, resultType) ← forallMetaTelescope (← inferType rule)
  if (← whnfR resultType).isEq then
    let ⟨newExpr, eqProof, subgoals⟩ ← goal.rewrite expr rule rev
    let proof ← if isTarget then
      mkAppOptM ``cast #[newExpr, expr, ← mkEqSymm eqProof]
    else
      mkAppOptM ``cast #[expr, newExpr, eqProof]
    return ⟨newExpr, proof, subgoals.toArray⟩
  let rule := mkAppN rule ruleArgs
  let (template, newExpr) ← getNewExpr rule rev oldExpr
  let lemmas ← labelled `grw
  let (lhsExpr, rhsExpr) := if isTarget then (newExpr, oldExpr) else (oldExpr, newExpr)

  -- TODO surely this can be faster
  for lem in lemmas do
    let lemResult ← withTraceNode `GRW (fun _ ↦ return m!"trying lemma {lem}") do
      let lemResult ← try commitIfNoEx do
        let lemExpr ← mkConstWithFreshMVarLevels lem
        let lemType ← inferType lemExpr
        let (metas, binders, _) ← withReducible <| forallMetaTelescopeReducing lemType
        guard <| ← isDefEq rhsExpr (← inferType (mkAppN lemExpr metas))

        withLocalDeclD (← mkFreshUserName `h) lhsExpr fun value => do
          if let some firstDefaultArg := binders.findIdx? (· == .default) then
            withReducible <| metas[firstDefaultArg]!.mvarId!.assignIfDefeq value
          else
            throwError "Lemma {lem} did not have a default argument"

          trace[GRW] "Lemma {lem} matches, trying to fill args"
          pure <| some ⟨← mkLambdaFVars #[value] (mkAppN lemExpr metas), metas⟩
      catch ex => do
        trace[GRW] "error in lemma {lem}: {ex.toMessageData}"
        pure none

      if let some (lemExpr, metas) := lemResult then
        let metas ← metas.filterM fun x => not <$> x.mvarId!.isAssigned
        let args := template.getAppArgs
        -- HACK: we are assuming the side goals of the grw lemma come in the same order
        -- as they appear in the function, and all the fixed args (e.g. type, instances)
        -- come before the ones to rewrite
        let args := args[args.size - metas.size:].toArray
        let subgoals ← (metas.zip args).concatMapM fun (arg, template) => do
          let mvar := arg.mvarId!
          let type ← instantiateMVars (← inferType arg)
          withTraceNode `GRW (fun _ ↦ return m!"Looking for value of type {type}") do
            withReducibleAndInstances <| useRule template rule mvar
        trace[GRW] "Got subgoals {subgoals}"
        return some (lemExpr, subgoals)
      else
        return none

    if let some (proof, subgoals) := lemResult then
      trace[GRW] "Got proof {proof}"
      let ruleSubgoals ← (ruleArgs.map Expr.mvarId!).filterM fun x => not <$> x.isAssigned
      let subgoals := subgoals ++ ruleSubgoals
      let otherMVars := (← getMVarsNoDelayed proof).filter (!subgoals.contains ·)
      return (newExpr, proof, subgoals ++ otherMVars)
  throwError "No grw lemmas worked"
