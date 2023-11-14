/-
Copyright (c) 2023 Sebastian Zimmer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Zimmer
-/
import Mathlib.Tactic.Core
import Std.Tactic.LabelAttr
import Mathlib.Tactic.GCongr

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

/--
Lemmas marked `@[grw_weaken]` are used to 'weaken' rules in the `grw` tactic, for example by
converting `a < b` into `a ≤ b`. The lemma should take a single explicit argument.

The `grw` tactic currently tries all weakening lemmas and stops when one works. There is no
backtracking or recursion.

The weakening process does not affect the type of the resulting target/hypothesis, so it is safe
to convert `b > a` into `a ≤ b`, for example.

-/
initialize extWeaken : LabelExtension ← (
  let descr := "A lemma that goes from a strict relation to a non strict one."
  let grw_weaken := `grw_weaken
  registerLabelAttr grw_weaken descr grw_weaken)


open GCongr

private partial def getNeedleReplacement (relation_type : Expr) : MetaM (Expr × Expr) := do
  let ⟨_, args⟩ := relation_type.getAppFnArgs
  if args.size < 2 then
    throwError "Expecting relation but got {relation_type}"

  return ⟨args[args.size - 2]!, args[args.size - 1]!⟩

private partial def getNewType (rule : Expr) (rev : Bool) (oldType : Expr) : MetaM Expr := do
  let ruleType ← instantiateMVars (← inferType rule)
  let ⟨needle, replacement⟩ := if rev then
    (← getNeedleReplacement ruleType).swap
  else
    ← getNeedleReplacement ruleType
  trace[GRW] "Got needle = {needle} replacement = {replacement}"
  let abst ← withReducible $ kabstract oldType needle
  if !abst.hasLooseBVars then
    throwError "Could not find pattern {needle} in {oldType}"
  let newType := abst.instantiate1 replacement
  trace[GRW] "old type {oldType} new type {newType}"
  return newType

-- TODO make this extensible
private partial def dischargeSideGoal (mvar : MVarId) : MetaM Unit := Term.TermElabM.run' do
  trace[GRW] "Attempting to discharge side goal {mvar}"
  let [] ← Tactic.run mvar <| evalTactic (Unhygienic.run `(tactic| gcongr_discharger))
    | failure

private partial def dischargeMainGoal (rule : Expr) (mvar : MVarId) : MetaM Unit := do
  trace[GRW] "Discharging main goal {mvar}"
  try do
    commitIfNoEx mvar.applyRfl
    trace[GRW] "used reflexivity"
    return
  catch _ =>
  try do
    commitIfNoEx <| mvar.assignIfDefeq rule
    trace[GRW] "used rule {rule}"
    return
  catch _ =>

  throwError "Could not discharge main goal"

private partial def useRule (rule : Expr) (mvar : MVarId) : MetaM (Array MVarId) := do
  let ⟨progress, _, subgoals⟩ ← mvar.gcongr
    none
    []
    (side_goal_discharger := dischargeSideGoal)
    (main_goal_discharger := dischargeMainGoal rule)

  let subgoals := subgoals
  if !progress then
    throwError "gcongr could not make progress on {mvar}"
  trace[GRW] "Got proof {← instantiateMVars (Expr.mvar mvar)}"
  return subgoals

private def weaken (rule : Expr) : MetaM Expr := do
  let lemmas ← labelled `grw_weaken

  for lem in lemmas do
    let s ← saveState
    try do
      let result ← mkAppM lem #[rule]
      trace[GRW] "weakened to {← inferType result}"
      return result
    catch _ =>
      s.restore

  return rule

/--
Use the relation `rule` to rewrite `expr`
-/
partial def runGrw (expr rule : Expr) (rev isTarget : Bool) :
    MetaM (Expr × Expr × MVarId × Array MVarId) := do
  let oldType ← instantiateMVars (← inferType expr)
  let ⟨ruleArgs, _, _⟩ ← forallMetaTelescope (← inferType rule)
  let metaRule := mkAppN rule ruleArgs
  let newType ← getNewType metaRule rev oldType
  let weakRule ← weaken metaRule
  let lemmas ← labelled `grw

  let result ← mkFreshExprMVar newType

  -- TODO surely this can be faster
  for lem in lemmas do
    let lemResult : Option (Expr × Array MVarId)
        ← withTraceNode `GRW (λ _ ↦ return m!"trying lemma {lem}") do
      let s ← saveState
      let (lemResult : Option (Expr × Array Expr)) ← try
        let lemExpr ← mkConstWithFreshMVarLevels lem
        let lemType ← inferType lemExpr
        let ⟨metas, binders, _⟩ ← forallMetaTelescopeReducing lemType
        let mvarToAssign := if isTarget then expr.mvarId! else result.mvarId!
        withReducible $ mvarToAssign.assignIfDefeq (mkAppN lemExpr metas)

        let firstDefaultArg := binders.findIdx? (λ x ↦ x == .default)
        if let some firstDefaultArg := firstDefaultArg then do
          let valueToAssign := if isTarget then result else expr
          withReducible $ metas[firstDefaultArg]!.mvarId!.assignIfDefeq valueToAssign
        else
          throwError "Lemma {lem} did not have a default argument"

        trace[GRW] "Lemma {lem} matches, trying to fill args"
        pure $ some ⟨lemExpr, metas⟩
      catch ex => do
        trace[GRW] "error in lemma {ex.toMessageData}"
        s.restore
        pure none

      if let some ⟨lemExpr, metas⟩ := lemResult then
        let subgoals ← metas.concatMapM fun arg => do
          let mvar := arg.mvarId!
          let type ← instantiateMVars (← inferType arg)
          if ← mvar.isAssigned then
            trace[GRW] "mvar already assigned to {← instantiateMVars arg} : {type}"
            pure #[]
          else
            withTraceNode `GRW (λ _ ↦ return m!"Looking for value of type {type}") do
              withReducibleAndInstances $ useRule weakRule mvar
        trace[GRW] "Got subgoals {subgoals}"
        return some ⟨(← instantiateMVars <| mkAppN lemExpr metas), subgoals⟩
      else
        return none

    if let some ⟨prf, subgoals⟩ := lemResult then
      trace[GRW] "Got proof {prf}"
      return ⟨newType, prf, result.mvarId!, subgoals⟩
  throwError "No grw lemmas worked"
