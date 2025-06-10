/-
Copyright (c) 2023 Sebastian Zimmer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Zimmer, Mario Carneiro, Heather Macbeth
-/
import Mathlib.Tactic.Core
import Lean.LabelAttribute
import Mathlib.Tactic.GCongr.Core

/-!
# GRW Tactic

This module defines the core of the `grw` tactic.

-/

open Lean Meta Elab Tactic

namespace Mathlib.Tactic

structure GRewriteResult where
  /-- The rewritten expression -/
  eNew     : Expr
  /-- The proof of the implication. The direction depends on the argument `forwardImp`. -/
  impProof : Expr
  /-- The new side goals -/
  mvarIds  : List MVarId -- new goals

axiom getRel (e : Expr) : Option (Name × Expr × Expr)

/-- Configures the behavior of the `rewrite` and `rw` tactics. -/
structure GRewrite.Config extends Rewrite.Config where
  useRewrite : Bool := true

declare_config_elab elabRewriteConfig Rewrite.Config

/--
Rewrite `e` using the relation `hrel : x ~ y`, and construct an implication proof
using the `gcongr` tactic to discharge this goal.

if `forwardImp = true`, we prove that `e → eNew`; otherwise `eNew → e`.

If `symm = false`, we rewrite `e` to `eNew := e[x/y]`; otherwise `eNew := e[y/x]`.

The code aligns with `Lean.MVarId.rewrite` as much as possible.
-/
noncomputable
def _root_.Lean.MVarId.grewrite (mvarId : MVarId) (e : Expr) (hrel : Expr) (forwardImp : Bool)
    (symm : Bool := false) (config := { : GRewrite.Config }) : MetaM GRewriteResult :=
  mvarId.withContext do
    mvarId.checkNotAssigned `grewrite
    let hrelType ← instantiateMVars (← inferType hrel)
    let (newMVars, binderInfos, hrelType) ← forallMetaTelescopeReducing hrelType
    -- If we can use the normal `rewrite` tactic, we default to using that.
    if (hrelType.isAppOfArity ``Iff 2 || hrelType.isAppOfArity ``Eq 3) && config.useRewrite then
      let x ← mvarId.rewrite e hrel symm config.toConfig
      sorry
    else
    let hrelIn := hrel
    let hrel := mkAppN hrel newMVars
    let some (relName, lhs, rhs) := getRel hrelType |
      throwTacticEx `grewrite mvarId m!"{hrelType} is not a relation"
    let (lhs, rhs) := if symm then (rhs, lhs) else (lhs, rhs)
    if lhs.getAppFn.isMVar then
      throwTacticEx `grewrite mvarId
        m!"pattern is a metavariable{indentExpr lhs}\nfrom equation{indentExpr hrelType}"
    let e ← instantiateMVars e
    let eAbst ←
      withConfig (fun oldConfig => { config, oldConfig with }) <| kabstract e lhs config.occs
    unless eAbst.hasLooseBVars do
      throwTacticEx `grewrite mvarId
        m!"did not find instance of the pattern in the target expression{indentExpr lhs}"
    -- construct grewrite proof
    let eNew := eAbst.instantiate1 rhs
    let eNew ← instantiateMVars eNew
    try
      check eNew
    catch ex =>
      throwTacticEx `grewrite mvarId m!"\
        new expression is not type correct:{indentD eNew}\nError: {ex.toMessageData}\
        \n\n\
        Possible solutions: use grewrite's 'occs' configuration option to limit which occurrences \
        are rewritten, or use 'gcongr'."
    let eNew ← if rhs.hasBinderNameHint then eNew.resolveBinderNameHint else pure eNew
    let template := eAbst.instantiate1 (← mkFreshExprSyntheticOpaqueMVar default)

    let mkImp (e₁ e₂ : Expr) : Expr := .forallE `_a e₁ e₂ .default
    let imp := if forwardImp then mkImp e eNew else mkImp eNew e
    let gcongrGoal ← mkFreshExprMVar imp
    let (_, _, _) ← gcongrGoal.mvarId!.gcongr template [] (inGRewrite := true)

    postprocessAppMVars `grewrite mvarId newMVars binderInfos
      (synthAssignedInstances := !tactic.skipAssignedInstances.get (← getOptions))
    let newMVarIds ← newMVars.map Expr.mvarId! |>.filterM fun mvarId => not <$> mvarId.isAssigned
    let otherMVarIds ← getMVarsNoDelayed hrelIn
    let otherMVarIds := otherMVarIds.filter (!newMVarIds.contains ·)
    let newMVarIds := newMVarIds ++ otherMVarIds
    pure { eNew, impProof := ← instantiateMVars gcongrGoal, mvarIds := newMVarIds.toList }


end Mathlib.Tactic
