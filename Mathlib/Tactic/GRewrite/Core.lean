/-
Copyright (c) 2023 Sebastian Zimmer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Zimmer, Mario Carneiro, Heather Macbeth, Jovan Gerbscheid
-/
import Mathlib.Tactic.Core
import Lean.LabelAttribute
import Mathlib.Tactic.GCongr.Core

/-!

# The generalized rewriting tactic

This module defines the core of the `grw`/`grewrite` tactic.

-/

open Lean Meta

namespace Mathlib.Tactic

def GRewrite.dischargeMain (hrel : Expr) (goal : MVarId) : MetaM Unit := do
  try
    goal.gcongrForward #[hrel]
  catch _ =>
    throwTacticEx `grewrite goal m!"could not discharge {← goal.getType} using {← inferType hrel}"


structure GRewriteResult where
  /-- The rewritten expression -/
  eNew     : Expr
  /-- The proof of the implication. The direction depends on the argument `forwardImp`. -/
  impProof : Expr
  /-- The new side goals -/
  mvarIds  : List MVarId -- new goals

/-- Configures the behavior of the `rewrite` and `rw` tactics. -/
structure GRewrite.Config extends Rewrite.Config where
  useRewrite : Bool := true
  implicationHyp : Bool := false

declare_config_elab elabRewriteConfig Rewrite.Config

/--
Rewrite `e` using the relation `hrel : x ~ y`, and construct an implication proof
using the `gcongr` tactic to discharge this goal.

if `forwardImp = true`, we prove that `e → eNew`; otherwise `eNew → e`.

If `symm = false`, we rewrite `e` to `eNew := e[x/y]`; otherwise `eNew := e[y/x]`.

The code aligns with `Lean.MVarId.rewrite` as much as possible.
-/
def _root_.Lean.MVarId.grewrite (goal : MVarId) (e : Expr) (hrel : Expr)
    (forwardImp symm : Bool) (config : GRewrite.Config) : MetaM GRewriteResult :=
  goal.withContext do
    goal.checkNotAssigned `grewrite
    let hrelType ← instantiateMVars (← inferType hrel)
    let maxMVars? := if config.implicationHyp then some (hrelType.getForallArity - 1) else none
    let (newMVars, binderInfos, hrelType) ← forallMetaTelescopeReducing hrelType maxMVars?

    -- If we can use the normal `rewrite` tactic, we default to using that.
    if (hrelType.isAppOfArity ``Iff 2 || hrelType.isAppOfArity ``Eq 3) && config.useRewrite then
      let ⟨eNew, eqProof, subgoals⟩ ← goal.rewrite e hrel symm config.toConfig
      let proof ← if forwardImp then
        mkAppOptM ``cast #[e, eNew, eqProof]
      else
        mkAppOptM ``cast #[eNew, e, ← mkEqSymm eqProof]
      return ⟨eNew, proof, subgoals⟩

    let hrelIn := hrel
    -- check that `hrel` proves a relation
    let hrel := mkAppN hrel newMVars
    let some (_, lhs, rhs) := GCongr.getRel hrelType |
      throwTacticEx `grewrite goal m!"{hrelType} is not a relation"
    let (lhs, rhs) := if symm then (rhs, lhs) else (lhs, rhs)
    if lhs.getAppFn.isMVar then
      throwTacticEx `grewrite goal
        m!"pattern is a metavariable{indentExpr lhs}\nfrom equation{indentExpr hrelType}"
    -- abstract the occurrences of `lhs` from `e` to get `eAbst`
    let e ← instantiateMVars e
    let eAbst ←
      withConfig (fun oldConfig => { config, oldConfig with }) <| kabstract e lhs config.occs
    unless eAbst.hasLooseBVars do
      throwTacticEx `grewrite goal
        m!"did not find instance of the pattern in the target expression{indentExpr lhs}"
    -- construct `eNew` by instantiating `eAbst` with `rhs`.
    let eNew := eAbst.instantiate1 rhs
    let eNew ← instantiateMVars eNew
    -- check that `eNew` is well typed
    try
      check eNew
    catch ex =>
      throwTacticEx `grewrite goal m!"\
        rewritten expression is not type correct:{indentD eNew}\nError: {ex.toMessageData}\
        \n\n\
        Possible solutions: use grewrite's 'occs' configuration option to limit which occurrences \
        are rewritten, or specify what the rewritten expression should be and use 'gcongr'."
    let eNew ← if rhs.hasBinderNameHint then eNew.resolveBinderNameHint else pure eNew
    -- construct the implication proof using `gcongr`
    let template := eAbst.instantiate1 (← mkFreshExprSyntheticOpaqueMVar default)
    let mkImp (e₁ e₂ : Expr) : Expr := .forallE `_a e₁ e₂ .default
    let imp := if forwardImp then mkImp e eNew else mkImp eNew e
    let gcongrGoal ← mkFreshExprMVar imp
    let (_, _, sideGoals) ← gcongrGoal.mvarId!.gcongr template [] (inGRewrite := true)
      (mainGoalDischarger := GRewrite.dischargeMain hrel)
    -- post-process the metavariables
    postprocessAppMVars `grewrite goal newMVars binderInfos
      (synthAssignedInstances := !tactic.skipAssignedInstances.get (← getOptions))
    let newMVarIds ← (sideGoals ++ newMVars.map Expr.mvarId!).filterM (not <$> ·.isAssigned)
    let otherMVarIds ← getMVarsNoDelayed hrelIn
    let otherMVarIds := otherMVarIds.filter (!newMVarIds.contains ·)
    let newMVarIds := newMVarIds ++ otherMVarIds
    pure { eNew, impProof := ← instantiateMVars gcongrGoal, mvarIds := newMVarIds.toList }

end Mathlib.Tactic
