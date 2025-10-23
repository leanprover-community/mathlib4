/-
Copyright (c) 2023 Sebastian Zimmer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Zimmer, Mario Carneiro, Heather Macbeth, Jovan Gerbscheid
-/
import Mathlib.Tactic.GCongr.Core

/-!

# The generalized rewriting tactic

This module defines the core of the `grw`/`grewrite` tactic.

TODO:

The algorithm used to implement `grw` uses the same method as `rw` to determine where to rewrite.
This means that we can get ill-typed results. Moreover, it doesn't detect which occurrences
can be rewritten by `gcongr` and which can't. It also means we cannot rewrite bound variables.

A better algorithm would be similar to `simp only`, where we recursively enter the subexpression
using `gcongr` lemmas. This is tricky due to the many different `gcongr` for each pattern.

With the current implementation, we can instead use `nth_grw`.

-/

open Lean Meta

namespace Mathlib.Tactic

/-- Given a proof of `a ~ b`, close a goal of the form `a ~' b` or `b ~' a`
for some possibly different relation `~'`. -/
def GRewrite.dischargeMain (hrel : Expr) (goal : MVarId) : MetaM Bool := do
  if ← goal.gcongrForward #[hrel] then
    return true
  else
    throwTacticEx `grewrite goal m!"could not discharge {← goal.getType} using {← inferType hrel}"

/-- The result returned by `Lean.MVarId.grewrite`. -/
structure GRewriteResult where
  /-- The rewritten expression -/
  eNew : Expr
  /-- The proof of the implication. The direction depends on the argument `forwardImp`. -/
  impProof : Expr
  /-- The new side goals -/
  mvarIds : List MVarId -- new goals

/-- Configures the behavior of the `rewrite` and `rw` tactics. -/
structure GRewrite.Config extends Rewrite.Config where
  /-- When `useRewrite = true`, switch to using the default `rewrite` tactic when the goal is
  and equality or iff. -/
  useRewrite : Bool := true
  /-- When `implicationHyp = true`, interpret the rewrite rule as an implication. -/
  implicationHyp : Bool := false

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
    let maxMVars? ←
      if config.implicationHyp then
        if let arity + 1 := hrelType.getForallArity then
          pure (some arity)
        else
          throwTacticEx `apply_rw goal m!"invalid implication {hrelType}"
      else
        pure none
    let (newMVars, binderInfos, hrelType) ←
      withReducible <| forallMetaTelescopeReducing hrelType maxMVars?

    -- If we can use the normal `rewrite` tactic, we default to using that.
    if (hrelType.isAppOfArity ``Iff 2 || hrelType.isAppOfArity ``Eq 3) && config.useRewrite then
      let { eNew, eqProof, mvarIds } ← goal.rewrite e hrel symm config.toConfig
      let mp := if forwardImp then ``Eq.mp else ``Eq.mpr
      let impProof ← mkAppOptM mp #[e, eNew, eqProof]
      return { eNew, impProof, mvarIds }

    let hrelIn := hrel
    -- check that `hrel` proves a relation
    let hrel := mkAppN hrel newMVars
    let some (_, lhs, rhs) := GCongr.getRel hrelType |
      throwTacticEx `grewrite goal m!"{hrelType} is not a relation"
    let (lhs, rhs) := if symm then (rhs, lhs) else (lhs, rhs)
    if lhs.getAppFn.isMVar then
      throwTacticEx `grewrite goal
        m!"pattern is a metavariable{indentExpr lhs}\nfrom relation{indentExpr hrelType}"
    -- abstract the occurrences of `lhs` from `e` to get `eAbst`
    let e ← instantiateMVars e
    let eAbst ←
      withConfig (fun oldConfig => { config, oldConfig with }) <| kabstract e lhs config.occs
    unless eAbst.hasLooseBVars do
      throwTacticEx `grewrite goal
        m!"did not find instance of the pattern in the target expression{indentExpr lhs}"
    -- construct `eNew` by instantiating `eAbst` with `rhs`.
    let eNew := eAbst.instantiate1 (GCongr.mkHoleAnnotation rhs)
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
    let mkImp (e₁ e₂ : Expr) : Expr := .forallE `_a e₁ e₂ .default
    let imp := if forwardImp then mkImp e eNew else mkImp eNew e
    let gcongrGoal ← mkFreshExprMVar imp
    let (_, _, sideGoals) ← gcongrGoal.mvarId!.gcongr (!forwardImp) []
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
