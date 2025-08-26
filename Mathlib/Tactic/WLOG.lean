/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Johan Commelin, Reid Barton, Thomas Murrills
-/
import Mathlib.Tactic.Core
import Lean.Meta.Tactic.Cases

/-!

# Without loss of generality tactic

The tactic `wlog h : P` will add an assumption `h : P` to the main goal,
and add a new goal that requires showing that the case `h : ¬ P` can be reduced to the case
where `P` holds (typically by symmetry).

The new goal will be placed at the top of the goal stack.

-/

namespace Mathlib.Tactic

open Lean Meta Elab Term Tactic MetavarContext.MkBinding

/-- The result of running `wlog` on a goal. -/
structure WLOGResult where
  /-- The `reductionGoal` requires showing that the case `h : ¬ P` can be reduced to the case where
  `P` holds. It has two additional assumptions in its context:

  * `h : ¬ P`: the assumption that `P` does not hold
  * `H`: the statement that in the original context `P` suffices to prove the goal.
  -/
  reductionGoal : MVarId
  /-- The pair `(HFVarId, negHypFVarId)` of `FVarIds` for `reductionGoal`:

  * `HFVarId`: `H`, the statement that in the original context `P` suffices to prove the goal.
  * `negHypFVarId`: `h : ¬ P`, the assumption that `P` does not hold
  -/
  reductionFVarIds : FVarId × FVarId
  /-- The original goal with the additional assumption `h : P`. -/
  hypothesisGoal   : MVarId
  /-- The `FVarId` of the hypothesis `h` in `hypothesisGoal` -/
  hypothesisFVarId : FVarId
  /-- The array of `FVarId`s that was reverted to produce the reduction hypothesis `H` in
  `reductionGoal`, which are still present in the context of `reductionGoal` (but not necessarily
  `hypothesisGoal`). -/
  revertedFVarIds  : Array FVarId

open private withFreshCache mkAuxMVarType from Lean.MetavarContext in
/-- `wlog goal h P xs H` will return two goals: the `hypothesisGoal`, which adds an assumption
`h : P` to the context of `goal`, and the `reductionGoal`, which requires showing that the case
`h : ¬ P` can be reduced to the case where `P` holds (typically by symmetry).

In `reductionGoal`, there will be two additional assumptions:
- `h : ¬ P`: the assumption that `P` does not hold
- `H`: which is the statement that in the old context `P` suffices to prove the goal.
  If `H` is `none`, the name `this` is used.

If `xs` is `none`, all hypotheses are reverted to produce the reduction goal's hypothesis `H`.
Otherwise, the `xs` are elaborated to hypotheses in the context of `goal`, and only those
hypotheses are reverted (and any that depend on them).

If `h` is `none`, the hypotheses of types `P` and `¬ P` in both branches will be inaccessible. -/
def _root_.Lean.MVarId.wlog (goal : MVarId) (h : Option Name) (P : Expr)
    (xs : Option (TSyntaxArray `ident) := none) (H : Option Name := none) :
    TacticM WLOGResult := goal.withContext do
  goal.checkNotAssigned `wlog
  let H := H.getD `this
  let inaccessible := h.isNone
  let h := h.getD `h
  /- Compute the type for H and keep track of the FVarId's reverted in doing so. (Do not modify the
  tactic state.) -/
  let HSuffix := Expr.forallE h P (← goal.getType) .default
  let fvars ← getFVarIdsAt goal xs
  let fvars := fvars.map Expr.fvar
  let lctx := (← goal.getDecl).lctx
  let (revertedFVars, HType) ← liftMkBindingM fun ctx => (do
    let f ← collectForwardDeps lctx fvars
    let revertedFVars := filterOutImplementationDetails lctx (f.map Expr.fvarId!)
    let HType ← withFreshCache do
      mkAuxMVarType lctx (revertedFVars.map Expr.fvar) .natural HSuffix (usedLetOnly := true)
    return (revertedFVars, HType))
      { preserveOrder := false, quotContext := ctx.quotContext }
  /- Set up the goal which will suppose `h`; this begins as a goal with type H (hence HExpr), and h
  is obtained through `introNP` -/
  let HExpr ← mkFreshExprSyntheticOpaqueMVar HType
  let hGoal := HExpr.mvarId!
  /- Begin the "reduction goal" which will contain hypotheses `H` and `¬h`. For now, it only
  contains `H`. Keep track of that hypothesis' FVarId. -/
  let (HFVarId, reductionGoal) ←
    goal.assertHypotheses #[{ userName := H, type := HType, value := HExpr }]
  let HFVarId := HFVarId[0]!
  /- Clear the reverted fvars from the branch that will contain `h` as a hypothesis. -/
  let hGoal ← hGoal.tryClearMany revertedFVars
  /- Introduce all of the reverted fvars to the context in order to restore the original target as
  well as finally introduce the hypothesis `h`. -/
  let (_, hGoal) ← hGoal.introNP revertedFVars.size
  -- keep track of the hypothesis' FVarId
  let (hFVar, hGoal) ← if inaccessible then hGoal.intro1 else hGoal.intro1P
  /- Split the reduction goal by cases on `h`. Keep the one with `¬h` as the reduction goal,
  and prove the easy goal by applying `H` to all its premises, which are fvars in the context. -/
  let (⟨easyGoal, hyp⟩, ⟨reductionGoal, negHyp⟩) ←
    reductionGoal.byCases P <| if inaccessible then `_ else h
  easyGoal.withContext do
    -- Exclude ldecls from the `mkAppN` arguments
    let HArgFVarIds ← revertedFVars.filterM (notM ·.isLetVar)
    let HApp ← instantiateMVars <|
      mkAppN (.fvar HFVarId) (HArgFVarIds.map .fvar) |>.app (.fvar hyp)
    ensureHasNoMVars HApp
    easyGoal.assign HApp
  return ⟨reductionGoal, (HFVarId, negHyp), hGoal, hFVar, revertedFVars⟩

/-- `wlog h : P` will add an assumption `h : P` to the main goal, and add a side goal that requires
showing that the case `h : ¬ P` can be reduced to the case where `P` holds (typically by symmetry).

The side goal will be at the top of the stack. In this side goal, there will be two additional
assumptions:
- `h : ¬ P`: the assumption that `P` does not hold
- `this`: which is the statement that in the old context `P` suffices to prove the goal.
  By default, the name `this` is used, but the idiom `with H` can be added to specify the name:
  `wlog h : P with H`.

Typically, it is useful to use the variant `wlog h : P generalizing x y`,
to revert certain parts of the context before creating the new goal.
In this way, the wlog-claim `this` can be applied to `x` and `y` in different orders
(exploiting symmetry, which is the typical use case).

By default, the entire context is reverted. -/
syntax (name := wlog) "wlog " binderIdent " : " term
  (" generalizing" (ppSpace colGt ident)*)? (" with " binderIdent)? : tactic

elab_rules : tactic
| `(tactic| wlog $h:binderIdent : $P:term $[ generalizing $xs*]? $[ with $H:ident]?) =>
  withMainContext do
  let H := H.map (·.getId)
  let h := match h with
  | `(binderIdent|$h:ident) => some h.getId
  | _ => none
  let P ← elabType P
  let goal ← getMainGoal
  let { reductionGoal, hypothesisGoal .. } ← goal.wlog h P xs H
  replaceMainGoal [reductionGoal, hypothesisGoal]

end Mathlib.Tactic
