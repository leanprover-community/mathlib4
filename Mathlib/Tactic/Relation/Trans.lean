/-
Copyright (c) 2022 Siddhartha Gadgil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Mario Carneiro
-/
import Mathlib.Lean.Meta
import Mathlib.Lean.Elab.Tactic.Basic
import Mathlib.Lean.Expr.Basic
import Lean.Elab.Tactic.Location

/-!
# `trans` tactic

This implements the `trans` tactic, which can apply transitivity theorems with an optional middle
variable argument.
-/

namespace Mathlib.Tactic
open Lean Meta Elab

initialize registerTraceClass `Tactic.trans

/-- Environment extension storing transitivity lemmas -/
initialize transExt :
    SimpleScopedEnvExtension (Name × Array (DiscrTree.Key true)) (DiscrTree Name true) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun dt (n, ks) ↦ dt.insertCore ks n
    initial := {}
  }

initialize registerBuiltinAttribute {
  name := `trans
  descr := "transitive relation"
  add := fun decl _ kind ↦ MetaM.run' <| withReducible do
    let declTy := (← getConstInfo decl).type
    let (hs, _, targetTy) ← forallMetaTelescope declTy
    let failMsg := "@[trans] attribute only applies to lemmas proving x ∼ y → y ∼ z → x ∼ z"
    let some h₂ := hs.back? | throwError "{failMsg}, but couldn't find hypotheses"
    let some h₁ := hs.pop.back? | throwError "{failMsg}, but only found one hypothesis"
    let xz ← targetTy.getNumExplicitArgs 2
    let xy ← (← inferType h₁).getNumExplicitArgs 2
    let yz ← (← inferType h₂).getNumExplicitArgs 2
    unless ← withNewMCtxDepth <|
        isDefEq xz[0]! xy[0]! <&&> isDefEq xz[1]! yz[1]! <&&> isDefEq xy[1]! yz[0]! do
      throwError "{failMsg
        }, but got {xy[0]!} ∼ {xy[1]!} → {yz[0]!} ∼ {yz[1]!} → {xz[0]!} ∼ {xz[1]!}"
    let key ← DiscrTree.mkPath (← whnfR targetTy)
    transExt.add (decl, key) kind
}

/-- Composition using the `Trans` class in the homogeneous case. -/
def _root_.Trans.simple {a b c : α} [Trans r r r] : r a b → r b c → r a c := trans

/-- Composition using the `Trans` class in the general case. -/
def _root_.Trans.het {a : α} {b : β} {c : γ}
  {r : α → β → Sort u} {s : β → γ → Sort v} {t : outParam (α → γ → Sort w)}
  [Trans r s t] : r a b → s b c → t a c := trans

/-- Applies all `@[trans]` lemmas to the goal, optionally using `y?` as a "bridge" argument. Fails
if no lemma can be applied.

If a lemma of type `..hyps → x ∼ y → y ∼ z → x ∼ z` can be applied to the goal of type `x ∼ z`,
this returns `?g₁ : x ∼ y`, `?g₂ : y ∼ z`, and `?y` in that order, along with an array of any
unsolved explicit arguments in `hyps`. If `?y` was solved, we return `none`.

If the argument `y?` is provided as `none`, a new metavariable will be created for `y` if
necessary; otherwise the third component of the return value will be `none`.

If `userFacingGoals` is `true`, the returned goals will be renamed appropriately and changed from
`.natural` (the default) to `.syntheticOpaque`, except for `?y` (if present). This allows `?y` to
be assigned in the course of solving for the other goals. -/
def _root_.Lean.MVarId.trans (g : MVarId) (y? : Option Expr := none) (userFacingGoals := false)
    : MetaM (MVarId × MVarId × Option MVarId × Array MVarId) := withReducible do
  let tgt ← g.getType'
  let s ← saveState
  for lem in (← (transExt.getState (← getEnv)).getUnify tgt) ++ #[``Trans.simple, ``Trans.het] do
    trace[Tactic.trans] "trying {lem}"
    try
      let (l, lType) ← mkFun lem
      let (hs, bs, targetTy) ← forallMetaTelescope lType
      let g₂ := hs.back.mvarId!
      let g₁ := hs[hs.size - 2]!.mvarId!
      -- whnf(R) the hypotheses. Also makes them syntheticOpaque.
      let g₂ ← g₂.change (← whnfR <|← g₂.getType) false
      let g₁ ← g₁.change (← whnfR <|← g₁.getType) false
      -- Assign mvars in `targetTy` (and therefore in `hs`)
      unless ← isDefEq targetTy tgt do throwError "doesn't apply!"
      -- Process optional "bridge" argument
      let yz ← (← inferType hs.back).getNumExplicitArgs 2
      let yGoal? ← match y? with
        | none => pure yz[0]!.mvarId?
        | some y => match yz[0]!.mvarId? with
          | some mvarId => do
            unless ← isDefEq yz[0]! y do
              throwError "could not use {y}; was not defeq to {yz[0]!}"
            unless ← mvarId.isAssigned do mvarId.assign y -- `isDefEq` doesn't always assign mvars
            pure none
          | none => throwError "could not use {y}; {yz[0]!} is not a metavariable"
      -- We use `mkAppNUnifying` to account for the new assignments.
      let proof ← mkAppNUnifying l hs
      -- Assign the proof to `g`
      unless ← isDefEq (.mvar g) proof do
        throwError "{← g.getType} is not defeq to {← inferType proof}"
      unless ← g.isAssigned do g.assign proof -- `isDefEq` doesn't always assign mvars
      -- Handle remaining `hs`
      let (explicitHyps, implicitHyps, instImplicitHyps) := groupByBinderInfo hs.pop.pop bs.pop.pop
      -- Check we have all instance hypotheses, and if not try to synthesize them.
      instImplicitHyps.forM fun mvar => do
        let mvarId := mvar.mvarId!
        unless ← mvarId.isAssigned do
          let mvarVal ← synthInstance (← instantiateMVars <|← mvarId.getType)
          mvarId.assign mvarVal
      -- Make sure all implicit hypotheses in `hs` got assigned, but make an exception for the
      -- "bridge" argument `y`, if there is one.
      let allImplicitHypsAssigned ←
        if let some yGoal := yGoal? then
          implicitHyps.allM fun h => do
            let mvarId := h.mvarId!
            pure (mvarId == yGoal) <||> mvarId.isAssigned
        else
          implicitHyps.allM (·.mvarId!.isAssigned)
      unless allImplicitHypsAssigned do
        throwError "could not unify all implicit arguments, namely {
          ← implicitHyps.filterM (notM ·.mvarId!.isAssigned)}"
      if userFacingGoals then return (
          ← g₁.mkUserFacingMVar `trans₁ false, -- already `.syntheticOpaque`.
          ← g₂.mkUserFacingMVar `trans₂ false,
          (← yGoal?.mapM (·.mkUserFacingMVar? `trans_y (setSyntheticOpaque := false))).join,
          ← mkUserFacingMVarsArray (explicitHyps.map (·.mvarId!)) `trans_side)
      else return (
          g₁,
          g₂,
          yGoal?,
          ← explicitHyps.filterMapM (·.mvarId!.unassigned?))
    catch e =>
      trace[Tactic.trans] "failed: {e.toMessageData}"
      s.restore
  throwError "no trans lemmas applied"

open Lean.Elab.Tactic

/--
`trans` applies to a goal whose target has the form `t ~ u` where `~` is a transitive relation,
that is, a relation which has a transitivity lemma tagged with the attribute [trans].

* `trans s` replaces the goal with the two subgoals `t ~ s` and `s ~ u`.
* If `s` is omitted, then a metavariable is used instead.
-/
elab "trans" t?:(ppSpace (colGt term))? : tactic => withMainContext do
  let yGoals? ← t?.mapM (elabTermWithHoles · none (← getMainTag))
  let (y?, goals?) := match yGoals? with
    | some (y, goals) => (some y, some goals)
    | none => (none, none)
  let (g₁, g₂, yGoal?, otherGoals) ← liftMetaM <| (← getMainGoal).trans y?
  let goals? ← goals?.mapM (mkUserFacingMVars · `trans_y_side)
  let mut allGoals := #[]
  allGoals := allGoals.push g₁
  allGoals := allGoals.push g₂
  if let some y  := yGoal? then allGoals := allGoals.push y
  if let some gs := goals? then allGoals := allGoals ++ gs
  allGoals := allGoals ++ otherGoals
  replaceMainGoal allGoals.toList
