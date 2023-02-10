/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Johan Commelin, Reid Barton, Thomas Murrills
-/
import Lean
import Mathlib.Tactic.Core

/-!

# Without loss of generality tactic

The tactic `wlog h : P` will add an assumption `h : P` to the main goal,
and add a new goal that requires showing that the case `h : ¬ P` can be reduced to the case
where `P` holds (typically by symmetry).

The new goal will be placed at the top of the goal stack.

-/

namespace Mathlib.Tactic.WLOG

open Lean Meta Elab Term Tactic

/-- `wlog h : P` will add an assumption `h : P` to the main goal,
and add a side goal that requires showing that the case `h : ¬ P` can be reduced to the case
where `P` holds (typically by symmetry).

The side goal will be at the top of the stack. In this side goal, there will be two assumptions:
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
| `(tactic| wlog $h:ident : $P:term $[ generalizing $xs*]? $[ with $H:ident]?) => do
  let H := H.map (·.getId) |>.getD `this
  let h := h.getId
  let P ← elabType P
  let goal ← getMainGoal
  /- Compute the type of H and keep track of the FVarId's reverted in doing so. (Do not modify the
  tactic state.) -/
  let (revertedFVars, HType) ← withoutModifyingState <| goal.withContext do
    let newGoal ← goal.assert h P (← mkFreshExprMVar P)
    let lctx := (← newGoal.getDecl).lctx
    let toRevert ← match xs with
    | some xs => getFVarIdsAt newGoal xs
    | none => pure lctx.getFVarIds
    let toRevert := toRevert.filter (fun fvar => ! (lctx.fvarIdToDecl.find! fvar).isAuxDecl)
    --!! use preserveOrder := true?
    let (revertedFVars, goal) ← newGoal.revert toRevert (clearAuxDeclsInsteadOfRevert := true)
    return (revertedFVars, ← goal.getType)
  /- Set up the goal which will suppose `h`; this begins as a goal with type H (hence HExpr), and h
  is obtained through `introN` -/
  --!! Natural mvarkind ok?
  let HExpr ← mkFreshExprMVar HType
  let hBranch := HExpr.mvarId!
  /- Begin the "reduction branch" which will contain hypotheses `H` and `¬h`. For now, it only
  contains `H`. `HFVarId -/
  let (HFVarId, reductionBranch) ← goal.assertHypotheses #[⟨H, HType, HExpr⟩]
  let HFVarId := HFVarId[0]!
  /- Clear the reverted fvars from the branch that will contain `h` as a hypothesis. -/
  let hBranch ← hBranch.tryClearMany revertedFVars --!! move before?
  /- Introduce all of the reverted fvars to the context in order to restore the original target as
  well as finally introduce the hypothesis `h`. -/
  let (_, hBranch) ← hBranch.introNP (revertedFVars.size + 1)
  /- Split the reduction branch by cases on `h`. Keep the one with `¬h` as the reduction branch,
  and prove the easy branch by applying `H` to all its premises, which are fvars in the context. -/
  let (⟨easyBranch, hyp⟩, ⟨reductionBranch, _⟩) ← reductionBranch.byCases P h
  easyBranch.withContext do
    let HApp ← instantiateMVars <|
      mkAppN (.fvar HFVarId) (revertedFVars.map .fvar) |>.app (.fvar hyp)
    ensureHasNoMVars HApp
    easyBranch.assign HApp --!! Should we weaken the mvarkind to synthetic and use isDefEq?
  replaceMainGoal [reductionBranch, hBranch]
