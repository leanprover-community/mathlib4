/-
Copyright (c) 2023 Alex Keizer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Keizer
-/
import Lean
import Qq
import Mathlib.Logic.Equiv.Defs

/-!
# The `rw_equiv` tactic

Given an equivalence `α ≃ β`, rewrite the type of variables `x : α` in the local context to `x : β`.
The tactic performs roughly the following steps:
  * rewrite `x` to `invFun (toFun x)`
  * `generalize toFun x = x`
  * Clear the original, now-shadowed, declaration of `x` from the context
-/

namespace Mathlib.Tactic.RewriteEquiv
open Lean Elab Meta Tactic
open Qq

/-- Rewrite the type of variables `x : α` in the local context along an equivalence `α ≃ β` -/
def rewriteEquiv (α : Q(Sort u)) (β : Q(Sort v)) (eqv : Q($α ≃ $β)) : TacticM Unit := do
  let mut genArgs : Array GeneralizeArg := #[]
  let mut clearIds : Array FVarId := #[]

  let ctx ← getLCtx
  for decl in ctx do
    if ←isDefEq decl.type α then
      -- HACK: `Qq` doesn't like it if the following is `let` instead of `have`
      have var : Q($α) := decl.toExpr

      -- Rewrite `$var` to `invFun <| toFun $var`
      let newVar : Q($β) := q(Equiv.toFun $eqv <| $var)
      let eq : Q($var = (Equiv.invFun $eqv $newVar)) :=
        q(Eq.symm <| Equiv.left_inv $eqv $var)
      let r ← (← getMainGoal).rewrite (← getMainTarget) eq false
      let mvarId' ← (← getMainGoal).replaceTargetEq r.eNew r.eqProof
      replaceMainGoal (mvarId' :: r.mvarIds)

      -- Record the arguments needed to generalize `toFun $var`
      genArgs := genArgs.push {
        expr    := newVar
        xName?  := decl.userName
      }
      clearIds := clearIds.push decl.fvarId

  if genArgs.isEmpty then
    throwError "tactic `rw_equiv` failed, did not find any local variables of type\n\t{α}"

  -- Perform the generalizations recorded in `genArgs`, and clear the variables in `clear`
  withMainContext <| do
    let (_, _, mvarId) ← (←getMainGoal).generalizeHyp genArgs (←getLCtx).getFVarIds
    let mvarId ← mvarId.tryClearMany clearIds
    replaceMainGoal [mvarId]

/-- Rewrite the type of variables `x : α` in the local context along an equivalence `α ≃ β` -/
elab "rw_equiv " "[" eqvs:term,* "]" : tactic => do
  for eqv in eqvs.getElems do
    withMainContext <| withRef eqv <| do
      let u ← mkFreshLevelMVar;
      let v ← mkFreshLevelMVar;
      let α : Q(Sort u) ← mkFreshExprMVarQ q(Sort u);
      let β : Q(Sort v) ← mkFreshExprMVarQ q(Sort v);
      let eqv : Q($α ≃ $β) ← elabTermEnsuringTypeQ eqv q($α ≃ $β)
      rewriteEquiv α β eqv

end Mathlib.Tactic.RewriteEquiv
