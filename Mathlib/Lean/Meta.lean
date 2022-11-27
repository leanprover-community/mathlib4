/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Elab
import Lean.Meta.Tactic.Assert
import Lean.Meta.Tactic.Clear
import Mathlib.Util.MapsTo

/-! ## Additional utilities in `Lean.MVarId` -/

open Lean Meta

namespace Lean.MVarId

/--
Replace hypothesis `hyp` in goal `g` with `proof : typeNew`.
The new hypothesis is given the same user name as the original,
it attempts to avoid reordering hypotheses, and the original is cleared if possible.
-/
-- adapted from Lean.Meta.replaceLocalDeclCore
def replace (g : MVarId) (hyp : FVarId) (typeNew proof : Expr) :
    MetaM AssertAfterResult :=
  g.withContext do
    let ldecl ← hyp.getDecl
    -- `typeNew` may contain variables that occur after `hyp`.
    -- Thus, we use the auxiliary function `findMaxFVar` to ensure `typeNew` is well-formed
    -- at the position we are inserting it.
    let (_, ldecl') ← findMaxFVar typeNew |>.run ldecl
    let result ← g.assertAfter ldecl'.fvarId ldecl.userName typeNew proof
    (return { result with mvarId := ← result.mvarId.clear hyp }) <|> pure result
where
  /-- Finds the `LocalDecl` for the FVar in `e` with the highest index. -/
  findMaxFVar (e : Expr) : StateRefT LocalDecl MetaM Unit :=
    e.forEach' fun e ↦ do
      if e.isFVar then
        let ldecl' ← e.fvarId!.getDecl
        modify fun ldecl ↦ if ldecl'.index > ldecl.index then ldecl' else ldecl
        return false
      else
        return e.hasFVar

/-- Has the effect of `refine ⟨e₁,e₂,⋯, ?_⟩`.
-/
def existsi (mvar : MVarId) (es : List Expr) : MetaM MVarId := do
  es.foldlM (λ mv e => do
      let (subgoals,_) ← Elab.Term.TermElabM.run $ Elab.Tactic.run mv do
        Elab.Tactic.evalTactic (←`(tactic| refine ⟨?_,?_⟩))
      let [sg1, sg2] := subgoals | throwError "expected two subgoals"
      sg1.assign e
      pure sg2)
    mvar

end Lean.MVarId

namespace Lean.Elab.Tactic

/-- Analogue of `liftMetaTactic` for tactics that do not return any goals. -/
def liftMetaFinishingTactic (tac : MVarId → MetaM Unit) : TacticM Unit :=
  liftMetaTactic fun g => do tac g; pure []

end Lean.Elab.Tactic
