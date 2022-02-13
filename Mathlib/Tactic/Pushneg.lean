/-
Copyright (c) 2022 Alice Laroche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alice Laroche
-/

import Lean
import Lean.Meta
import Lean.Elab
import Mathlib.Lean.Expr
import Mathlib.Logic.Basic

namespace Mathlib.Tactic

open Lean Meta Elab.Tactic Parser.Tactic
open Lean.Expr
open Lean.Elab.Term


theorem not_not_eq (h : p = p') : (¬¬p) = p' := h ▸ (propext not_not)
theorem not_and_eq (h : p = p')    (h' : (¬q) = q') : (¬ (p ∧ q)) = (p' → q') := h ▸ h' ▸ propext not_and
theorem not_or_eq  (h : (¬p) = p') (h' : (¬q) = q') : (¬ (p ∨ q)) = (p' ∧ q') := h ▸ h' ▸ propext not_or_distrib
theorem not_forall_eq {s s' : α -> Prop} (h : ∀x, (¬s x) = s' x) : (¬ ∀x, s x) = (∃ x, s' x) := funext h ▸ propext not_forall
theorem not_exists_eq {s s' : α -> Prop} (h : ∀x, (¬s x) = s' x) : (¬ ∃x, s x) = (∀ x, s' x) := forall_congr h ▸ propext not_exists

def myTelescope (e : Expr) (f : Expr -> Expr -> MetaM α) : MetaM α := do
match e with
| Expr.lam n t b d => withLocalDecl n d.binderInfo t fun x => f x (instantiate1 b x)
| Expr.forallE n t b d => withLocalDecl n d.binderInfo t fun x => f x (instantiate1 b x)
| _ => throwError "binder expected{indentExpr e}"

partial def pushNegation (expr : Expr) : MetaM (Expr × Expr) := do
match expr with
| Expr.forallE n t b _ =>
   myTelescope expr fun x e => do
      let (eNew, eqProof) <- pushNegation e
      if eqProof.isAppOf ``Eq.refl
      then return (expr, <- mkEqRefl expr)
      else return (<-mkForallFVars #[x] eNew, <- mkForallCongr (<-mkLambdaFVars #[x] eqProof))
| Expr.lam n t b _ =>
   myTelescope expr fun x e => do
      let (eNew, eqProof) <- pushNegation e
      if eqProof.isAppOf ``Eq.refl
      then return (expr, <- mkEqRefl expr)
      else return (<-mkLambdaFVars #[x] eNew, <- mkFunExt (<-mkLambdaFVars #[x] eqProof))
| Expr.app e₁ e₂ _ =>
   match expr.not? with
   | some expr' =>
      match expr'.getAppFnArgs with
      | (`Not, #[e]) =>
         let (eNew, eqProof) <- pushNegation e
         let eqProof <- mkAppOptM ``not_not_eq #[none, none, eqProof]
         return (eNew, eqProof)
      | (`And, #[p, q]) =>
         let (p, eqProof₁) <- pushNegation p
         let (q, eqProof₂) <- pushNegation (mkNot q)
         let eNew := mkForall `_ default p q
         let eqProof <- mkAppOptM ``not_and_eq #[none, none,none, none, eqProof₁, eqProof₂]
         return (eNew, eqProof)
      | (`Or, #[p, q]) =>
         let (p, eqProof₁) <- pushNegation (mkNot p)
         let (q, eqProof₂) <- pushNegation (mkNot q)
         let eNew := mkAnd p q
         let eqProof <- mkAppOptM ``not_or_eq #[none, none,none, none, eqProof₁, eqProof₂]
         return (eNew, eqProof)
      | (`Exists, #[t, e]) =>
         myTelescope e fun x e => do
            let (eNew, eqProof) <- pushNegation (mkNot e)
            let eNew <- mkForallFVars #[x] eNew
            let eqProof <- mkLambdaFVars #[x] eqProof
            let eqProof <- mkAppOptM ``not_exists_eq #[none, none, none, eqProof]
            return (eNew, eqProof)
      | _ => match expr' with
         | Expr.forallE _ t _ _ =>
            myTelescope expr' fun x e => do
               let (eNew, eqProof) <- pushNegation (mkNot e)
               let eNew <- mkLambdaFVars #[x] eNew
               let level <- getLevel (<-inferType eNew)
               let eNew := mkAppN (mkConst ``Exists [level]) #[t, eNew]
               let eqProof <- mkLambdaFVars #[x] eqProof
               let eqProof <- mkAppOptM ``not_forall_eq #[none, none, none, eqProof]
               return (eNew, eqProof)
         | _ =>
            let (eNew, eqProof) <- pushNegation expr'
            let eqProof <- mkCongr (<-mkEqRefl (mkConst `Not)) eqProof
            return (mkNot eNew, eqProof)
   | _ =>
      let (e₁', eqProof₁) <- pushNegation e₁
      let (e₂', eqProof₂) <- pushNegation e₂
      let eqProof <- mkCongr eqProof₁ eqProof₂
      return (mkApp e₁' e₂', eqProof)
| _ => return (expr, <-mkEqRefl expr)


def pushnegTarget : TacticM Unit := do
let target <- getMainTarget
let (eNew, eqProof) <- pushNegation target
if !eqProof.isAppOf ``Eq.refl
then
   let mvarId' <- replaceTargetEq (← getMainGoal) eNew eqProof
   replaceMainGoal [mvarId']
else
   throwError "Pushneg couldn't find a negation to push"

def pushNegLocalDecl (fvarId : FVarId): TacticM Unit := do
let target <- getLocalDecl fvarId
let (eNew, eqProof) <- pushNegation target.type
if ! eqProof.isAppOf ``Eq.refl
then
   let mvarId' <- replaceLocalDecl (← getMainGoal) fvarId  eNew eqProof
   replaceMainGoal [mvarId'.mvarId]
else
   throwError "Pushneg couldn't find a negation to push"

elab "push_neg " loc:(ppSpace location)? : tactic => do
let loc := expandOptLocation loc
withLocation loc
  pushNegLocalDecl
  pushnegTarget
  (fun _ => throwError "Pushneg couldn't find a negation to push")
