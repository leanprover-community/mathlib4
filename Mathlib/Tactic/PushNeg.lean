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
import Mathlib.Init.Algebra.Order

namespace Mathlib.Tactic

open Lean Meta Elab.Tactic Parser.Tactic
open Lean.Expr
open Lean.Elab.Term

variable (p q : Prop) (s : α → Prop)

theorem not_not_eq : (¬ ¬ p) = p := propext not_not
theorem not_and_eq : (¬ (p ∧ q)) = (p → ¬ q) := propext not_and
theorem not_or_eq : (¬ (p ∨ q)) = (¬ p ∧ ¬ q) := propext not_or_distrib
theorem not_forall_eq : (¬ ∀ x, s x) = (∃ x, ¬ s x) := propext not_forall
theorem not_exists_eq : (¬ ∃ x, s x) = (∀ x, ¬ s x) := propext not_exists
theorem not_implies_eq : (¬ (p → q)) = (p ∧ ¬ q) := propext not_imp

#check @not_forall_eq

variable {β : Type u} [LinearOrder β]
theorem not_le_eq (a b : β) : (¬ (a ≤ b)) = (b < a) := propext not_le
theorem not_lt_eq (a b : β) : (¬ (a < b)) = (b ≤ a) := propext not_lt

namespace Mathlib.Tactic.PushNeg

def mkSimpStep (e : Expr) (pf : Expr) : Simp.Step :=
  Simp.Step.visit { expr := e, proof? := some pf }

def transformNegationStep (e : Expr) : SimpM Simp.Step := do
  let e_whnf ← whnfR e
  let some ex := e_whnf.not? | return Simp.Step.visit { expr := e }
  match ex.getAppFnArgs with
  | (``Not, #[e]) =>
      return mkSimpStep e (←mkAppM ``not_not_eq #[e])
  | (``And, #[p, q]) =>
      return mkSimpStep (mkForall `_ default p (mkNot q)) (←mkAppM ``not_and_eq #[p, q])
  | (``Or, #[p, q]) =>
      return mkSimpStep (mkAnd (mkNot p) (mkNot q)) (←mkAppM ``not_or_eq #[p, q])
  | (``LE.le, #[_ty, _inst, e₁, e₂]) =>
      return mkSimpStep (← mkAppM ``LT.lt #[e₂, e₁]) (← mkAppM ``not_le_eq #[e₁, e₂])
  | (``LT.lt, #[_ty, _inst, e₁, e₂]) =>
      return mkSimpStep (← mkAppM ``LE.le #[e₂, e₁]) (← mkAppM ``not_lt_eq #[e₁, e₂])
  | (``Exists, #[_, e]) =>
      match e with
        | (Expr.lam n typ bo bi) => do
          return Simp.Step.visit
                 { expr := mkForall n bi typ (← mkAppM `Not #[bo]),
                   proof? := some (← mkAppM ``not_exists_eq #[e]) }
        | _ => return Simp.Step.visit { expr := e }
  | _ => match ex with
          | .forallE name ty body binfo => do
            let body' : Expr := .lam name ty (mkNot body) binfo
            let body'' : Expr := .lam name ty body binfo
            return Simp.Step.visit
                 { expr := ← mkAppM ``Exists #[body'],
                   proof? := ← mkAppM ``not_forall_eq #[body''] }
          | _ => return Simp.Step.visit { expr := e }

partial def transformNegation (e : Expr) : SimpM Simp.Step := do
  let Simp.Step.visit r₁ ← transformNegationStep e | unreachable!
  match r₁.proof? with
  | none => return Simp.Step.visit r₁
  | some _ => do
      let Simp.Step.visit r₂ ← transformNegation r₁.expr | unreachable!
      return Simp.Step.visit (← Simp.mkEqTrans r₁ r₂)

elab "test_push_neg" : tactic => withMainContext do
  let myctx : Simp.Context :=
    { config := { eta := true },
      simpTheorems := #[ ]
      congrTheorems := (← getSimpCongrTheorems) }
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← getMVarType goal)
  let myres := ← Simp.main tgt myctx (methods := { pre := transformNegation })
  --let myres := ← Simp.main tgt defctx (methods := Simp.DefaultMethods.methods)
  replaceMainGoal [← applySimpResultToTarget goal tgt myres]

example : ((fun x => x+x) 1) = 2 := by
  test_push_neg
  simp

example : ¬ ¬ p = p := by
  test_push_neg
  sorry

example (x y : β) : ¬(x ≤ y) := by
  test_push_neg
  sorry

example : ¬∃ (y : Nat), (y = 1) := by
  test_push_neg
  sorry

example (h : ∃ y : Nat, ¬(y=1)): ¬∀ (y : Nat), (y = 1) := by
  test_push_neg
  exact h

example (x y : β) : ¬¬¬ (x ≤ y) := by
  test_push_neg
  sorry

end Mathlib.Tactic.PushNeg

/-- This function is used to instantiate the bounded var of a binder and give it a local declaration
as a free var.\
We want this to be able to push negations inside binders.
-/
def withLocalFromBinder (e : Expr) (f : Expr → Expr → MetaM α) : MetaM α := do
  match e with
  | Expr.lam n t b d => withLocalDecl n d t fun x => f x (instantiate1 b x)
  | Expr.forallE n t b d => withLocalDecl n d t fun x => f x (instantiate1 b x)
  | _ => throwError "binder expected{indentExpr e}"

/-- This function takes an expression and create the equivalent expression by pushing negations
and a proof of the equality
The function distinguishes 4 cases :
- If the expression is a binder, then the function instantiates the bounded variable, and pushes possibles
negations in the subexpression
- If the expression is a negation, then the function tries to use one of the rewriting theorems,
if no one is suitable, leave the negation in place and pushes possibles negations in the subexpression
- If the expression is an application, then the function tries to push possibles negations in
both subexressions
- In other cases, the function just returns the expression and the reflexive equality
-/
partial def pushNegTransformStep (expr : Expr) : MetaM (Simp.Result) := do
  let expr ← whnfR expr
  match expr.not? with
  | some expr' =>
    match expr'.getAppFnArgs with
    | (`Not, #[e]) =>
      return { expr := e, proof? := some (← mkAppM ``not_not_eq #[e]) }
    | (`And, #[p, q]) =>
      return { expr := forallE `_ p (mkNot q) default,
               proof? := some (← mkAppM ``not_and_eq #[p, q])}
    | (`Or, #[p, q]) =>
      return { expr := mkAnd (mkNot p) (mkNot q),
               proof? := some (← mkAppM ``not_or_eq #[p]) }
    | (`Exists, #[_, e]) =>
      match e with
        | (Expr.lam n typ bo bi) => do
          return { expr := forallE n typ (← mkAppM `Not #[bo]) bi,
                   proof? := some (← mkAppM ``not_exists_eq #[e]) }
        | _ => return { expr := expr, proof? := none } -- should we throw an error instead?
    | _ => return { expr := expr, proof? := none }
  | none => return { expr := expr, proof? := none }

#exit

partial def pushNegation (expr : Expr) : MetaM (Expr × Expr) := do
  match expr with
  | Expr.forallE .. =>
    withLocalFromBinder expr fun x e => do
      let (eNew, eqProof) ← pushNegation e
      if eqProof.isAppOf ``Eq.refl
      then return (expr, ← mkEqRefl expr)
      else return (←mkForallFVars #[x] eNew, ← mkForallCongr (←mkLambdaFVars #[x] eqProof))
  | Expr.lam .. =>
    withLocalFromBinder expr fun x e => do
      let (eNew, eqProof) ← pushNegation e
      if eqProof.isAppOf ``Eq.refl
      then return (expr, ← mkEqRefl expr)
      else return (←mkLambdaFVars #[x] eNew, ← mkFunExt (←mkLambdaFVars #[x] eqProof))
  | Expr.app e₁ e₂ =>
     match expr.not? with
     | some expr' =>
        match expr'.getAppFnArgs with
        | (`Not, #[e]) =>
          let (eNew, eqProof) ← pushNegation e
          let eqProof ← mkAppOptM ``not_not_eq #[none, none, eqProof]
          return (eNew, eqProof)
        | (`And, #[p, q]) =>
          let (p, eqProof₁) ← pushNegation p
          let (q, eqProof₂) ← pushNegation (mkNot q)
          let eNew := mkForall `_ default p q
          let eqProof ← mkAppOptM ``not_and_eq #[none, none,none, none, eqProof₁, eqProof₂]
          return (eNew, eqProof)
        | (`Or, #[p, q]) =>
          let (p, eqProof₁) ← pushNegation (mkNot p)
          let (q, eqProof₂) ← pushNegation (mkNot q)
          let eNew := mkAnd p q
          let eqProof ← mkAppOptM ``not_or_eq #[none, none,none, none, eqProof₁, eqProof₂]
          return (eNew, eqProof)
        | (`Exists, #[_, e]) =>
          withLocalFromBinder e fun x e => do
            let (eNew, eqProof) ← pushNegation (mkNot e)
            let eNew ← mkForallFVars #[x] eNew
            let eqProof ← mkLambdaFVars #[x] eqProof
            let eqProof ← mkAppOptM ``not_exists_eq #[none, none, none, eqProof]
            return (eNew, eqProof)
        | _ => match expr' with
          | Expr.forallE _ t _ _ =>
            withLocalFromBinder expr' fun x e => do
              let (eNew, eqProof) ← pushNegation (mkNot e)
              let eNew ← mkLambdaFVars #[x] eNew
              let level ← getLevel (←inferType eNew)
              let eNew := mkAppN (mkConst ``Exists [level]) #[t, eNew]
              let eqProof ← mkLambdaFVars #[x] eqProof
              let eqProof ← mkAppOptM ``not_forall_eq #[none, none, none, eqProof]
              return (eNew, eqProof)
          | _ =>
            let (eNew, eqProof) ← pushNegation expr'
            let eqProof ← mkCongr (←mkEqRefl (mkConst `Not)) eqProof
            return (mkNot eNew, eqProof)
     | _ =>
        let (e₁', eqProof₁) ← pushNegation e₁
        let (e₂', eqProof₂) ← pushNegation e₂
        let eqProof ← mkCongr eqProof₁ eqProof₂
        return (mkApp e₁' e₂', eqProof)
  | _ => return (expr, ←mkEqRefl expr)


def pushnegTarget : TacticM Unit := do
  let target ← getMainTarget
  let (eNew, eqProof) ← pushNegation target
  if !eqProof.isAppOf ``Eq.refl
  then
    let mvarId' ← replaceTargetEq (← getMainGoal) eNew eqProof
    replaceMainGoal [mvarId']
  else
    logInfo "push_neg couldn't find a negation to push"

def pushNegLocalDecl (fvarId : FVarId): TacticM Unit := do
  let target ← getLocalDecl fvarId
  let (eNew, eqProof) ← pushNegation target.type
  if ! eqProof.isAppOf ``Eq.refl
  then
    let mvarId' ← replaceLocalDecl (← getMainGoal) fvarId  eNew eqProof
    replaceMainGoal [mvarId'.mvarId]
  else
    logInfo "push_neg couldn't find a negation to push"


/--
Push negations in the goal of some assumption.
For instance, a hypothesis `h : ¬ ∀ x, ∃ y, x ≤ y` will be transformed by `push_neg at h` into
`h : ∃ x, ∀ y, y < x`. Variables names are conserved.
This tactic pushes negations inside expressions. For instance, given an assumption
```lean
h : ¬ ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - y₀| ≤ ε)
```
writing `push_neg at h` will turn `h` into
```lean
h : ∃ ε, ε > 0 ∧ ∀ δ, δ > 0 → (∃ x, |x - x₀| ≤ δ ∧ ε < |f x - y₀|),
```
(the pretty printer does *not* use the abreviations `∀ δ > 0` and `∃ ε > 0` but this issue
has nothing to do with `push_neg`).
Note that names are conserved by this tactic, contrary to what would happen with `simp`
using the relevant lemmas. One can also use this tactic at the goal using `push_neg`,
at every assumption and the goal using `push_neg at *` or at selected assumptions and the goal
using say `push_neg at h h' ⊢` as usual.
-/
elab "push_neg " loc:(ppSpace location)? : tactic => do
  match loc with
  | none => pushnegTarget
  | some loc =>
      let loc := expandLocation loc
      withLocation loc
        pushNegLocalDecl
        (logInfo "here")
        (fun _ => logInfo "push_neg couldn't find a negation to push")

variable {α : Type} {p q : Prop} {p' q' : α → Prop}

example : (¬p ∧ ¬q) → ¬(p ∨ q) := by
  intro h
  push_neg
  exact h

example : ¬(p ∧ q) → (p → ¬q) :=by
  intro h
  push_neg at h
  exact h

example : (∀(x : α), ¬ p' x) → ¬ ∃(x : α), p' x:= by
  intro h
  push_neg
  exact h

example : (¬ ∀(x : α), p' x) → (∃(x : α), ¬ p' x) :=by
  intro h
  push_neg at h
  exact h

example (p : Bool) : decide (¬ ¬ p) = p := by push_neg
