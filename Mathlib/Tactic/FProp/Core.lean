/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Lean
import Qq
import Mathlib.Tactic.FProp.FPropAttr

namespace Mathlib
open Lean Meta Qq

namespace Meta.FProp


private def _root_.Lean.Meta.letTelescopeImpl {α} (e : Expr) (k : Array Expr → Expr → MetaM α) : MetaM α := 
  lambdaLetTelescope e λ xs b => do
    if let .some i ← xs.findIdxM? (λ x => do pure ¬(← x.fvarId!.isLetVar)) then
      k xs[0:i] (← mkLambdaFVars xs[i:] b)
    else
      k xs b

private def _root_.Lean.Meta.letTelescope {α n} [MonadControlT MetaM n] [Monad n] (e : Expr) (k : Array Expr → Expr → n α) : n α := 
  map2MetaM (fun k => letTelescopeImpl e k) k

-- TODO: fix the implementation in STD
def _root_.Lean.Expr.modArgRev (modifier : Expr → Expr) (i : Nat) (e : Expr) : Expr :=
  match i, e with
  |      0, .app f x => .app f (modifier x)
  | (i'+1), .app f x => .app (modArgRev modifier i' f) x
  | _, _ => e

-- TODO: fix the implementation in STD
def _root_.Lean.Expr.modArg (modifier : Expr → Expr) (i : Nat) (e : Expr) (n := e.getAppNumArgs) : Expr :=
  Expr.modArgRev modifier (n - i - 1) e

-- TODO: fix the implementation in STD
def _root_.Lean.Expr.setArg (e : Expr) (i : Nat) (x : Expr) (n := e.getAppNumArgs) : Expr :=
  e.modArg (fun _ => x) i n



def letCase (decl : FPropDecl) (e : Expr) (f : Expr) (fprop : Expr → FPropM (Option Result)) : FPropM (Option Result) := do
  return none

def bvarAppCase (decl : FPropDecl) (e : Expr) (f : Expr) (fprop : Expr → FPropM (Option Result)) : FPropM (Option Result) := do
  return none

def fvarAppCase (decl : FPropDecl) (e : Expr) (f : Expr) (fprop : Expr → FPropM (Option Result)) : FPropM (Option Result) := do
  return none

def constAppCase (decl : FPropDecl) (e : Expr) (f : Expr) (fprop : Expr → FPropM (Option Result)) : FPropM (Option Result) := do
  return none

-- cache if there are no subgoals
def maybeCache (e : Expr) (r : Result) : FPropM (Option Result) := do -- return proof?
  if r.subgoals.length = 0 then
    modify (fun s => { s with cache := s.cache.insert e { expr := q(True), proof? := r.proof} })
  return r

mutual 
  partial def fprop (e : Expr) : FPropM (Option Result) := do

    -- check cache
    if let .some { expr := _, proof? := .some proof } := (← get).cache.find? e then
      trace[Meta.Tactic.fprop.cache] "cached result for {e}"
      return .some { proof := proof, subgoals := [] }

    else
      -- take care of forall and let binders and run main
      match e with
      | .letE .. => 
        letTelescope e fun xs b => do
          let .some r ← fprop b
            | return none
          maybeCache e {proof := ← mkLambdaFVars xs r.proof, subgoals := r.subgoals}
      | .forallE .. => 
        forallTelescope e fun xs b => do
          let .some r ← fprop b
            | return none
          maybeCache e {proof := ← mkLambdaFVars xs r.proof, subgoals := r.subgoals}
      | .mdata _ e' => fprop e'
      | .mvar _ => instantiateMVars e >>= fprop
      | _ => 
        let .some r ← main e
          | return none
        maybeCache e r
        

  partial def main (e : Expr) : FPropM (Option Result) := do

    let .some (decl, f) ← getFProp? e
      | return none

    let f := f.consumeMData

    match f with
    | .letE .. => letTelescope f fun xs b => do 
      trace[Meta.Tactic.fprop.step] "case `P (let x := ..; f)`\n{← ppExpr e}"
      let e' := e.setArg decl.funArgId b
      fprop (← mkLambdaFVars xs e')

    | .lam xName xType xBody xBi => 

      match xBody.consumeMData.headBeta.consumeMData with
      | (.bvar 0) => 
        trace[Meta.Tactic.fprop.step] "case `P (fun x => x)\n{← ppExpr e}"
        applyIdRule decl e xType

      | .letE .. => 
        trace[Meta.Tactic.fprop.step] "case `P (fun x => let y := ..; ..)\n{← ppExpr e}"
        letCase decl e f fprop

      | .lam  .. => 
        trace[Meta.Tactic.fprop.step] "case `P (fun x y => f x y)`\n{← ppExpr e}"
        applyPiRule decl e f

      | .mvar .. => fprop (← instantiateMVars e)

      | xBody => do
        if !(xBody.hasLooseBVar 0) then
          trace[Meta.Tactic.fprop.step] "case `P (fun x => y)`\n{← ppExpr e}"
          applyConstRule decl e xType xBody
        else 
          let f' := Expr.lam xName xType xBody xBi
          let g := xBody.getAppFn

          match g with 
          | .fvar .. => 
            trace[Meta.Tactic.fprop.step] "case `P (fun x => f x)` where `f` is free variable\n{← ppExpr e}"
            fvarAppCase decl e f' fprop
          | .bvar .. => 
            trace[Meta.Tactic.fprop.step] "case `P (fun f => f x)`\n{← ppExpr e}"
            bvarAppCase decl e f' fprop
          | .mvar .. => 
            fprop (← instantiateMVars e)
          | .proj .. => do
            trace[Meta.Tactic.fprop.step] "case `P (fun x => x.#)`\n{← ppExpr e}"
            constAppCase decl e f' fprop
          | .const .. =>
            trace[Meta.Tactic.fprop.step] "case `P (fun x => f x)` where `f` is declared function\n{← ppExpr e}"
            constAppCase decl e f' fprop
          | _ => 
            trace[Meta.Tactic.fprop.step] "unknown case, app function {← ppExpr g} has constructor: {g.ctorName} \n{← ppExpr e}\n"
            constAppCase decl e f' fprop

    | .mvar _ => do
      fprop (← instantiateMVars e)

    | f => do
      let f' ← etaExpand f
      trace[Meta.Tactic.fprop.step] "eta expanding function in\n{← ppExpr e}"
      fprop (e.setArg decl.funArgId f')

end
