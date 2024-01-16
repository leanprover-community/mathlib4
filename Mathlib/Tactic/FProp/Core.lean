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


----------------------------------------------------------------------------------------------------


def synthesizeInstance (thmId : Origin) (x type : Expr) : MetaM Bool := do
  match (← trySynthInstance type) with
  | LOption.some val =>
    if (← withReducibleAndInstances <| isDefEq x val) then
      return true
    else
      trace[Meta.Tactic.fprop.discharge] "{← ppOrigin thmId}, failed to assign instance{indentExpr type}\nsythesized value{indentExpr val}\nis not definitionally equal to{indentExpr x}"
      return false
  | _ =>
    trace[Meta.Tactic.fprop.discharge] "{← ppOrigin thmId}, failed to synthesize instance{indentExpr type}"
    return false


/-- Synthesize arguments `xs` either with typeclass synthesis, with fprop or with discharger.
If succesfull it returns list of subgoals that should be presented to the user.
If fails it returns `none`. -/
def synthesizeArgs (thmId : Origin) (xs : Array Expr) (bis : Array BinderInfo) 
  (discharge? : Expr → MetaM (Option Expr)) (fprop : Expr → FPropM (Option Result)) 
  : FPropM (Option (List MVarId)) := do
  let mut subgoals : List MVarId := []
  for x in xs, bi in bis do
    let type ← inferType x
    if bi.isInstImplicit then
      unless (← synthesizeInstance thmId x type) do
        return .none
    else if (← instantiateMVars x).isMVar then

      -- try type class
      if (← isClass? type).isSome then
        if (← synthesizeInstance thmId x type) then
          continue

      -- try function property
      if (← isFProp type.getForallBody) then
        if let .some ⟨proof, subgoals'⟩ ← fprop (← instantiateMVars type) then
          subgoals := subgoals ++ subgoals'
          if (← isDefEq x proof) then
            continue
          else do
            trace[Meta.Tactic.fprop.discharge] "{← ppOrigin thmId}, failed to assign proof{indentExpr type}"
            return none

      -- try discharger
      if (← isProp type) then
        if let .some proof ← discharge? type then
          if (← isDefEq x proof) then
            continue 
          else do
            trace[Meta.Tactic.fprop.discharge] "{← ppOrigin thmId}, failed to assign proof{indentExpr type}"
            return none

      trace[Meta.Tactic.fprop.discharge] "{← ppOrigin thmId}, failed to discharge hypotheses{indentExpr type}"
      return none

  return .some subgoals


def tryTheoremCore (xs : Array Expr) (bis : Array BinderInfo) (val : Expr) (type : Expr) (e : Expr) (thmId : Origin) 
  (discharge? : Expr → MetaM (Option Expr)) (fprop : Expr → FPropM (Option Result)) : FPropM (Option Result) := do
  if (← isDefEq type e) then
    let .some subgoals ← synthesizeArgs thmId xs bis discharge? fprop | return none
    let proof ← instantiateMVars (mkAppN val xs)

    -- TODO: check that the only mvars in proof are subgoals
    if subgoals.length == 0 && (← hasAssignableMVar proof) then 
      trace[Meta.Tactic.fprop.apply] "{← ppOrigin thmId}, has unassigned metavariables after unification"
      return none

    trace[Meta.Tactic.fprop.apply] "{← ppOrigin thmId}, \n{e}"
    return .some { proof := proof, subgoals := subgoals}
  else
    trace[Meta.Tactic.fprop.unify] "failed to unify {← ppOrigin thmId}\n{type}\nwith\n{e}"
    return none


def tryTheorem? (e : Expr) (thmProof : Expr) (thmId : Origin)
  (discharge? : Expr → MetaM (Option Expr)) (fprop : Expr → FPropM (Option Result)) : FPropM (Option Result) := do
  withNewMCtxDepth do
    let type ← instantiateMVars (← inferType thmProof)
    let (xs, bis, type) ← forallMetaTelescope type
    tryTheoremCore xs bis thmProof type e thmId discharge? fprop


def applyIdRule (fpropDecl : FPropDecl) (e X : Expr) 
  (fprop : Expr → FPropM (Option Result)) : FPropM (Option Result) := do 

  let ext := fpropLambdaTheoremsExt.getState (← getEnv)
  let .some thm := ext.theorems.find? (fpropDecl.fpropName, .id) 
    | return none
  let .id id_X := thm.thrmArgs | return none
  
  let type ← instantiateMVars (← inferType thm.proof)
  let (xs, bis, type) ← forallMetaTelescope type

  xs[id_X]!.mvarId!.assign X

  tryTheoremCore xs bis thm.proof type e (.decl thm.thrmName) fpropDecl.discharger fprop


def applyConstRule (fpropDecl : FPropDecl) (e X y : Expr) 
  (fprop : Expr → FPropM (Option Result)) : FPropM (Option Result) := do 

  let ext := fpropLambdaTheoremsExt.getState (← getEnv)
  let .some thm := ext.theorems.find? (fpropDecl.fpropName, .const) | return none
  let .const id_X id_y := thm.thrmArgs | return none
  
  let type ← instantiateMVars (← inferType thm.proof)
  let (xs, bis, type) ← forallMetaTelescope type

  xs[id_X]!.mvarId!.assign X
  xs[id_y]!.mvarId!.assign y

  tryTheoremCore xs bis thm.proof type e (.decl thm.thrmName) fpropDecl.discharger fprop


def applyProjRule (fpropDecl : FPropDecl) (e x Y : Expr) 
  (fprop : Expr → FPropM (Option Result)) : FPropM (Option Result) := do 

  let ext := fpropLambdaTheoremsExt.getState (← getEnv)
  let .some thm := ext.theorems.find? (fpropDecl.fpropName, .proj) | return none
  let .proj id_x id_Y := thm.thrmArgs | return none
  
  let type ← instantiateMVars (← inferType thm.proof)
  let (xs, bis, type) ← forallMetaTelescope type

  xs[id_x]!.mvarId!.assign x
  xs[id_Y]!.mvarId!.assign Y

  tryTheoremCore xs bis thm.proof type e (.decl thm.thrmName) fpropDecl.discharger fprop


def applyProjDepRule (fpropDecl : FPropDecl) (e x Y : Expr)
  (fprop : Expr → FPropM (Option Result)) : FPropM (Option Result) := do 

  let ext := fpropLambdaTheoremsExt.getState (← getEnv)
  let .some thm := ext.theorems.find? (fpropDecl.fpropName, .projDep) | return none
  let .projDep id_x id_Y := thm.thrmArgs | return none
  
  let type ← instantiateMVars (← inferType thm.proof)
  let (xs, bis, type) ← forallMetaTelescope type

  xs[id_x]!.mvarId!.assign x
  xs[id_Y]!.mvarId!.assign Y

  tryTheoremCore xs bis thm.proof type e (.decl thm.thrmName) fpropDecl.discharger fprop


def applyCompRule (fpropDecl : FPropDecl) (e f g : Expr)
  (fprop : Expr → FPropM (Option Result)) : FPropM (Option Result) := do 

  let ext := fpropLambdaTheoremsExt.getState (← getEnv)
  let .some thm := ext.theorems.find? (fpropDecl.fpropName, .comp) | return none
  let .comp id_f id_g := thm.thrmArgs | return none
  
  let type ← instantiateMVars (← inferType thm.proof)
  let (xs, bis, type) ← forallMetaTelescope type

  xs[id_f]!.mvarId!.assign f
  xs[id_g]!.mvarId!.assign g

  tryTheoremCore xs bis thm.proof type e (.decl thm.thrmName) fpropDecl.discharger fprop


def applyLetRule (fpropDecl : FPropDecl) (e f g : Expr) 
  (fprop : Expr → FPropM (Option Result)) : FPropM (Option Result) := do 

  let ext := fpropLambdaTheoremsExt.getState (← getEnv)
  let .some thm := ext.theorems.find? (fpropDecl.fpropName, .letE) | return none
  let .letE id_f id_g := thm.thrmArgs | return none
  
  let type ← instantiateMVars (← inferType thm.proof)
  let (xs, bis, type) ← forallMetaTelescope type

  xs[id_f]!.mvarId!.assign f
  xs[id_g]!.mvarId!.assign g

  tryTheoremCore xs bis thm.proof type e (.decl thm.thrmName) fpropDecl.discharger fprop


def applyPiRule (fpropDecl : FPropDecl) (e f : Expr)
  (fprop : Expr → FPropM (Option Result)) : FPropM (Option Result) := do 

  let ext := fpropLambdaTheoremsExt.getState (← getEnv)
  let .some thm := ext.theorems.find? (fpropDecl.fpropName, .pi) | return none
  let .pi id_f := thm.thrmArgs | return none
  
  let type ← instantiateMVars (← inferType thm.proof)
  let (xs, bis, type) ← forallMetaTelescope type

  xs[id_f]!.mvarId!.assign f

  tryTheoremCore xs bis thm.proof type e (.decl thm.thrmName) fpropDecl.discharger fprop


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

    let .some (fpropDecl, f) ← getFProp? e
      | return none

    let f := f.consumeMData

    match f with
    | .letE .. => letTelescope f fun xs b => do 
      trace[Meta.Tactic.fprop.step] "case `P (let x := ..; f)`\n{← ppExpr e}"
      let e' := e.setArg fpropDecl.funArgId b
      fprop (← mkLambdaFVars xs e')

    | .lam xName xType xBody xBi => 

      match xBody.consumeMData.headBeta.consumeMData with
      | (.bvar 0) => 
        trace[Meta.Tactic.fprop.step] "case `P (fun x => x)\n{← ppExpr e}"
        applyIdRule fpropDecl e xType fprop

      | .letE .. => 
        trace[Meta.Tactic.fprop.step] "case `P (fun x => let y := ..; ..)\n{← ppExpr e}"
        letCase fpropDecl e f fprop

      | .lam  .. => 
        trace[Meta.Tactic.fprop.step] "case `P (fun x y => f x y)`\n{← ppExpr e}"
        applyPiRule fpropDecl e f fprop

      | .mvar .. => fprop (← instantiateMVars e)

      | xBody => do
        if !(xBody.hasLooseBVar 0) then
          trace[Meta.Tactic.fprop.step] "case `P (fun x => y)`\n{← ppExpr e}"
          applyConstRule fpropDecl e xType xBody fprop
        else 
          let f' := Expr.lam xName xType xBody xBi
          let g := xBody.getAppFn

          match g with 
          | .fvar .. => 
            trace[Meta.Tactic.fprop.step] "case `P (fun x => f x)` where `f` is free variable\n{← ppExpr e}"
            fvarAppCase fpropDecl e f' fprop
          | .bvar .. => 
            trace[Meta.Tactic.fprop.step] "case `P (fun f => f x)`\n{← ppExpr e}"
            bvarAppCase fpropDecl e f' fprop
          | .mvar .. => 
            fprop (← instantiateMVars e)
          | .proj .. => do
            trace[Meta.Tactic.fprop.step] "case `P (fun x => x.#)`\n{← ppExpr e}"
            constAppCase fpropDecl e f' fprop
          | .const .. =>
            trace[Meta.Tactic.fprop.step] "case `P (fun x => f x)` where `f` is fpropDeclared function\n{← ppExpr e}"
            constAppCase fpropDecl e f' fprop
          | _ => 
            trace[Meta.Tactic.fprop.step] "unknown case, app function {← ppExpr g} has constructor: {g.ctorName} \n{← ppExpr e}\n"
            constAppCase fpropDecl e f' fprop

    | .mvar _ => do
      fprop (← instantiateMVars e)

    | f => do
      let f' ← etaExpand f
      trace[Meta.Tactic.fprop.step] "eta expanding function in\n{← ppExpr e}"
      fprop (e.setArg fpropDecl.funArgId f')

end
