/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Qq
import Mathlib.Tactic.FProp.FPropTypes


namespace Mathlib
open Lean Meta

namespace Meta.FProp


/-- Basic information about function property

To use `fprop` to prove a function property `P : (α→β)→Prop` one has to provide `FPropDecl`.
-/
structure FPropDecl where
  /-- function transformation name -/
  fpropName : Name
  /-- path for discriminatory tree -/
  path : Array DiscrTree.Key
  /-- argument index of a function this function property talks about. For example, this would be 4 for `@Continuous α β _ _ f` -/
  funArgId : Nat
  /-- Custom discharger for this function property. -/
  dischargeStx? : Option Syntax
  deriving Inhabited, BEq

structure FPropDecls where
  decls : DiscrTree FPropDecl := {}
  deriving Inhabited

abbrev FPropDeclsExt := SimpleScopedEnvExtension FPropDecl FPropDecls

initialize fpropDeclsExt : FPropDeclsExt ←
  registerSimpleScopedEnvExtension {
    name := by exact decl_name%
    initial := {}
    addEntry := fun d e => 
      {d with decls := d.decls.insertCore e.path e {}}
  }



def addFPropDecl (declName : Name) (dischargeStx? : Option Syntax) : MetaM Unit := do

  let info ← getConstInfo declName

  let (xs,_,b) ← forallMetaTelescope info.type

  if ¬b.isProp then
    throwError "invalid fprop declaration, has to be `Prop` valued function"

  let lvls := info.levelParams.map (fun l => Level.param l)
  let e := mkAppN (.const declName lvls) xs
  let path ← DiscrTree.mkPath e {}

  -- find the argument position of the function `f` in `P f`
  let mut .some funArgId ← xs.reverse.findIdxM? fun x => do
    if (← inferType x).isForall then
      return true
    else
      return false
    | throwError "invalid fprop declaration, can't find argument of type `α → β`"
  funArgId := xs.size - funArgId - 1

  let decl : FPropDecl := {
    fpropName := declName
    path := path
    funArgId := funArgId
    dischargeStx? := dischargeStx?
  }

  modifyEnv fun env => fpropDeclsExt.addEntry env decl

  trace[Meta.Tactic.fprop.attr] "added new function property `{declName}`\nlook up pattern is `{path}`"

  

def getFProp? (e : Expr) : MetaM (Option (FPropDecl × Expr)) := do
  let ext := fpropDeclsExt.getState (← getEnv)

  let decls ← ext.decls.getMatch e {}

  if decls.size = 0 then
    return none

  if decls.size > 1 then
    throwError "expression {← ppExpr e} matches multiple function properties {decls.map (fun d => d.fpropName)}, this is a bug!"

  let decl := decls[0]!
  let f := e.getArg! decl.funArgId

  return (decl,f)

def isFProp (e : Expr) : MetaM Bool := do return (← getFProp? e).isSome

/-- Returns function property declaration from `e = P f`. -/
def getFPropDecl? (e : Expr) : MetaM (Option FPropDecl) := do
  match ← getFProp? e with
  | .some (decl,_) => return decl
  | .none => return none


/-- Returns function `f` from `e = P f` and `P` is function property. -/
def getFPropFun? (e : Expr) : MetaM (Option Expr) := do
  match ← getFProp? e with
  | .some (_,f) => return f
  | .none => return none





open Elab Term in
def tacticToDischarge (tacticCode : Syntax) : Expr → MetaM (Option Expr) := fun e => do
    let mvar ← mkFreshExprSyntheticOpaqueMVar e `simp.discharger
    let runTac? : TermElabM (Option Expr) :=
      try
        /- We must only save messages and info tree changes. Recall that `simp` uses temporary metavariables (`withNewMCtxDepth`).
           So, we must not save references to them at `Term.State`. -/
        withoutModifyingStateWithInfoAndMessages do
          instantiateMVarDeclMVars mvar.mvarId!

          let _ ←
            withSynthesize (mayPostpone := false) do Tactic.run mvar.mvarId! (Tactic.evalTactic tacticCode *> Tactic.pruneSolvedGoals)

          let result ← instantiateMVars mvar
          if result.hasExprMVar then
            return none
          else
            return some result
      catch _ =>
        return none
    let (result?, _) ← runTac?.run {} {} 
    
    return result?


def FPropDecl.discharger (fpropDecl : FPropDecl) (e : Expr) : MetaM (Option Expr) := do
    let .some stx := fpropDecl.dischargeStx?
      | return none
    tacticToDischarge stx e
