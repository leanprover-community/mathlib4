/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Qq

/-!
## `funTrans` environment extension that stores all registered function properties
-/


namespace Mathlib
open Lean Meta

namespace Meta.FunTrans



initialize registerTraceClass `Meta.Tactic.fun_trans.attr
initialize registerTraceClass `Meta.Tactic.fun_trans

initialize registerTraceClass `Meta.Tactic.fun_trans.step
initialize registerTraceClass `Meta.Tactic.fun_trans.unify
initialize registerTraceClass `Meta.Tactic.fun_trans.discharge
initialize registerTraceClass `Meta.Tactic.fun_trans.rewrite
initialize registerTraceClass `Meta.Tactic.fun_trans.unfold
initialize registerTraceClass `Meta.Tactic.fun_trans.cache



/-- Basic information about function transformation -/
structure FunTransDecl where
  /-- function transformation name -/
  funTransName : Name
  /-- path for discriminatory tree -/
  path : Array DiscrTree.Key
  /-- argument index of a function this function transformation talks about.
  For example, this would be 8 for `@fderiv 𝕜 _ E _ _ F _ _ f` -/
  funArgId : Nat
  deriving Inhabited, BEq

/-- -/
structure FunTransDecls where
  /-- discriminatory tree for function transformations -/
  decls : DiscrTree FunTransDecl := {}
  deriving Inhabited

/-- -/
abbrev FunTransDeclsExt := SimpleScopedEnvExtension FunTransDecl FunTransDecls

/-- -/
initialize funTransDeclsExt : FunTransDeclsExt ←
  registerSimpleScopedEnvExtension {
    name := by exact decl_name%
    initial := {}
    addEntry := fun d e =>
      {d with decls := d.decls.insertCore e.path e}
  }

/-- -/
def addFunTransDecl (declName : Name) : MetaM Unit := do

  let info ← getConstInfo declName

  let (xs,_,b) ← forallMetaTelescope info.type

  -- find the argument position of the function `f` in `P f`
  let mut .some funArgId ← xs.reverse.findIdxM? fun x => do
    if (← inferType x).isForall then
      return true
    else
      return false
    | throwError "invalid fun_trans declaration, can't find argument of type `α → β`"
  funArgId := xs.size - funArgId - 1

  let lvls := info.levelParams.map (fun l => Level.param l)
  let e := mkAppN (.const declName lvls) xs[0:funArgId+1]
  let path ← DiscrTree.mkPath e {}

  let decl : FunTransDecl := {
    funTransName := declName
    path := path
    funArgId := funArgId
  }

  modifyEnv fun env => funTransDeclsExt.addEntry env decl

  trace[Meta.Tactic.fun_trans.attr]
    "added new function property `{declName}`\nlook up pattern is `{path}`"


/-- -/
def getFunTrans? (e : Expr) : MetaM (Option (FunTransDecl × Expr)) := do
  unless e.isApp do return .none

  let ext := funTransDeclsExt.getState (← getEnv)

  let decls ← ext.decls.getMatchWithExtra e
    {zeta:=false,zetaDelta:=false,proj:=.no,iota:=false,beta:=false}

  if decls.size = 0 then
    return none

  if decls.size > 1 then
    throwError "\
fun_trans bug: expression {← ppExpr e} matches multiple function transformations
{decls.map (fun d => d.1.funTransName)}"

  let decl := decls[0]!.fst
  let f := e.getArg! decl.funArgId

  return (decl,f)

/-- -/
def isFunTrans (e : Expr) : MetaM Bool := do return (← getFunTrans? e).isSome

/-- Returns function property transformation from `e = T f`. -/
def getFunTransDecl? (e : Expr) : MetaM (Option FunTransDecl) := do
  match ← getFunTrans? e with
  | .some (decl,_) => return decl
  | .none => return none


/-- Returns function `f` from `e = T f` and `T` is function transformation. -/
def getFunTransFun? (e : Expr) : MetaM (Option Expr) := do
  match ← getFunTrans? e with
  | .some (_,f) => return f
  | .none => return none
