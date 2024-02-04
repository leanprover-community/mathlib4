/-

Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Qq
import Std.Tactic.Where
import Mathlib.Tactic.Simps.Basic

/-!
## `funProp` environment extension that stores all registered function properties
-/


namespace Mathlib
open Lean Meta

namespace Meta.FunProp


/-- Basic information about function property

To use `funProp` to prove a function property `P : (α→β)→Prop` one has to provide `FunPropDecl`.
-/
structure FunPropDecl where
  /-- function transformation name -/
  funPropName : Name
  /-- path for discriminatory tree -/
  path : Array DiscrTree.Key
  /-- argument index of a function this function property talks about.
  For example, this would be 4 for `@Continuous α β _ _ f` -/
  funArgId : Nat
  /-- Custom discharger for this function property. -/
  dischargeStx? : Option (TSyntax `tactic)
  deriving Inhabited, BEq

/-- -/
structure FunPropDecls where
  /-- discriminatory tree for function properties -/
  decls : DiscrTree FunPropDecl := {}
  deriving Inhabited

/-- -/
abbrev FunPropDeclsExt := SimpleScopedEnvExtension FunPropDecl FunPropDecls

/-- -/
initialize funPropDeclsExt : FunPropDeclsExt ←
  registerSimpleScopedEnvExtension {
    name := by exact decl_name%
    initial := {}
    addEntry := fun d e =>
      {d with decls := d.decls.insertCore e.path e}
  }

/-- -/
def addFunPropDecl (declName : Name) (dischargeStx? : Option (TSyntax `tactic)) : MetaM Unit := do

  let info ← getConstInfo declName

  let (xs,_,b) ← forallMetaTelescope info.type

  if ¬b.isProp then
    throwError "invalid fun_prop declaration, has to be `Prop` valued function"

  let lvls := info.levelParams.map (fun l => Level.param l)
  let e := mkAppN (.const declName lvls) xs
  let path ← DiscrTree.mkPath e {}

  -- find the argument position of the function `f` in `P f`
  let mut .some funArgId ← xs.reverse.findIdxM? fun x => do
    if (← inferType x).isForall then
      return true
    else
      return false
    | throwError "invalid fun_prop declaration, can't find argument of type `α → β`"
  funArgId := xs.size - funArgId - 1

  let decl : FunPropDecl := {
    funPropName := declName
    path := path
    funArgId := funArgId
    dischargeStx? := dischargeStx?
  }

  modifyEnv fun env => funPropDeclsExt.addEntry env decl

  trace[Meta.Tactic.funProp.attr]
    "added new function property `{declName}`\nlook up pattern is `{path}`"


/-- -/
def getFunProp? (e : Expr) : MetaM (Option (FunPropDecl × Expr)) := do
  let ext := funPropDeclsExt.getState (← getEnv)

  let decls ← ext.decls.getMatch e {}

  if decls.size = 0 then
    return none

  if decls.size > 1 then
    throwError "\
fun_prop bug: expression {← ppExpr e} matches multiple function properties
{decls.map (fun d => d.funPropName)}"

  let decl := decls[0]!
  let f := e.getArg! decl.funArgId

  return (decl,f)

/-- -/
def isFunProp (e : Expr) : MetaM Bool := do return (← getFunProp? e).isSome

/-- Returns function property declaration from `e = P f`. -/
def getFunPropDecl? (e : Expr) : MetaM (Option FunPropDecl) := do
  match ← getFunProp? e with
  | .some (decl,_) => return decl
  | .none => return none


/-- Returns function `f` from `e = P f` and `P` is function property. -/
def getFunPropFun? (e : Expr) : MetaM (Option Expr) := do
  match ← getFunProp? e with
  | .some (_,f) => return f
  | .none => return none


open Elab Term in
/-- -/
def tacticToDischarge (tacticCode : TSyntax `tactic) : Expr → MetaM (Option Expr) := fun e =>
  withTraceNode `Meta.Tactic.fun_prop
    (fun r => do pure s!"[{ExceptToEmoji.toEmoji r}] discharging: {← ppExpr e}") do
    let mvar ← mkFreshExprSyntheticOpaqueMVar e `funProp.discharger
    let runTac? : TermElabM (Option Expr) :=
      try
        withoutModifyingStateWithInfoAndMessages do
          instantiateMVarDeclMVars mvar.mvarId!

          let _ ←
            withSynthesize (mayPostpone := false) do
              Tactic.run mvar.mvarId! (Tactic.evalTactic tacticCode *> Tactic.pruneSolvedGoals)

          let result ← instantiateMVars mvar
          if result.hasExprMVar then
            return none
          else
            return some result
      catch _ =>
        return none
    let (result?, _) ← runTac?.run {} {}

    return result?

/-- -/
def FunPropDecl.discharger (funPropDecl : FunPropDecl) (e : Expr) : MetaM (Option Expr) := do
    let .some stx := funPropDecl.dischargeStx?
      | return none
    tacticToDischarge stx e
