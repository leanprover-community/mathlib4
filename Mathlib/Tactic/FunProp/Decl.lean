/-
Copyright (c) 2024 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
import Mathlib.Init

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
  /-- path for discrimination tree -/
  path : Array DiscrTree.Key
  /-- argument index of a function this function property talks about.
  For example, this would be 4 for `@Continuous α β _ _ f` -/
  funArgId : Nat
  deriving Inhabited, BEq

/-- Discrimination tree for function properties. -/
structure FunPropDecls where
  /-- Discrimination tree for function properties. -/
  decls : DiscrTree FunPropDecl := {}
  deriving Inhabited

set_option linter.style.docString false in
/-- -/
abbrev FunPropDeclsExt := SimpleScopedEnvExtension FunPropDecl FunPropDecls

/-- Extension storing function properties tracked and used by the `fun_prop` attribute and tactic,
including, for example, `Continuous`, `Measurable`, `Differentiable`, etc. -/
initialize funPropDeclsExt : FunPropDeclsExt ←
  registerSimpleScopedEnvExtension {
    name := by exact decl_name%
    initial := {}
    addEntry := fun d e =>
      {d with decls := d.decls.insertCore e.path e}
  }

/-- Register new function property. -/
def addFunPropDecl (declName : Name) : MetaM Unit := do

  let info ← getConstInfo declName

  let (xs, bi, b) ← forallMetaTelescope info.type

  if ¬b.isProp then
    throwError "invalid fun_prop declaration, has to be `Prop` valued function"

  let lvls := info.levelParams.map (fun l => Level.param l)
  let e := mkAppN (.const declName lvls) xs
  let path ← DiscrTree.mkPath e

  -- find the argument position of the function `f` in `P f`
  let mut .some funArgId ← (xs.zip bi).findIdxM? fun (x,bi) => do
    if (← inferType x).isForall && bi.isExplicit then
      return true
    else
      return false
    | throwError "invalid fun_prop declaration, can't find argument of type `α → β`"

  let decl : FunPropDecl := {
    funPropName := declName
    path := path
    funArgId := funArgId
  }

  modifyEnv fun env => funPropDeclsExt.addEntry env decl

  trace[Meta.Tactic.funProp.attr]
    "added new function property `{declName}`\nlook up pattern is `{path}`"


/-- Is `e` a function property statement? If yes return function property declaration and
the function it talks about. -/
def getFunProp? (e : Expr) : MetaM (Option (FunPropDecl × Expr)) := do
  let ext := funPropDeclsExt.getState (← getEnv)

  let decls ← ext.decls.getMatch e (← read)

  if h : decls.size = 0 then
    return none
  else
    if decls.size > 1 then
      throwError "fun_prop bug: expression {← ppExpr e} matches multiple function properties\n\
        {decls.map (fun d => d.funPropName)}"

    let decl := decls[0]
    unless decl.funArgId < e.getAppNumArgs do return none
    let f := e.getArg! decl.funArgId

    return (decl,f)

/-- Is `e` a function property statement? -/
def isFunProp (e : Expr) : MetaM Bool := do return (← getFunProp? e).isSome

/-- Is `e` a `fun_prop` goal? For example `∀ y z, Continuous fun x => f x y z` -/
def isFunPropGoal (e : Expr) : MetaM Bool := do
  forallTelescope e fun _ b =>
  return (← getFunProp? b).isSome

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
/-- Turn tactic syntax into a discharger function. -/
def tacticToDischarge (tacticCode : TSyntax `tactic) : Expr → MetaM (Option Expr) := fun e =>
  withTraceNode `Meta.Tactic.fun_prop
    (fun r => do pure s!"[{ExceptToEmoji.toEmoji r}] discharging: {← ppExpr e}") do
    let mvar ← mkFreshExprSyntheticOpaqueMVar e `funProp.discharger
    let runTac? : TermElabM (Option Expr) :=
      try
        withoutModifyingStateWithInfoAndMessages do
          instantiateMVarDeclMVars mvar.mvarId!

          let _ ←
            withSynthesize (postpone := .no) do
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

end Meta.FunProp

end Mathlib
