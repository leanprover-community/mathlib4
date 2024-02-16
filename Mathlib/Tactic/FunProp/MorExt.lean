/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Std.Data.RBMap.Alter

import Mathlib.Tactic.FunProp.ToStd

/-!
## `funProp` environment extension that stores all registered coercions from a morphism to a function
-/


namespace Mathlib
open Lean Meta

namespace Meta.FunProp


private local instance : Ord Name := ⟨Name.quickCmp⟩

/-- -/
initialize morCoeDeclsExt : SimpleScopedEnvExtension Name (Std.RBSet Name compare) ←
  registerSimpleScopedEnvExtension {
    name := by exact decl_name%
    initial := {}
    addEntry := fun d n => d.insert n
  }


/-- -/
def addMorCoeDecl (declName : Name) : MetaM Unit := do

  let info ← getConstInfo declName
  let type := info.type

  forallTelescope type fun xs b => do

  let n := xs.size

  -- coercion needs at least two arguments
  if n < 2 then throwError "invalid morphism coercion, expecting function of at least two arguments"


  let x := xs[n-1]!
  let f := xs[n-2]!
  if ¬(← x.fvarId!.getBinderInfo).isExplicit ||
     ¬(← f.fvarId!.getBinderInfo).isExplicit then
    throwError "invalid morphism coercion, last two argumets are expected to be explicit"

  modifyEnv fun env => morCoeDeclsExt.addEntry env declName

  trace[Meta.Tactic.fun_prop.attr]
    "registered new morphism coercion `{declName}`
     morphism: {← ppExpr f} : {← ppExpr (← inferType f)}
     argument: {← ppExpr x} : {← ppExpr (← inferType x)}
     return value: {← ppExpr b}"


/-- Initialization of `funProp` attribute -/
initialize morCoeAttr : Unit ←
  registerBuiltinAttribute {
    name  := `fun_prop_coe
    descr := "registers morphism coercion for `fun_prop` and `fun_trans` tactics"
    applicationTime := AttributeApplicationTime.afterCompilation
    add   := fun declName _stx _attrKind =>
       discard <| MetaM.run do
       addMorCoeDecl declName
    erase := fun _declName =>
      throwError "can't remove `fun_prop_coe` attribute (not implemented yet)"
  }


namespace Mor

def isMorCoeName (name : Name) : CoreM Bool := do
  return morCoeDeclsExt.getState (← getEnv) |>.contains name

def isMorCoe (e : Expr) : CoreM Bool := do
  let .some (name,_) := e.getAppFn.const? | return false
  isMorCoeName name

structure App where
  coe : Expr
  fn  : Expr
  arg : Expr


def isMorApp? (e : Expr) : CoreM (Option App) := do

  let .app (.app coe f) x := e | return none
  if ← isMorCoe coe then
    return .some { coe := coe, fn := f, arg := x }
  else
    return none

partial def whnfPred (e : Expr) (pred : Expr → MetaM Bool) (cfg : WhnfCoreConfig := {}) :
    MetaM Expr := do
  whnfEasyCases e fun e => do
    let e ← whnfCore e cfg

    if let .some ⟨coe,f,x⟩ ← isMorApp? e then
      let f ← whnfPred f pred cfg
      if cfg.zeta then
        return (coe.app f).app x
      else
        return ← letTelescope f fun xs f' =>
          mkLambdaFVars xs ((coe.app f').app x)

    if (← pred e) then
        match (← unfoldDefinition? e) with
        | some e => whnfPred e pred cfg
        | none   => return e
    else
      return e

def whnf (e : Expr)  (cfg : WhnfCoreConfig := {}) : MetaM Expr :=
  whnfPred e (fun _ => return false) cfg


/-- Argument of morphism application that stores corresponding coercion if necessary -/
structure Arg where
  /-- argument of type `α` -/
  expr : Expr
  /-- coercion `F → α → β` -/
  coe : Option Expr := none
  deriving Inhabited

/-- Morphism application -/
def app (f : Expr) (arg : Arg) : Expr :=
  match arg.coe with
  | .none => f.app arg.expr
  | .some coe => (coe.app f).app arg.expr


/-- Given `e = f a₁ a₂ ... aₙ`, returns `k f #[a₁, ..., aₙ]` where `f` can be bundled morphism. -/
partial def withApp {α} (e : Expr) (k : Expr → Array Arg → MetaM α) : MetaM α :=
  go e #[]
where
  /-- -/
  go : Expr → Array Arg →  MetaM α
    | .mdata _ b, as => go b as
    | .app (.app c f) x, as => do
      if ← isMorCoe c then
        go f (as.push { coe := c, expr := x})
      else
        go (.app c f) (as.push { expr := x})
    | .app f a, as =>
      go f (as.push { expr := a })
    | f        , as => k f as.reverse


/--
If the given expression is a sequence of morphism applications `f a₁ .. aₙ`, return `f`.
Otherwise return the input expression.
-/
def getAppFn (e : Expr) : MetaM Expr :=
  match e with
  | .mdata _ b => getAppFn b
  | .app (.app c f) _ => do
    if ← isMorCoe c then
      getAppFn f
    else
      getAppFn (.app c f)
  | .app f _ =>
    getAppFn f
  | e => return e

/-- Given `f a₁ a₂ ... aₙ`, returns `#[a₁, ..., aₙ]` where `f` can be bundled morphism. -/
def getAppArgs (e : Expr) : MetaM (Array Arg) := withApp e fun _ xs => return xs

/-- `mkAppN f #[a₀, ..., aₙ]` ==> `f a₀ a₁ .. aₙ` where `f` can be bundled morphism. -/
def mkAppN (f : Expr) (xs : Array Arg) : Expr :=
  xs.foldl (init := f) (fun f x =>
    match x with
    | ⟨x, .none⟩ => (f.app x)
    | ⟨x, .some coe⟩ => (coe.app f).app x)
