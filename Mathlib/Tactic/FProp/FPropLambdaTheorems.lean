/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Mathlib.Tactic.FProp.FPropDecl

namespace Mathlib
open Lean Meta

namespace Meta.FProp

inductive LambdaTheoremArgs 
  | id (X : Nat) 
  | const (X y : Nat) 
  | proj (x Y : Nat) 
  | projDep (x Y : Nat) 
  | comp (f g : Nat) 
  | letE (f g : Nat) 
  | pi (f : Nat)
  deriving Inhabited, BEq, Repr, Hashable

inductive LambdaTheoremType 
  | id  | const | proj| projDep | comp  | letE  | pi
  deriving Inhabited, BEq, Repr, Hashable

def LambdaTheoremArgs.type (t : LambdaTheoremArgs) : LambdaTheoremType :=
  match t with
  | .id .. => .id
  | .const .. => .const
  | .proj .. => .proj
  | .projDep .. => .projDep
  | .comp .. => .comp
  | .letE .. => .letE
  | .pi .. => .pi


/- Custom rule for proving function property of `fun x : X => x`, #[X] -/
/- Custom rule for proving function property of `fun x : X => y`, #[X,y] -/
/- Custom rule for proving function property of `fun f : X → Y => f x`, #[x,Y] -/
/- Custom rule for proving function property of `fun f : (x' : X) → Y x' => f x`, #[x,Y] -/
/- Custom rule for proving function property of `fun x => f (g x)` , #[f,g] -/
/- Custom rule for proving function property of `fun x => let y := g x; f x y`, #[f,g] -/
/- Custom rule for proving function property of `fun x y => f x y`, #[f]. This should reduce the goal to `∀ y, P (fun x => f x y)`.-/
-- TODO: explain what is going on here
structure LambdaTheorem where
  fpropName : Name
  thrmName : Name
  levelParams : Array Name
  proof : Expr
  thrmArgs : LambdaTheoremArgs
  deriving Inhabited, BEq

/-- Returns `proof` with fresh universe metavariables -/
def LambdaTheorem.getProof (fpropThm : LambdaTheorem) : MetaM Expr := do
  if fpropThm.proof.isConst && fpropThm.levelParams.isEmpty then
    let info ← getConstInfo fpropThm.proof.constName!
    if info.levelParams.isEmpty then
      return fpropThm.proof
    else
      return fpropThm.proof.updateConst! (← info.levelParams.mapM (fun _ => mkFreshLevelMVar))
  else
    let us ← fpropThm.levelParams.mapM fun _ => mkFreshLevelMVar
    return fpropThm.proof.instantiateLevelParamsArray fpropThm.levelParams us


structure LambdaTheorems where
  theorems : HashMap (Name × LambdaTheoremType) LambdaTheorem := {}
  deriving Inhabited

abbrev FPropLambdaTheoremsExt := SimpleScopedEnvExtension LambdaTheorem LambdaTheorems

initialize fpropLambdaTheoremsExt : FPropLambdaTheoremsExt ←
  registerSimpleScopedEnvExtension {
    name := by exact decl_name%
    initial := {}
    addEntry := fun d e =>
      {d with theorems := d.theorems.insert (e.fpropName, e.thrmArgs.type) e}
  }

-----------



set_option linter.unusedVariables false in
open Qq in
def detectLambdaTheoremArgs (f : Expr) (xs : Array Expr) : Option LambdaTheoremArgs := do
  
  match f with
  | .lam xName xType xBody xBi => 
    match xBody with 
    | .bvar 0 => 
      -- fun x => x
      let .some argId_X := xs.findIdx? (fun x => x == xType) | none
      return .id argId_X
    | .fvar yId => 
      -- fun x => y
      let .some argId_X := xs.findIdx? (fun x => x == xType) | none
      let .some argId_y := xs.findIdx? (fun x => x == (.fvar yId)) | none
      return .const argId_X argId_y
    | .app (.bvar 0) (.fvar xId) =>
      -- fun f => f x
      let fType := xType
       let .some argId_x := xs.findIdx? (fun x => x == (.fvar xId)) | none
       match fType with
       | .forallE xName' xType' (.fvar yId) xBi' =>
         let .some argId_Y := xs.findIdx? (fun x => x == (.fvar yId)) | none
         return .proj argId_x argId_Y
       | .forallE xName' xType' (.app (.fvar yId) (.bvar 0)) xBi' =>
         let .some argId_Y := xs.findIdx? (fun x => x == (.fvar yId)) | none
         return .projDep argId_x argId_Y
       | _ => none
    | .app (.fvar fId) (.app (.fvar gId) (.bvar 0)) => 
      -- fun x => f (g x)
      let .some argId_f := xs.findIdx? (fun x => x == (.fvar fId)) | none
      let .some argId_g := xs.findIdx? (fun x => x == (.fvar gId)) | none
      return .comp argId_f argId_g
    | .letE yName yType (.app (.fvar gId) (.bvar 0)) (.app (.app (.fvar fId) (.bvar 1)) (.bvar 0)) _ =>  
      -- fun x => let y := g x; f x y
      let .some argId_f := xs.findIdx? (fun x => x == (.fvar fId)) | none
      let .some argId_g := xs.findIdx? (fun x => x == (.fvar gId)) | none
      return .letE argId_f argId_g
    | .lam Name yType (.app (.app (.fvar fId) (.bvar 1)) (.bvar 0)) yBi =>
      -- fun x y => f x y
      let .some argId_f := xs.findIdx? (fun x => x == (.fvar fId)) | none
      return .pi argId_f
    | _ => none
  | _ => none


def addLambdaTheorem (declName : Name) : MetaM Unit := do

  let info ← getConstInfo declName

  forallTelescope info.type fun xs b => do

    let .some (decl,f) ← getFProp? b
      | throwError "unrecognized function property, {← ppExpr b}"

    let .some thrmArgs := detectLambdaTheoremArgs f xs
      | throwError "unrecognized lambda rule, {← ppExpr f}"

    let thrm : LambdaTheorem := {
      fpropName := decl.fpropName
      thrmName := declName
      levelParams := info.levelParams.toArray
      proof := (.const declName (info.levelParams.map fun l => .param l))
      thrmArgs := thrmArgs
    }

    modifyEnv fun env => fpropLambdaTheoremsExt.addEntry env thrm

    trace[Meta.Tactic.fprop.attr] "added lambda theorem `{declName}` of function property `{decl.fpropName}`, theorem type `{repr thrmArgs.type}`"


def getLambdaTheorem (fpropName : Name) (type : LambdaTheoremType) : CoreM (Option LambdaTheorem) := do
  return (fpropLambdaTheoremsExt.getState (← getEnv)).theorems.find? (fpropName,type)
