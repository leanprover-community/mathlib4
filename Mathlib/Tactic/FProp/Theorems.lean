/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Std.Data.RBMap.Alter

import Mathlib.Tactic.FProp.Decl
import Mathlib.Tactic.FProp.FunctionData
import Mathlib.Tactic.FProp.RefinedDiscrTree

/-!
## `fprop` enviroment extensions storing thorems for `fprop`
-/

namespace Mathlib
open Lean Meta

namespace Meta.FProp


/-- Stores important argument indices of lambda theorems

For example
```
theorem Continuous_const {α β} [TopologicalSpace α] [TopologicalSpace β] (y : β) :
    Continuous fun _ : α => y
```
is represented by
```
  .const 0 4
```
 -/
inductive LambdaTheoremArgs
  | id (X : Nat)
  | const (X y : Nat)
  | proj (x Y : Nat)
  | projDep (x Y : Nat)
  | comp (f g : Nat)
  | pi (f : Nat)
  deriving Inhabited, BEq, Repr, Hashable

/-- There are 5(+1) basic lambda theorems

- id      `Continous fun x => x`
- const   `Continous fun x => y`
- proj    `Continous fun (f : X → Y) => f x`
- projDep `Continous fun (f : (x : X) → Y x => f x)`
- comp    `Continous f → Continous g → Continous fun x => f (g x)`
- pi      `∀ y, Continuous (f · y) → Continous fun x y => f x y` -/
inductive LambdaTheoremType
  | id  | const | proj| projDep | comp  | pi
  deriving Inhabited, BEq, Repr, Hashable

/-- -/
def LambdaTheoremArgs.type (t : LambdaTheoremArgs) : LambdaTheoremType :=
  match t with
  | .id .. => .id
  | .const .. => .const
  | .proj .. => .proj
  | .projDep .. => .projDep
  | .comp .. => .comp
  | .pi .. => .pi

set_option linter.unusedVariables false in
/--  -/
def detectLambdaTheoremArgs (f : Expr) (ctxVars : Array Expr) :
    MetaM (Option LambdaTheoremArgs) := do

  -- eta expand but beta reduce body
  let f ← forallTelescope (← inferType f) fun xs b =>
    mkLambdaFVars xs (mkAppN f xs).headBeta

  match f with
  | .lam xName xType xBody xBi =>
    match xBody with
    | .bvar 0 =>
      -- fun x => x
      let .some argId_X := ctxVars.findIdx? (fun x => x == xType) | return none
      return .some (.id argId_X)
    | .fvar yId =>
      -- fun x => y
      let .some argId_X := ctxVars.findIdx? (fun x => x == xType) | return none
      let .some argId_y := ctxVars.findIdx? (fun x => x == (.fvar yId)) | return none
      return .some (.const argId_X argId_y)
    | .app (.bvar 0) (.fvar xId) =>
      -- fun f => f x
      let fType := xType
       let .some argId_x := ctxVars.findIdx? (fun x => x == (.fvar xId)) | return none
       match fType with
       | .forallE xName' xType' (.fvar yId) xBi' =>
         let .some argId_Y := ctxVars.findIdx? (fun x => x == (.fvar yId)) | return none
         return .some <| .proj argId_x argId_Y
       | .forallE xName' xType' (.app (.fvar yId) (.bvar 0)) xBi' =>
         let .some argId_Y := ctxVars.findIdx? (fun x => x == (.fvar yId)) | return none
         return .some <| .projDep argId_x argId_Y
       | _ => return none
    | .app (.fvar fId) (.app (.fvar gId) (.bvar 0)) =>
      -- fun x => f (g x)
      let .some argId_f := ctxVars.findIdx? (fun x => x == (.fvar fId)) | return none
      let .some argId_g := ctxVars.findIdx? (fun x => x == (.fvar gId)) | return none
      return .some <| .comp argId_f argId_g
    | .lam Name yType (.app (.app (.fvar fId) (.bvar 1)) (.bvar 0)) yBi =>
      -- fun x y => f x y
      let .some argId_f := ctxVars.findIdx? (fun x => x == (.fvar fId)) | return none
      return .some <| .pi argId_f
    | _ => return none
  | _ => return none


structure LambdaTheorem where
  /-- Name of function property -/
  fpropName : Name
  /-- Name of lambda theorem -/
  thmName : Name
  /-- Type and important argument of the theorem. -/
  thmArgs : LambdaTheoremArgs
  deriving Inhabited, BEq

/-- -/
structure LambdaTheorems where
  /-- map: function property name × theorem type → lambda theorem -/
  theorems : HashMap (Name × LambdaTheoremType) LambdaTheorem := {}
  deriving Inhabited


/-- return proof of lambda theorem -/
def LambdaTheorem.getProof (thm : LambdaTheorem) : MetaM Expr := do
  mkConstWithFreshMVarLevels thm.thmName

/-- -/
abbrev LambdaTheoremsExt := SimpleScopedEnvExtension LambdaTheorem LambdaTheorems

/-- Extension storing all lambda theorems. -/
initialize lambdaTheoremsExt : LambdaTheoremsExt ←
  registerSimpleScopedEnvExtension {
    name := by exact decl_name%
    initial := {}
    addEntry := fun d e =>
      {d with theorems := d.theorems.insert (e.fpropName, e.thmArgs.type) e}
  }

/-- -/
def getLambdaTheorem (fpropName : Name) (type : LambdaTheoremType) :
    CoreM (Option LambdaTheorem) := do
  return (lambdaTheoremsExt.getState (← getEnv)).theorems.find? (fpropName,type)


--------------------------------------------------------------------------------

/-- Function theorems are stated in uncurried or compositional form.

uncurried
```
theorem Continuous_add : Continuous (fun x => x.1 + x.2)
```

compositional
```
theorem Continuous_add (hf : Continuous f) (hg : Continuous g) : Continuous (fun x => (f x) + (g x))
```
 -/
inductive TheoremForm where
  | uncurried | comp
  deriving Inhabited, BEq, Repr


/-- theorem about specific function (eiter declared constant or free variable) -/
structure FunctionTheorem where
  /-- function property name -/
  fpropName : Name
  /-- theorem name -/
  thmName   : Name
  /-- function name -/
  funName   : Name
  /-- array of argument indices about which this theorem is about -/
  mainArgs  : Array Nat
  /-- total number of arguments applied to the function  -/
  appliedArgs : Nat
  /-- priority  -/
  priority    : Nat  := eval_prio default
  /-- form of the theorem, see documentation of TheoremForm -/
  form : TheoremForm
  deriving Inhabited, BEq


private local instance : Ord Name := ⟨Name.quickCmp⟩

/-- -/
structure FunctionTheorems where
  /-- map: function name → function property → function theorem -/
  theorems : Std.RBMap Name (Std.RBMap Name (Array FunctionTheorem) compare) compare := {}
  deriving Inhabited


/-- return proof of function theorem -/
def FunctionTheorem.getProof (thm : FunctionTheorem) : MetaM Expr := do
  mkConstWithFreshMVarLevels thm.thmName


/-- -/
abbrev FunctionTheoremsExt := SimpleScopedEnvExtension FunctionTheorem FunctionTheorems

/-- Extension storing all function theorems. -/
initialize functionTheoremsExt : FunctionTheoremsExt ←
  registerSimpleScopedEnvExtension {
    name     := by exact decl_name%
    initial  := {}
    addEntry := fun d e =>
      {d with
        theorems :=
          d.theorems.alter e.funName fun funProperties =>
            let funProperties := funProperties.getD {}
            funProperties.alter e.fpropName fun thms =>
              let thms := thms.getD #[]
              thms.push e}
  }

/-- -/
def getTheoremsForFunction (funName : Name) (fpropName : Name) : CoreM (Array FunctionTheorem) := do
  return (functionTheoremsExt.getState (← getEnv)).theorems.findD funName {} |>.findD fpropName #[]


--------------------------------------------------------------------------------

/-- General theorem about function property
  used for transition and morphism theorems -/
structure GeneralTheorem where
  /-- function property name -/
  fpropName   : Name
  /-- theorem name -/
  thmName     : Name
  /-- discreminatory tree keys used to index this theorem -/
  keys        : List RefinedDiscrTree.DTExpr
  /-- priority -/
  priority    : Nat  := eval_prio default
  deriving Inhabited, BEq

/-- Get proof of a theorem. -/
def GeneralTheorem.getProof (thm : GeneralTheorem) : MetaM Expr := do
  mkConstWithFreshMVarLevels thm.thmName

/-- -/
structure GeneralTheorems where
  theorems     : RefinedDiscrTree GeneralTheorem := {}
  deriving Inhabited

/-- -/
abbrev GeneralTheoremsExt := SimpleScopedEnvExtension GeneralTheorem GeneralTheorems

/-- -/
initialize transitionTheoremsExt : GeneralTheoremsExt ←
  registerSimpleScopedEnvExtension {
    name     := by exact decl_name%
    initial  := {}
    addEntry := fun d e =>
      {d with theorems := e.keys.foldl (RefinedDiscrTree.insertDTExpr · · e) d.theorems}
  }

/-- -/
initialize morTheoremsExt : GeneralTheoremsExt ←
  registerSimpleScopedEnvExtension {
    name     := by exact decl_name%
    initial  := {}
    addEntry := fun d e =>
      {d with theorems := e.keys.foldl (RefinedDiscrTree.insertDTExpr · · e) d.theorems}
  }



--------------------------------------------------------------------------------


/-- There are four types of theorems:
- lam - theorem about basic lambda calculus terms
- function - theorem about a specific function(declared or free variable) in specific arguments
- mor - special theorems talking about bundled morphisms/DFunLike.coe
- transition - theorems infering one function property from another

Examples:
- lam
```
  theorem Continuous_id : Continous fun x => x
  theorem Continuous_comp (hf : Continuous f) (hg : Continuous g) : Continous fun x => f (g x)
```
- function
```
  theorem Continuous_add : Continuous (fun x => x.1 + x.2)
  theorem Continuous_add (hf : Continuous f) (hg : Continuous g) :
      Continuous (fun x => (f x) + (g x))
```
- mor - the head of function body has to be ``DFunLike.code
```
  theorem ContDiff.clm_apply {f : E → F →L[𝕜] G} {g : E → F}
      (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
      ContDiff 𝕜 n fun x => (f x) (g x)
  theorem clm_linear {f : E →L[𝕜] F} : IsLinearMap 𝕜 f
```
- transition - the conclusion has to be in the form `P f` where `f` is a free variable
```
  theorem linear_is_continuous [FiniteDimensional ℝ E] {f : E → F} (hf : IsLinearMap 𝕜 f) :
      Conttinuous f
```
-/
inductive Theorem where
  | lam        (thm : LambdaTheorem)
  | function   (thm : FunctionTheorem)
  | mor        (thm : GeneralTheorem)
  | transition (thm : GeneralTheorem)


/-- -/
def getTheoremFromConst (declName : Name) (prio : Nat := eval_prio default) : MetaM Theorem := do
  let info ← getConstInfo declName
  forallTelescope info.type fun xs b => do

    let .some (decl,f) ← getFProp? b
      | throwError "unrecognized function property `{← ppExpr b}`"
    let fpropName := decl.fpropName

    if let .some thmArgs ← detectLambdaTheoremArgs f xs then
      return .lam {
        fpropName := fpropName
        thmName := declName
        thmArgs := thmArgs
      }

    let fData ← getFunctionData f

    match fData.fn with
    | .const funName _ =>

      let .some (f',_) ← splitMorToComp f
        | throwError s!"fprop bug: failed at detecting theorem type `{← ppExpr b}`"

      let form : TheoremForm := if (← isDefEq f' f) then .uncurried else .comp

      return .function {
-- fpropName funName fData.mainArgs fData.args.size thmForm
        fpropName := fpropName
        thmName := declName
        funName := funName
        mainArgs := fData.mainArgs
        appliedArgs := fData.args.size
        priority := prio
        form := form
      }
    | .fvar .. =>
      let (_,_,b') ← forallMetaTelescope info.type
      let keys := ← RefinedDiscrTree.mkDTExprs b'
      let thm : GeneralTheorem := {
        fpropName := fpropName
        thmName := declName
        keys    := keys
        priority  := prio
      }
      -- todo: maybe do a little bit more caraful detection of morphism and transition theorems
      let lastArg := fData.args[fData.args.size-1]!
      if lastArg.coe.isSome then
        return .mor thm
      else
        return .transition thm
    | _ =>
      throwError "unrecognized theoremType `{← ppExpr b}`"


/-- -/
def addTheorem (declName : Name) (attrKind : AttributeKind := .global)
    (prio : Nat := eval_prio default) : MetaM Unit := do
  match (← getTheoremFromConst declName prio) with
  | .lam thm =>
    trace[Meta.Tactic.fprop.attr] "\
lambda theorem: {thm.thmName}
function property: {thm.fpropName}
type: {repr thm.thmArgs.type}"
    lambdaTheoremsExt.add thm attrKind
  | .function thm =>
    trace[Meta.Tactic.fprop.attr] "\
function theorem: {thm.thmName}
function property: {thm.fpropName}
function name: {thm.funName}
main arguments: {thm.mainArgs}
applied arguments: {thm.appliedArgs}
form: {repr thm.form}"
    functionTheoremsExt.add thm attrKind
  | .mor thm =>
    trace[Meta.Tactic.fprop.attr] "\
morphism theorem: {thm.thmName}
function property: {thm.fpropName}"
    morTheoremsExt.add thm attrKind
  | .transition thm =>
    trace[Meta.Tactic.fprop.attr] "\
transition theorem: {thm.thmName}
function property: {thm.fpropName}"
    transitionTheoremsExt.add thm attrKind
