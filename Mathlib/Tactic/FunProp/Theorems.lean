/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Mathlib.Tactic.FunProp.Decl
import Mathlib.Tactic.FunProp.Types
import Mathlib.Tactic.FunProp.FunctionData
import Mathlib.Tactic.FunProp.RefinedDiscrTree

/-!
## `fun_prop` environment extensions storing theorems for `fun_prop`
-/

namespace Mathlib
open Lean Meta

namespace Meta.FunProp

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
  | letE (f g : Nat)
  | pi (f : Nat)
  deriving Inhabited, BEq, Repr, Hashable

/-- There are 5(+1) basic lambda theorems

- id      `Continuous fun x => x`
- const   `Continuous fun x => y`
- proj    `Continuous fun (f : X → Y) => f x`
- projDep `Continuous fun (f : (x : X) → Y x => f x)`
- comp    `Continuous f → Continuous g → Continuous fun x => f (g x)`
- letE    `Continuous f → Continuous g → Continuous fun x => let y := g x; f x y`
- pi      `∀ y, Continuous (f · y) → Continuous fun x y => f x y` -/
inductive LambdaTheoremType
  | id  | const | proj| projDep | comp | letE  | pi
  deriving Inhabited, BEq, Repr, Hashable

/-- -/
def LambdaTheoremArgs.type (t : LambdaTheoremArgs) : LambdaTheoremType :=
  match t with
  | .id .. => .id
  | .const .. => .const
  | .proj .. => .proj
  | .projDep .. => .projDep
  | .comp .. => .comp
  | .letE .. => .letE
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
    | .letE yName yType (.app (.fvar gId) (.bvar 0))
                        (.app (.app (.fvar fId) (.bvar 1)) (.bvar 0)) dep =>
      let .some argId_f := ctxVars.findIdx? (fun x => x == (.fvar fId)) | return none
      let .some argId_g := ctxVars.findIdx? (fun x => x == (.fvar gId)) | return none
      return .some <| .letE argId_f argId_g
    | .lam Name yType (.app (.app (.fvar fId) (.bvar 1)) (.bvar 0)) yBi =>
      -- fun x y => f x y
      let .some argId_f := ctxVars.findIdx? (fun x => x == (.fvar fId)) | return none
      return .some <| .pi argId_f
    | _ => return none
  | _ => return none


/--  -/
structure LambdaTheorem where
  /-- Name of function property -/
  funPropName : Name
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
      {d with theorems := d.theorems.insert (e.funPropName, e.thmArgs.type) e}
  }

/-- -/
def getLambdaTheorem (funPropName : Name) (type : LambdaTheoremType) :
    CoreM (Option LambdaTheorem) := do
  return (lambdaTheoremsExt.getState (← getEnv)).theorems.find? (funPropName,type)


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

/-- theorem about specific function (either declared constant or free variable) -/
structure FunctionTheorem where
  /-- function property name -/
  funPropName : Name
  /-- theorem name -/
  thmOrigin   : Origin
  /-- function name -/
  funOrigin   : Origin
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
  theorems :
    Batteries.RBMap Name (Batteries.RBMap Name (Array FunctionTheorem) compare) compare := {}
  deriving Inhabited


/-- return proof of function theorem -/
def FunctionTheorem.getProof (thm : FunctionTheorem) : MetaM Expr := do
  match thm.thmOrigin with
  | .decl name => mkConstWithFreshMVarLevels name
  | .fvar id => return .fvar id


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
          d.theorems.alter e.funOrigin.name fun funProperties =>
            let funProperties := funProperties.getD {}
            funProperties.alter e.funPropName fun thms =>
              let thms := thms.getD #[]
              thms.push e}
  }

/-- -/
def getTheoremsForFunction (funName : Name) (funPropName : Name) :
    CoreM (Array FunctionTheorem) := do
  return (functionTheoremsExt.getState (← getEnv)).theorems.findD funName {}
    |>.findD funPropName #[]


--------------------------------------------------------------------------------

/-- General theorem about function property
  used for transition and morphism theorems -/
structure GeneralTheorem where
  /-- function property name -/
  funPropName   : Name
  /-- theorem name -/
  thmName     : Name
  /-- discrimination tree keys used to index this theorem -/
  keys        : List RefinedDiscrTree.DTExpr
  /-- priority -/
  priority    : Nat  := eval_prio default
  deriving Inhabited, BEq

/-- Get proof of a theorem. -/
def GeneralTheorem.getProof (thm : GeneralTheorem) : MetaM Expr := do
  mkConstWithFreshMVarLevels thm.thmName

/-- -/
structure GeneralTheorems where
  /-- -/
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
- transition - theorems inferring one function property from another

Examples:
- lam
```
  theorem Continuous_id : Continuous fun x => x
  theorem Continuous_comp (hf : Continuous f) (hg : Continuous g) : Continuous fun x => f (g x)
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
      Continuous f
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

    let .some (decl,f) ← getFunProp? b
      | throwError "unrecognized function property `{← ppExpr b}`"
    let funPropName := decl.funPropName

    let fData? ← getFunctionData? f defaultUnfoldPred {zeta:=false}

    if let .some thmArgs ← detectLambdaTheoremArgs (← fData?.get) xs then
      return .lam {
        funPropName := funPropName
        thmName := declName
        thmArgs := thmArgs
      }

    let .data fData := fData?
      | throwError s!"function in invalid form {← ppExpr f}"

    match fData.fn with
    | .const funName _ =>

      -- todo: more robust detection of compositional and uncurried form!!!
      -- I think this detects `Continuous fun x => x + c` as compositional ...
      let dec ← fData.nontrivialDecomposition
      let form : TheoremForm := if dec.isSome || funName == ``Prod.mk then .comp else .uncurried

      return .function {
-- funPropName funName fData.mainArgs fData.args.size thmForm
        funPropName := funPropName
        thmOrigin := .decl declName
        funOrigin := .decl funName
        mainArgs := fData.mainArgs
        appliedArgs := fData.args.size
        priority := prio
        form := form
      }
    | .fvar .. =>
      let (_,_,b') ← forallMetaTelescope info.type
      let keys := ← RefinedDiscrTree.mkDTExprs b' {} false
      let thm : GeneralTheorem := {
        funPropName := funPropName
        thmName := declName
        keys    := keys
        priority  := prio
      }
      -- todo: maybe do a little bit more careful detection of morphism and transition theorems
      match (← fData.isMorApplication) with
      | .exact => return .mor thm
      | .underApplied | .overApplied =>
        throwError "fun_prop theorem about morphism coercion has to be in fully applied form"
      | .none =>
        if fData.fn.isFVar && (fData.args.size == 1) &&
           (fData.args[0]!.expr == fData.mainVar) then
          return .transition thm

        throwError "Not a valid `fun_prop` theorem!"
    | _ =>
      throwError "unrecognized theoremType `{← ppExpr b}`"


/-- -/
def addTheorem (declName : Name) (attrKind : AttributeKind := .global)
    (prio : Nat := eval_prio default) : MetaM Unit := do
  match (← getTheoremFromConst declName prio) with
  | .lam thm =>
    trace[Meta.Tactic.fun_prop.attr] "\
lambda theorem: {thm.thmName}
function property: {thm.funPropName}
type: {repr thm.thmArgs.type}"
    lambdaTheoremsExt.add thm attrKind
  | .function thm =>
    trace[Meta.Tactic.fun_prop.attr] "\
function theorem: {thm.thmOrigin.name}
function property: {thm.funPropName}
function name: {thm.funOrigin.name}
main arguments: {thm.mainArgs}
applied arguments: {thm.appliedArgs}
form: {repr thm.form}"
    functionTheoremsExt.add thm attrKind
  | .mor thm =>
    trace[Meta.Tactic.fun_prop.attr] "\
morphism theorem: {thm.thmName}
function property: {thm.funPropName}"
    morTheoremsExt.add thm attrKind
  | .transition thm =>
    trace[Meta.Tactic.fun_prop.attr] "\
transition theorem: {thm.thmName}
function property: {thm.funPropName}"
    transitionTheoremsExt.add thm attrKind
