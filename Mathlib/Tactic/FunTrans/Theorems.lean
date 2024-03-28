/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Std.Data.RBMap.Alter

import Mathlib.Tactic.FunTrans.Decl
import Mathlib.Tactic.FunProp.Theorems

/-!
## `fun_trans` enviroment extensions storing thorems for `fun_trans`
-/

namespace Mathlib
open Lean Meta

namespace Meta.FunTrans

/--  -/
structure LambdaTheorem where
  /-- Name of function transformation -/
  funTransName : Name
  /-- Name of lambda theorem -/
  thmName : Name
  /-- total number of arguments applied to the function transformation  -/
  transAppliedArgs : Nat
  /-- Type and important argument of the theorem. -/
  thmArgs : FunProp.LambdaTheoremArgs
  deriving Inhabited, BEq

/-- -/
structure LambdaTheorems where
  /-- map: function transfromation name × theorem type → lambda theorem -/
  theorems : HashMap (Name × FunProp.LambdaTheoremType) (Array LambdaTheorem) := {}
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
      {d with theorems :=
         let es := d.theorems.findD (e.funTransName, e.thmArgs.type) #[]
         d.theorems.insert (e.funTransName, e.thmArgs.type) (es.push e)}
  }

/-- Return lambda theorems of type `type` for function transformation `funTransName`

Theorems are filtered and sorted based on the optional argument `nargs`. It specifies the number of
arguments of the expression we want to transform.

For example when transforming
```
deriv (fun x => x * sin x)
```
we do not want to use composition theorem stating `deriv (fun x' => f (g x')) x` because our
expression does not have the concrete point where we differentiate.

On the other hand when transforming
```
deriv (fun x' => 1/(1-x')) x
```
we prefer the version `deriv (fun x' => f (g x')) x` over `deriv (fun x' => f (g x'))` as the former
uses `DifferntiableAt` insed of `Differentiable` as preconditions. -/
def getLambdaTheorems (funTransName : Name) (type : FunProp.LambdaTheoremType) (nargs : Option Nat):
    CoreM (Option (Array LambdaTheorem)) := do
  let .some thms := (lambdaTheoremsExt.getState (← getEnv)).theorems.find? (funTransName,type)
    | return none

  match nargs with
  | none => return thms
  | some n =>
    let thms := thms
        |>.filter (fun thm => thm.transAppliedArgs ≤ n)
        |>.qsort (fun t t' => t'.transAppliedArgs < t.transAppliedArgs)
    return thms


----------------------------------------------------------------------------------------------------


/-- theorem about specific function (either declared constant or free variable) -/
structure FunctionTheorem where
  /-- function transformation name -/
  funTransName : Name
  /-- total number of arguments applied to the function transformation  -/
  transAppliedArgs : Nat
  /-- theorem name -/
  thmOrigin   : FunProp.Origin
  /-- function name -/
  funOrigin   : FunProp.Origin
  /-- array of argument indices about which this theorem is about -/
  mainArgs  : Array Nat
  /-- total number of arguments applied to the function  -/
  appliedArgs : Nat
  /-- priority  -/
  priority    : Nat  := eval_prio default
  /-- form of the theorem, see documentation of TheoremForm -/
  form : FunProp.TheoremForm
  deriving Inhabited, BEq


private local instance : Ord Name := ⟨Name.quickCmp⟩

/-- -/
structure FunctionTheorems where
  /-- map: function name → function transformation → function theorem -/
  theorems : Std.RBMap Name (Std.RBMap Name (Array FunctionTheorem) compare) compare := {}
  deriving Inhabited


/-- return proof of function theorem -/
def FunctionTheorem.getProof (thm : FunctionTheorem) : MetaM Expr := do
  match thm.thmOrigin with
  | .decl name => mkConstWithFreshMVarLevels name
  | .fvar id => pure (.fvar id)


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
          d.theorems.alter e.funOrigin.name fun funTrans =>
            let funTrans := funTrans.getD {}
            funTrans.alter e.funTransName fun thms =>
              let thms := thms.getD #[]
              thms.push e}
  }


/-- -/
def getTheoremsForFunction (funName : Name) (funTransName : Name) (nargs : Option Nat) (mainArgs : Option (Array ℕ)) :
    CoreM (Array FunctionTheorem) := do

  let thms := (functionTheoremsExt.getState (← getEnv)).theorems.findD funName {}
              |>.findD funTransName #[]

  let thms := thms
      |>.filter (fun thm =>
         (nargs.map (fun n => (thm.transAppliedArgs ≤ n : Bool))).getD true
         &&
         (mainArgs.map (fun args => FunProp.isOrderedSubsetOf args thm.mainArgs)).getD true)
      |>.qsort (fun t t' => t'.transAppliedArgs < t.transAppliedArgs)

  return thms



----------------------------------------------------------------------------------------------------

/-- General theorem about function transformation used for morphism theorems -/
structure GeneralTheorem where
  /-- function transformation name -/
  funTransName   : Name
  /-- theorem name -/
  thmName     : Name
  /-- discriminatory tree keys used to index this theorem -/
  keys        : List FunProp.RefinedDiscrTree.DTExpr
  /-- priority -/
  priority    : Nat  := eval_prio default
  deriving Inhabited, BEq

/-- Get proof of a theorem. -/
def GeneralTheorem.getProof (thm : GeneralTheorem) : MetaM Expr := do
  mkConstWithFreshMVarLevels thm.thmName

/-- -/
structure GeneralTheorems where
  /-- -/
  theorems     : FunProp.RefinedDiscrTree GeneralTheorem := {}
  deriving Inhabited

/-- -/
abbrev GeneralTheoremsExt := SimpleScopedEnvExtension GeneralTheorem GeneralTheorems

/-- -/
initialize morTheoremsExt : GeneralTheoremsExt ←
  registerSimpleScopedEnvExtension {
    name     := by exact decl_name%
    initial  := {}
    addEntry := fun d e =>
      {d with theorems := e.keys.foldl (FunProp.RefinedDiscrTree.insertDTExpr · · e) d.theorems}
  }


/-- -/
initialize fvarTheoremsExt : GeneralTheoremsExt ←
  registerSimpleScopedEnvExtension {
    name     := by exact decl_name%
    initial  := {}
    addEntry := fun d e =>
      {d with theorems := e.keys.foldl (FunProp.RefinedDiscrTree.insertDTExpr · · e) d.theorems}
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
  | fvar       (thm : GeneralTheorem)


/-- -/
def getTheoremFromConst (declName : Name) (prio : Nat := eval_prio default) : MetaM Theorem := do
  let info ← getConstInfo declName
  forallTelescope info.type fun xs b => do

    unless b.isEq do throwError "equality expected"

    let lhs := b.getArg! 1

    let .some (decl,f) ← getFunTrans? lhs
      | throwError "unrecognized function transformation `{← ppExpr lhs}`"
    let funTransName := decl.funTransName

    let fData? ← FunProp.getFunctionData? f FunProp.defaultUnfoldPred {zeta:=false}

    if let .some thmArgs ← FunProp.detectLambdaTheoremArgs (← fData?.get) xs then
      return .lam {
        funTransName := funTransName
        transAppliedArgs := lhs.getAppNumArgs
        thmName := declName
        thmArgs := thmArgs
      }

    let .data fData := fData?
      | throwError s!"function in invalid form {← ppExpr f}"

    match fData.fn with
    | .const funName _ =>

      let dec ← fData.nontrivialDecomposition
      let form : FunProp.TheoremForm :=
        if dec.isSome || funName == ``Prod.mk then .comp else .uncurried

      return .function {
-- funTransName funName fData.mainArgs fData.args.size thmForm
        funTransName := funTransName
        transAppliedArgs := lhs.getAppNumArgs'
        thmOrigin := .decl declName
        funOrigin := .decl funName
        mainArgs := fData.mainArgs
        appliedArgs := fData.args.size
        priority := prio
        form := form
      }
    | .fvar .. =>
      let (_,_,b') ← forallMetaTelescope info.type
      let keys := ← FunProp.RefinedDiscrTree.mkDTExprs (b'.getArg! 1) {} false
      let thm : GeneralTheorem := {
        funTransName := funTransName
        thmName := declName
        keys    := keys
        priority  := prio
      }

      let n := fData.args.size
      if n = 1 &&
         fData.args[0]!.coe.isNone &&
         fData.args[0]!.expr == fData.mainVar then
        return .fvar thm
      else if (n > 0) && fData.args[n-1]!.coe.isSome then
        return .mor thm
      else
        throwError "unrecognized theoremType `{← ppExpr b}`"
    | _ =>
      throwError "unrecognized theoremType `{← ppExpr b}`"


/-- -/
def addTheorem (declName : Name) (attrKind : AttributeKind := .global)
    (prio : Nat := eval_prio default) : MetaM Unit := do
  match (← getTheoremFromConst declName prio) with
  | .lam thm =>
    trace[Meta.Tactic.fun_trans.attr] "\
lambda theorem: {thm.thmName}
function transfromations: {thm.funTransName}
type: {repr thm.thmArgs.type}"
    lambdaTheoremsExt.add thm attrKind
  | .function thm =>
    trace[Meta.Tactic.fun_trans.attr] "\
function theorem: {thm.thmOrigin.name}
function transformation: {thm.funTransName}
function transformation applied args: {thm.transAppliedArgs}
function name: {thm.funOrigin.name}
main arguments: {thm.mainArgs}
applied arguments: {thm.appliedArgs}
form: {repr thm.form}"
    functionTheoremsExt.add thm attrKind
  | .mor thm =>
    trace[Meta.Tactic.fun_trans.attr] "\
morphism theorem: {thm.thmName}
function transformation: {thm.funTransName}
discr tree key: {thm.keys}"
    morTheoremsExt.add thm attrKind
  | .fvar thm =>
    trace[Meta.Tactic.fun_trans.attr] "\
fvar theorem: {thm.thmName}
function transformation: {thm.funTransName}
discr tree key: {thm.keys}"
    fvarTheoremsExt.add thm attrKind
