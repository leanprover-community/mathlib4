/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Std.Data.RBMap.Alter
import Mathlib.Data.FunLike.Basic
import Mathlib.Tactic.FProp.RefinedDiscrTree
import Mathlib.Tactic.FProp.FPropDecl
import Mathlib.Tactic.FProp.ArraySet
import Mathlib.Tactic.FProp.Meta
import Mathlib.Tactic.FProp.FPropTypes
import Mathlib.Tactic.FProp.FPropTheorems

/-!
## `fprop` 

this file defines enviroment extension for `fprop`
-/


namespace Mathlib
open Lean Meta

namespace Meta.FProp

/-- Type of `fprop` theorem

**simple**
Stating function property of declared function in simpl style i.e. the theorem talks about uncurried form of the function
```
theorem continuous_fst : Continuous fun x : α×β => x.1 := ...
```

**comp**
Stating function property of declared function in composition style i.e. each argument is parametrized by a function)
```
theorem continuous_fst' (f : α → β×γ) (hf : Continuous f) : Continuous fun x => (f x).1 := ...
```

**mor**
Stating function property of bundled morphism.
```
theorem continuous_clm (f : E =>L[K] F) : Continuous f := ...
```

**transition**
Stating that certain function property implies different function property.
```
theorem continuous_clm' (f : E → F) (hf : IsContinuousLinearMap K f) : Continuous f := ...
```
  -/
inductive FPropTheorem2Type where
  | simple (fpropName : Name) (functionName : Name) (mainArgs : ArraySet Nat) (appliedArgs : Nat)
  | comp   (fpropName : Name) (functionName : Name) (mainArgs : ArraySet Nat) (appliedArgs : Nat)
  | mor (fpropName : Name) -- (morphismName : Name)
  | transition (outFPropName : Name) -- (inFPropNames : Array Name)



/-- Detect type of fprop theorem. Throws if not a valid fprop theorem -/
def getFPropTheorem2Type (e : Expr) : MetaM FPropTheorem2Type := 
  forallTelescope e fun xs b => do
    let .some (fpropDecl,f) ← getFProp? b | throwError "not a fprop theorem"
    let fpropName := fpropDecl.fpropName
    let f ← fpropNormalizeFun f
    lambdaTelescope f fun xs fb => do
      if xs.size ≠ 1 then
        throwError "FProp theorem in invalid form, expected function in one argument but got `{← ppExpr f}`"
      let xId := xs[0]!.fvarId!
      let fn := Mor.getAppFn fb
      let args := Mor.getAppArgs fb
      let mainArgs := args
        |>.mapIdx (fun i ⟨arg,_⟩ => if arg.containsFVar xId then some i.1 else none)
        |>.filterMap id
        |>.toArraySet
      let appliedArgs := args.size
      match fn with
      | .const functionName _ => do
        let isSimple ← do
          match ← splitMorToComp f with
          | none => pure false
          | .some (f', _) => isDefEq f' f
        if isSimple then 
          return .simple fpropName functionName mainArgs appliedArgs
        else
          return .comp fpropName functionName mainArgs appliedArgs
      | .fvar .. => 
        -- todo: do more careful check
        if fb.isAppOfArity ``DFunLike.coe 6 then
          return .mor fpropName 
        else
          return .transition fpropName
      | _ => 
        throwError "FProp theorem in invalid form {← ppExpr fn}"
    

/-- -/
structure FPropTheorem2 where
  fpropName   : Name
  mainArgs    : ArraySet Nat
  appliedArgs : Nat
  functionName : Name
  theoremName : Name
  priority    : Nat  := eval_prio default
  isSimple : Bool 
  deriving Inhabited, BEq

def FPropTheorem2.toTheorem (thm : FPropTheorem2) : MetaM FPropTheorem :=
  mkFPropTheoremFromConst thm.theoremName thm.priority


/-- Returns `proof` with fresh universe metavariables -/
def FPropTheorem2.getProof (fpropThm : FPropTheorem2) : MetaM Expr := do
  sorry
  -- if fpropThm.proof.isConst && fpropThm.levelParams.isEmpty then
  --   let info ← getConstInfo fpropThm.proof.constName!
  --   if info.levelParams.isEmpty then
  --     return fpropThm.proof
  --   else
  --     return fpropThm.proof.updateConst! (← info.levelParams.mapM (fun _ => mkFreshLevelMVar))
  -- else
  --   let us ← fpropThm.levelParams.mapM fun _ => mkFreshLevelMVar
  --   return fpropThm.proof.instantiateLevelParamsArray fpropThm.levelParams us

local instance : Ord Name := ⟨Name.quickCmp⟩

/-- function name → function property → list of theorems -/
structure FPropTheorems2 where
  theorems     : Std.RBMap Name (Std.RBMap Name (Array FPropTheorem2) compare) compare := {}
  deriving Inhabited

--- 

/-- -/
abbrev FPropTheorems2Ext := SimpleScopedEnvExtension FPropTheorem2 FPropTheorems2

/-- -/
def FPropTheorems2Ext.getTheorems (ext : FPropTheorems2Ext) : CoreM FPropTheorems2 := do
  modifyEnv fun env => ext.modifyState env fun a => a
  return ext.getState (← getEnv)

initialize fpropTheorems2Ext : FPropTheorems2Ext ←
  registerSimpleScopedEnvExtension {
    name     := by exact decl_name%
    initial  := {}
    addEntry := fun d e => 
      {d with 
        theorems := 
          d.theorems.alter e.functionName fun funProperties => 
            let funProperties := funProperties.getD {}
            funProperties.alter e.fpropName fun thms => 
              let thms := thms.getD #[]
              thms.push e}
  }

---

open RefinedDiscrTree in
/-- -/
def mkFPropTheorem2FromConst (declName : Name) (prio : Nat) : MetaM FPropTheorem2 := do
  let info ← getConstInfo declName
  forallTelescope info.type fun _ b => do

  let .some (fpropDecl,_) ← getFProp? b
    | throwError "unrecognize function property in `{← ppExpr b}`"

  let thrmType ← getFPropTheorem2Type b
  
  match thrmType with
  | .simple _ funName mainArgs appliedArgs => 
      return {
        fpropName   := fpropDecl.fpropName
        mainArgs    := mainArgs
        appliedArgs := appliedArgs
        functionName := funName
        theoremName := declName
        isSimple := true
      }
  | .comp _ funName mainArgs appliedArgs => 
      return {
        fpropName   := fpropDecl.fpropName
        mainArgs    := mainArgs
        appliedArgs := appliedArgs
        functionName := funName
        theoremName := declName
        isSimple := false
      }
    | .mor _ => 
      logWarning "morphism theorem"
      return {
        fpropName   := fpropDecl.fpropName
        mainArgs    := #[0].toArraySet
        appliedArgs := 1
        functionName := default
        theoremName := declName
        isSimple := false
      }
    | .transition _ => 
      logWarning "transition theorem"
      return {
        fpropName   := fpropDecl.fpropName
        mainArgs    := #[0].toArraySet
        appliedArgs := 1
        functionName := default
        theoremName := declName
        isSimple := false
      }



/-- -/
def FPropTheorems2Ext.addTheorem (ext : FPropTheorems2Ext) (declName : Name)
  (attrKind : AttributeKind) (prio : Nat) : MetaM Unit := do
  let thrm ← mkFPropTheorem2FromConst declName prio
  ext.add thrm attrKind

/-- -/
def addTheorem2 (declName : Name) (attrKind : AttributeKind) (prio : Nat) 
  : MetaM Unit := do

  let info ← getConstInfo declName
  forallTelescope info.type fun _ b => do

  let .some (fpropDecl,_) ← getFProp? b
    | throwError "unrecognize function property in `{← ppExpr b}`"

  let thrmType ← getFPropTheorem2Type b
  
  match thrmType with
  | .simple _ funName mainArgs appliedArgs => do
    let thm : FPropTheorem2:= {
      fpropName   := fpropDecl.fpropName
      mainArgs    := mainArgs
      appliedArgs := appliedArgs
      functionName := funName
      theoremName := declName
      isSimple := true
    }
    fpropTheorems2Ext.add thm attrKind
    trace[Meta.Tactic.fprop.attr] "added simple theorem `{declName}`\nfunction property `{thm.fpropName}`\nfunction {thm.functionName}\narguments {thm.mainArgs}"

  | .comp _ funName mainArgs appliedArgs => 
    let thm : FPropTheorem2:= {
      fpropName   := fpropDecl.fpropName
      mainArgs    := mainArgs
      appliedArgs := appliedArgs
      functionName := funName
      theoremName := declName
      isSimple := false
    }
    fpropTheorems2Ext.add thm attrKind
    trace[Meta.Tactic.fprop.attr] "added composition theorem `{declName}`\nfunction property `{thm.fpropName}`\nfunction {thm.functionName}\narguments {thm.mainArgs}"

    | .mor _ => 
      logWarning "morphism theorem"
      fpropMorTheoremsExt.addTheorem declName attrKind prio

    | .transition _ => 
      logWarning "transition theorem"
      fpropTransitionTheoremsExt.addTheorem declName attrKind prio


