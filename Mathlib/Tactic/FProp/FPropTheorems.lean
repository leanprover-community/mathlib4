/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Lean.Meta.Tactic.Simp.Types
import Std.Data.RBMap.Alter
import Mathlib.Tactic.FProp.RefinedDiscrTree
import Mathlib.Tactic.FProp.FPropDecl

/-!
## `fprop` 

this file defines enviroment extension for `fprop`
-/


namespace Mathlib
open Lean Meta

namespace Meta.FProp

structure FPropTheorem where
  fpropName   : Name
  keys        : Array RefinedDiscrTree.Key := #[]
  levelParams : Array Name := #[]
  proof       : Expr
  priority    : Nat  := eval_prio default
  origin      : Origin
  deriving Inhabited, BEq

structure FPropTheorems where
  theorems     : RefinedDiscrTree FPropTheorem := {}
  deriving Inhabited

--- 

abbrev FPropTheoremsExt := SimpleScopedEnvExtension FPropTheorem FPropTheorems

def FPropTheoremsExt.getTheorems (ext : FPropTheoremsExt) : CoreM FPropTheorems := do
  modifyEnv fun env => ext.modifyState env fun a => a
  return ext.getState (← getEnv)

initialize fpropTheoremsExt : FPropTheoremsExt ←
  registerSimpleScopedEnvExtension {
    name     := by exact decl_name%
    initial  := {}
    addEntry := fun d e => {d with theorems := d.theorems.insertInRefinedDiscrTree e.keys e}
  }

---

open RefinedDiscrTree in
def mkFPropTheoremFromConst (declName : Name) (prio : Nat) : MetaM FPropTheorem := do
  let info ← getConstInfo declName
  let .some proof := info.value?
    | throwError "invalud fprop theorem `{declName}`"

  let (_,_,b) ← forallMetaTelescope info.type

  let .some (decl,_) ← getFProp? b
    | throwError "unrecognize function property in `{← ppExpr b}`"

  return {
    fpropName := decl.fpropName
    keys := ← mkPath b
    levelParams := info.levelParams.toArray
    proof := proof
    priority := prio
    origin := .decl declName
  }

def FPropTheoremsExt.addTheorem (ext : FPropTheoremsExt) (declName : Name) 
  (attrKind : AttributeKind) (prio : Nat) : MetaM Unit := do
  let thrm ← mkFPropTheoremFromConst declName prio
  ext.add thrm attrKind

def addTheorem (declName : Name) (attrKind : AttributeKind) (prio : Nat) 
  : MetaM Unit := do
  let thrm ← mkFPropTheoremFromConst declName prio
  fpropTheoremsExt.add thrm attrKind

  trace[Meta.Tactic.fprop.attr] "added theorem `{declName}` of function property `{thrm.fpropName}`\nlook up pattern is `{thrm.keys}`"


  
