/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Std.Data.RBMap.Alter

/-!
## `funProp` environment extension that stores all registered coercions from a morphism to a function
-/


namespace Mathlib
open Lean Meta

namespace Meta.FunProp


/-- Morphism coercion

Coercion from bundled morphism to function type
-/
structure MorCoeDecl where
  /-- function transformation name -/
  morCoeName : Name
  /--  -/
  morId : Nat
  /--  -/
  argId : Nat
  deriving Inhabited, BEq


private local instance : Ord Name := ⟨Name.quickCmp⟩

/-- -/
structure MorCoeDecls where
  /-- discriminatory tree for function properties -/
  decls : Std.RBMap Name MorCoeDecl compare := {}
  deriving Inhabited

/-- -/
abbrev MorCoeDeclsExt := SimpleScopedEnvExtension MorCoeDecl MorCoeDecls

/-- -/
initialize morCoeDeclsExt : MorCoeDeclsExt ←
  registerSimpleScopedEnvExtension {
    name := by exact decl_name%
    initial := {}
    addEntry := fun d e =>
      {d with decls := d.decls.insert e.morCoeName e}
  }


/-- -/
def addMorCoeDecl (declName : Name) : MetaM Unit := do

  let info ← getConstInfo declName
  let type := info.type

  forallTelescope type fun xs b => do

  let n := xs.size

  -- coercion needs at least two arguments
  if n < 2 then throwError "invalid morphism coercion, expecting function of at least two arguments"

  -- the last argument should be explicit it is the function argument
  -- note: morphisms with functions as codomain are not supported
  if ¬(← xs[n-1]!.fvarId!.getBinderInfo).isExplicit then
    throwError "invalid morphism coercion, last argumet is expected to be explicit {(← xs[n-1]!.fvarId!.getBinderInfo).isExplicit}"
  let argId := n-1

  let fs ← ((Array.range (n-1)).zip xs[0:n-1].toArray)
      |>.filterMapM (fun (i,x) => do
        if (← x.fvarId!.getBinderInfo).isExplicit then
          pure (Option.some i)
        else
          pure none)

  -- apart from the last argument there can be only one more explicit argument and that is
  -- the morphism
  if fs.size ≠ 1 then
    throwError "invalid morphism coercion, expecting only two explicit arguments"
  let morId := fs[0]!

  let decl : MorCoeDecl := {
    morCoeName := declName
    morId := morId
    argId := argId
  }

  modifyEnv fun env => morCoeDeclsExt.addEntry env decl

  trace[Meta.Tactic.fun_prop.attr]
    "registered new morphism coercion `{declName}`
     morphism: {← ppExpr xs[morId]!} : {← ppExpr (← inferType xs[morId]!)}
     argument: {← ppExpr xs[argId]!} : {← ppExpr (← inferType xs[argId]!)}
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
