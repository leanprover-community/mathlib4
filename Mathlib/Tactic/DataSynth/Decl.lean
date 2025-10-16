/-
Copyright (c) 2025 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
import Mathlib.Lean.Meta.RefinedDiscrTree
import Mathlib.Tactic.DataSynth.Types

import Qq

/-! Structure and enviroment extension storing `data_synth` declarations.

-/

open Lean Meta

namespace Mathlib.Meta.DataSynth


initialize emptyDispatch : IO.Ref (Goal → DataSynthM (Option Result))
  ← IO.mkRef fun _ => return none
initialize emptyTheoremsRegister : IO.Ref (Name → Syntax → AttributeKind → AttrM Bool)
  ← IO.mkRef fun _ _ _ => return false

local instance : Inhabited (IO.Ref (Goal → DataSynthM (Option Result))) := ⟨emptyDispatch⟩
local instance : Inhabited (IO.Ref (Name → Syntax → AttributeKind → AttrM Bool)) :=
  ⟨emptyTheoremsRegister⟩

/-- Each type of `data_synth` goal like `HasFDerivAt`, `HasFDerivWithinAt` etc. is
called `data_synth` declaration and the structure `DataSynthDecl` stores information on which
arguments are considered as input or output. For example for `HasFDerivAt R f f' x` arguments `R`,
`f` and `x` are considered as input arguments and `f'` as output argument.
-/
structure DataSynthDecl where
  /-- Name of the `data_synth` declaration e.g. `HasFDerivAt`. -/
  name : Name := default
  /-- Number of arguments of the decalaration e.g. `HasFDerivAt` has 13 arguments including implicit
  and instance implicit arguments. -/
  nargs : Nat := 0
  /-- Indices of arguments that are considered as outputs e.g. for `HasFDerivAt` only `f'` is
  considered as output argument and its index is 11. -/
  outputArgs : Array Nat := #[]
  /-- If normal call to `data_synth` fails then try this callback. This is used in cases when custom
  unification is needed like application of `HasFDerivAt.comp`. -/
  customDispatchName? : Option Name -- Goal → DataSynthM (Option Result)
  /-- Custom theorem registration, `data_synth` with custom dispatch might want to register certain
  theorems differently. This custom call will be used before registering a theorem as normal
  `data_synth` theorem. If `true` is returned then the theorem is not registered as normal
  `data_synth` theorem.

  For example, `HasFDerivAt` will use this to register `HasFDerivAt.comp/pi/apply` theorems as
  they need custom unification procedure. -/
  customTheoremRegisterName? : Option Name
deriving Inhabited

/-- Type for the environment extension storing all `data_synth` declarations. -/
abbrev DataSynthDeclsExt := SimpleScopedEnvExtension DataSynthDecl (NameMap DataSynthDecl)

/-- Environment extension storing all `data_synth` declarations. -/
initialize dataSynthDeclsExt : DataSynthDeclsExt ←
  registerSimpleScopedEnvExtension {
    name := by exact decl_name%
    initial := {}
    addEntry := fun d e => d.insert e.name e
  }

open Qq in
private unsafe def DataSynthDecl.getCustomDispatchImpl (decl : DataSynthDecl) :
    MetaM (Option (Goal → DataSynthM (Option Result))) := do

  let some name := decl.customDispatchName? | return none
  let disch ← Meta.evalExpr (Goal → DataSynthM (Option Result))
    q(Goal → DataSynthM (Option Result)) (Expr.const name [])
  return disch

@[implemented_by DataSynthDecl.getCustomDispatchImpl]
opaque DataSynthDecl.getCustomDispatch (decl : DataSynthDecl) :
    MetaM (Option (Goal → DataSynthM (Option Result)))

open Qq in
def setCustomDispatch (dataSynthName : Name) (dispatchName : Name) : MetaM Unit := do
  let info ← getConstInfo dispatchName

  unless (← isDefEq q(Goal → DataSynthM (Option Result)) info.type) do
    throwError m!"{dispatchName} is not valid data_synth dispatch function!"

  let s := dataSynthDeclsExt.getState (← getEnv)
  if let some decl := s.find? dataSynthName then
    dataSynthDeclsExt.add { decl with customDispatchName? := dispatchName }

open Qq in
private unsafe def DataSynthDecl.getCustomTheoremRegisterImpl (decl : DataSynthDecl) :
    MetaM (Option (Name → Syntax → AttributeKind → AttrM Bool)) := do

  let some name := decl.customTheoremRegisterName? | return none
  let disch ← Meta.evalExpr (Name → Syntax → AttributeKind → AttrM Bool)
    q(Name → Syntax → AttributeKind → AttrM Bool) (Expr.const name [])
  return disch

@[implemented_by DataSynthDecl.getCustomTheoremRegisterImpl]
opaque DataSynthDecl.getCustomTheoremRegister (decl : DataSynthDecl) :
    MetaM (Option (Name → Syntax → AttributeKind → AttrM Bool))

open Qq in
def setCustomTheoremRegister (dataSynthName : Name) (theoremRegisterName : Name) : MetaM Unit := do
  let info ← getConstInfo theoremRegisterName

  unless (← isDefEq q(Name → Syntax → AttributeKind → AttrM Bool) info.type) do
    throwError m!"{theoremRegisterName} is not valid data_synth theorem register function!"

  let s := dataSynthDeclsExt.getState (← getEnv)
  if let some decl := s.find? dataSynthName then
    dataSynthDeclsExt.add { decl with customTheoremRegisterName? := theoremRegisterName }


/-- Get `data_synth` declaration if `e` is a `data_synth` goal. -/
def getDataSynth? (e : Expr) : MetaM (Option DataSynthDecl) := do

  let e ← whnfR e

  let ext := dataSynthDeclsExt.getState (← getEnv)

  let .some (fnName,_) := e.getAppFn'.const?
    | return none

  let .some DataSynthDecl := ext.find? fnName
    | return none

  if e.getAppNumArgs' = DataSynthDecl.nargs then
    return DataSynthDecl
  else
    return none


/-- Add `data_synth` declaration to the environment. -/
def addDataSynthDecl (declName : Name) (outArgs : Array Name) :
    MetaM Unit := do

  let info ← getConstInfo declName

  let (xs,_,_) ← forallMetaTelescope info.type

  -- get all argument names
  let argNames ←
    forallTelescope info.type fun xs _ =>
      xs.mapM (fun x => x.fvarId!.getUserName)

  -- convert names to indices
  let outputArgs : Array Nat ←
    outArgs.mapM (fun arg => do
      let some i := argNames.findIdx? (arg==·)
        | throwError "argument {arg} not found"
      pure i)

  -- make new reference unique to this `data_synth` declaration

  let decl : DataSynthDecl := {
    name := declName
    nargs := xs.size
    outputArgs := outputArgs
    customDispatchName? := none
    customTheoremRegisterName? := none
  }

  modifyEnv (dataSynthDeclsExt.addEntry · decl)

end Mathlib.Meta.DataSynth
