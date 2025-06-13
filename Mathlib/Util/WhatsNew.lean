/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Mathlib.Init

/-!
Defines a command wrapper that prints the changes the command makes to the
environment.

```
whatsnew in
theorem foo : 42 = 6 * 7 := rfl
```
-/

open Lean Elab Command

namespace Mathlib.WhatsNew

private def throwUnknownId (id : Name) : CommandElabM Unit :=
  throwError "unknown identifier '{mkConst id}'"

private def levelParamsToMessageData (levelParams : List Name) : MessageData :=
  match levelParams with
  | []    => ""
  | u::us => Id.run <| do
    let mut m := m!".\{{u}"
    for u in us do
      m := m ++ ", " ++ toMessageData u
    return m ++ "}"

private def mkHeader (kind : String) (id : Name) (levelParams : List Name) (type : Expr)
    (safety : DefinitionSafety) : CoreM MessageData := do
  let m : MessageData :=
    match safety with
    | DefinitionSafety.unsafe  => "unsafe "
    | DefinitionSafety.partial => "partial "
    | DefinitionSafety.safe    => ""
  let m := if isProtected (← getEnv) id then m ++ "protected " else m
  let (m, id) := match privateToUserName? id with
    | some id => (m ++ "private ", id)
    | none    => (m, id)
  let m := m ++ kind ++ " " ++ id ++ levelParamsToMessageData levelParams ++ " : " ++ type
  pure m

private def mkHeader' (kind : String) (id : Name) (levelParams : List Name) (type : Expr)
    (isUnsafe : Bool) : CoreM MessageData :=
  mkHeader kind id levelParams type
    (if isUnsafe then DefinitionSafety.unsafe else DefinitionSafety.safe)

private def printDefLike (kind : String) (id : Name) (levelParams : List Name) (type : Expr)
    (value : Expr) (safety := DefinitionSafety.safe) : CoreM MessageData :=
  return (← mkHeader kind id levelParams type safety) ++ " :=" ++ Format.line ++ value

private def printInduct (id : Name) (levelParams : List Name) (_numParams : Nat) (_numIndices : Nat)
    (type : Expr) (ctors : List Name) (isUnsafe : Bool) : CoreM MessageData := do
  let mut m ← mkHeader' "inductive" id levelParams type isUnsafe
  m := m ++ Format.line ++ "constructors:"
  for ctor in ctors do
    let cinfo ← getConstInfo ctor
    m := m ++ Format.line ++ ctor ++ " : " ++ cinfo.type
  pure m

private def printIdCore (id : Name) : ConstantInfo → CoreM MessageData
  | ConstantInfo.axiomInfo { levelParams := us, type := t, isUnsafe := u, .. } =>
    mkHeader' "axiom" id us t u
  | ConstantInfo.defnInfo { levelParams := us, type := t, value := v, safety := s, .. } =>
    printDefLike "def" id us t v s
  | ConstantInfo.thmInfo { levelParams := us, type := t, value := v, .. } =>
    printDefLike "theorem" id us t v
  | ConstantInfo.opaqueInfo { levelParams := us, type := t, isUnsafe := u, .. } =>
    mkHeader' "constant" id us t u
  | ConstantInfo.quotInfo { levelParams := us, type := t, .. } =>
    mkHeader' "Quotient primitive" id us t false
  | ConstantInfo.ctorInfo { levelParams := us, type := t, isUnsafe := u, .. } =>
    mkHeader' "constructor" id us t u
  | ConstantInfo.recInfo { levelParams := us, type := t, isUnsafe := u, .. } =>
    mkHeader' "recursor" id us t u
  | ConstantInfo.inductInfo
      { levelParams := us, numParams, numIndices, type := t, ctors, isUnsafe := u, .. } =>
    printInduct id us numParams numIndices t ctors u

def diffExtension (old new : Environment)
    (ext : PersistentEnvExtension EnvExtensionEntry EnvExtensionEntry EnvExtensionState) :
    CoreM (Option MessageData) := unsafe do
  let mut asyncMode := ext.toEnvExtension.asyncMode
  if asyncMode matches .async then
    -- allow for diffing async extensions by bumping mode to sync
    asyncMode := .sync
  let oldSt := ext.toEnvExtension.getState (asyncMode := asyncMode) old
  let newSt := ext.toEnvExtension.getState (asyncMode := asyncMode) new
  if ptrAddrUnsafe oldSt == ptrAddrUnsafe newSt then return none
  let oldEntries := ext.exportEntriesFn (← getEnv) oldSt.state .private
  let newEntries := ext.exportEntriesFn (← getEnv) newSt.state .private
  pure m!"-- {ext.name} extension: {(newEntries.size - oldEntries.size : Int)} new entries"

def whatsNew (old new : Environment) : CoreM MessageData := do
  let mut diffs := #[]

  for (c, i) in new.constants.map₂.toList do
    unless old.constants.map₂.contains c do
      diffs := diffs.push (← printIdCore c i)

  for ext in ← persistentEnvExtensionsRef.get do
    if let some diff := ← diffExtension old new ext then
      diffs := diffs.push diff

  if diffs.isEmpty then return "no new constants"

  pure <| MessageData.joinSep diffs.toList "\n\n"

/-- `whatsnew in $command` executes the command and then prints the
declarations that were added to the environment. -/
elab "whatsnew " "in" ppLine cmd:command : command => do
  let oldEnv ← getEnv
  try
    elabCommand cmd
  finally
    let newEnv ← getEnv
    logInfo (← liftCoreM <| whatsNew oldEnv newEnv)

end Mathlib.WhatsNew
