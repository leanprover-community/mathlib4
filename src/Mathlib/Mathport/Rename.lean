/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Lean

namespace Mathlib.Prelude.Rename

open Lean
open System (FilePath)
open Std (HashMap)

abbrev RenameMap := HashMap Name Name

def RenameMap.insertPair (m : RenameMap) : Name × Name → RenameMap
  | (n3, n4) => m.insert n3 n4

initialize renameExtension : SimplePersistentEnvExtension (Name × Name) RenameMap ←
  registerSimplePersistentEnvExtension {
    name          := `renameMapExtension
    addEntryFn    := RenameMap.insertPair
    addImportedFn := fun es => mkStateFromImportedEntries (RenameMap.insertPair) {} es
  }

def getRenameMap (env : Environment) : RenameMap :=
  renameExtension.getState env

def addNameAlignment (n3 n4 : Name) : CoreM Unit := do
  modifyEnv fun env => renameExtension.addEntry env (n3, n4)

open Lean.Elab Lean.Elab.Command

syntax (name := align) "#align " ident ident : command

@[commandElab align] def elabAlign : CommandElab
  | `(#align%$tk $id3:ident $id4:ident) =>
    liftCoreM $ addNameAlignment id3.getId id4.getId
  | _ => throwUnsupportedSyntax

syntax (name := lookup3) "#lookup3 " ident : command

@[commandElab lookup3] def elabLookup3 : CommandElab
  | `(#lookup3%$tk $id3:ident) => do
    let n3 := id3.getId
    match getRenameMap (← getEnv) |>.find? n3 with
    | none    => logInfoAt tk s!"name `{n3} not found"
    | some n4 => logInfoAt tk s!"{n4}"
  | _ => throwUnsupportedSyntax

end Mathlib.Prelude.Rename
