/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Lean

namespace Mathlib.Prelude.Rename

open Lean
open System (FilePath)
open Lean (HashMap)

/-- This structure keeps track of alignments from lean 3 names to lean 4 names and vice versa. -/
structure RenameMap where
  /-- This maps `n3 ↦ (dubious, n4)` where `n3` is the lean 3 name and `n4` is the corresponding
  lean 4 name. `dubious` is either empty, or a warning message to be displayed when `n3` is
  translated, which indicates that the translation from `n3` to `n4` is approximate and may cause
  downstream errors. -/
  toLean4 : NameMap (String × Name) := {}
  /-- This maps `n4 ↦ (n3, clashes)` where `n4` is the lean 4 name and `n3::clashes` is the list of
  all (non-`synthetic`) declarations that map to `n4`. (That is, we do not assume the mapping
  from lean 3 to lean 4 name is injective.) -/
  toLean3 : NameMap (Name × List Name) := {}
  deriving Inhabited

/-- An `olean` entry for the rename extension. -/
structure NameEntry where
  /-- The lean 3 name. -/
  n3 : Name
  /-- The lean 4 name. -/
  n4 : Name
  /-- If true, this lean 3 -> lean 4 mapping will not be entered into the converse map.
  This is used for "internal" definitions that should never be referred to in the source syntax. -/
  synthetic := false
  /-- A dubious translation is one where there is a type mismatch
  from the translated lean 3 definition to a pre-existing lean 4 definition.
  Type errors are likely in downstream theorems.
  The string stored here is printed in the event that `n3` is encountered by synport. -/
  dubious := ""

/-- Insert a name entry into the `RenameMap`. -/
def RenameMap.insert (m : RenameMap) (e : NameEntry) : RenameMap :=
  let ⟨to4, to3⟩ := m
  let to4 := to4.insert e.n3 (e.dubious, e.n4)
  let to3 := if e.synthetic then to3 else
    match to3.find? e.n4 with
    | none => to3.insert e.n4 (e.n3, [])
    | some (a, l) => if (a::l).contains e.n3 then to3 else to3.insert e.n4 (a, e.n3 :: l)
  ⟨to4, to3⟩

/-- Look up a lean 4 name from the lean 3 name. Also return the `dubious` error message. -/
def RenameMap.find? (m : RenameMap) : Name → Option (String × Name) := m.toLean4.find?

initialize renameExtension : SimplePersistentEnvExtension NameEntry RenameMap ←
  registerSimplePersistentEnvExtension {
    addEntryFn := (·.insert)
    addImportedFn := mkStateFromImportedEntries (·.insert) {}
  }

def getRenameMap (env : Environment) : RenameMap :=
  renameExtension.getState env

def addNameAlignment (n3 n4 : Name) (synthetic := false) (dubious := "") : CoreM Unit := do
  modifyEnv fun env => renameExtension.addEntry env { n3, n4, synthetic, dubious }

open Lean.Elab Lean.Elab.Command

/--
`#align lean_3.def_name Lean4.defName` will record an "alignment" from the lean 3 name
to the corresponding lean 4 name. This information is used by the
[mathport](https://github.com/leanprover-community/mathport) utility to translate later uses of
the definition.

If there is no alignment for a given definition, mathport will attempt to convert
from the lean 3 `snake_case` style to `UpperCamelCase` for namespaces and types and
`lowerCamelCase` for definitions, and `snake_case` for theorems. But for various reasons,
it may fail either to determine whether it is a type, definition, or theorem, or to determine
that a specific definition is in fact being called. Or a specific definition may need a different
name altogether because the existing name is already taken in lean 4 for something else. For
these reasons, you should use `#align` on any theorem that needs to be renamed from the default.
-/
syntax (name := align) "#align " ident ident : command

@[command_elab align] def elabAlign : CommandElab
  | `(#align $id3:ident $id4:ident) => do
    if (← getInfoState).enabled then
      if (← getEnv).contains id4.getId then
        addConstInfo id4 id4.getId none
    if (getRenameMap (← getEnv)).toLean4.contains id3.getId then
      throwErrorAt id3 "{id3.getId} has already been aligned (to {id4.getId})"
    liftCoreM $ addNameAlignment id3.getId id4.getId
  | _ => throwUnsupportedSyntax

/-- Show information about the alignment status of a lean 3 definition. -/
syntax (name := lookup3) "#lookup3 " ident : command

@[command_elab lookup3] def elabLookup3 : CommandElab
  | `(#lookup3%$tk $id3:ident) => do
    let n3 := id3.getId
    let m := getRenameMap (← getEnv)
    match m.find? n3 with
    | none    => logInfoAt tk s!"name `{n3} not found"
    | some (dubious, n4) => do
      let mut msg := m!"{n4}"
      if !dubious.isEmpty then
        msg := msg ++ s!" (dubious: {dubious})"
      logInfoAt tk <|
        match m.toLean3.find? n4 with
        | none | some (_, []) => msg
        | some (n, l) => m!"{msg} (aliases {n :: l})"
  | _ => throwUnsupportedSyntax
