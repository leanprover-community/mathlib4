/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Elab.Command
import Batteries.Tactic.Lint.Basic

/-!
# The `AssertNot` environment extension and the `assertNot` environment linter
-/

open Lean

namespace Mathlib.Linter

/-- A `Label` is the main structure for converting a folder into a `t-`label.
* The `label` field is the actual GitHub label.
* The `dirs` field is the array of all "root paths" such that a modification in a file contained
  in one of these paths should be labeled by `label`.
* The `exclusions` field is the array of all "root paths" that are excluded, among the
  ones that start with the ones in `dirs`.

It is not really intended to be used directly.
The command `add_label` manages `Label`s: it creates them and adds them to the `Environment`.
-/
structure AssertExists where
  /-- The fully qualified name of a declaration that is expected to exist. -/
  isDecl : Bool
  freshName : Name
  givenName : Name
  modName : Name

/-- Defines the `assertExistsExt` extension for adding an `Array` of `AssertExists`s
to the environment. -/
initialize assertExistsExt :
    PersistentEnvExtension AssertExists AssertExists (Array AssertExists) ←
  registerPersistentEnvExtension {
    mkInitial := pure {}
    addImportedFn := (pure <| .flatten ·)
    addEntryFn := .push
    exportEntriesFn := id
  }

end Mathlib.Linter
