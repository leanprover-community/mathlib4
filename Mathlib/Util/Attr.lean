/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Mathlib.Init
import Lean.Elab.Command

/-!
# User commands for assert the (non-)existence of declaration or instances.

These commands are used to enforce the independence of different parts of mathlib.

## TODO

Potentially after the port reimplement the mathlib 3 linters to check that declarations asserted
about do eventually exist.

Implement `assert_instance` and `assert_no_instance`
-/

section
open Lean Elab Meta Command

namespace Mathlib.AssertNotExist
structure AssertExists where
  /-- The fully qualified name of a declaration that is expected to exist. -/
  isDecl : Bool
  givenName : Name
  modName : Name

/-- Defines the `assertExistsExt` extension for adding an `Array` of `AssertExists`s
to the environment. -/
initialize assertExistsExt : PersistentEnvExtension AssertExists AssertExists (Array AssertExists) ←
  registerPersistentEnvExtension {
    mkInitial := pure {}
    addImportedFn := (return .flatten ·)
    addEntryFn := .push
    exportEntriesFn := id
  }

end Mathlib.AssertNotExist
