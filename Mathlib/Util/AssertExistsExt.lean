/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Lean.Environment

/-!
# Environment extension for tracking existence of declarations and imports

This is used by the `assert_not_exists` and `assert_not_imported` commands.
-/

section
open Lean Elab Meta

namespace Mathlib.AssertNotExist

/-- `AssertExists` is the structure that carries the data to check if a declaration or an
import are meant to exist somewhere in Mathlib. -/
structure AssertExists where
  /-- The type of the assertion: `true` means declaration, `false` means import. -/
  isDecl : Bool
  /-- The fully qualified name of a declaration that is expected to exist. -/
  givenName : Name
  /-- The name of the module where the assertion was made. -/
  modName : Name
  deriving BEq, Hashable

/-- Defines the `assertExistsExt` extension for adding a `HashSet` of `AssertExists`s
to the environment. -/
initialize assertExistsExt : SimplePersistentEnvExtension AssertExists (HashSet AssertExists) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun as => as.foldl HashSet.insertMany {}
    addEntryFn := .insert
  }

end Mathlib.AssertNotExist
