/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
import Lean
import Batteries.Data.List.Basic

open Lean Elab Meta

/-- `#import_diff foo` computes the new transitive imports that are added to a given file when
module `foo` is added to the set of imports of the file. -/
elab "#import_diff" n:ident : command => do
  let name := n.getId
  let env ← MonadEnv.getEnv
  let current_all_imports := env.allImportedModuleNames
  let current_imports := env.imports
  let new_imports := current_imports.push { module := name }
  let new_all_imports := (← Lean.importModules new_imports {}).allImportedModuleNames
  let import_diff := new_all_imports.toList.diff current_all_imports.toList
  Lean.logInfo s!"{import_diff}"

--TODO(Paul-Lez): maybe we want to be able to take `#import_diff foo₁ foo₂ foo₃ ...`?
