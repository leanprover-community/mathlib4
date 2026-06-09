/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import Mathlib

/-!
# Report of duplicate declarations across Mathlib

This script imports all of `Mathlib` and runs `Mathlib.Tactic.DuplicateDecls`
for theorems, instances, and definitions, logging the results.

Note: this file deliberately does not use the module system, since
`lintDuplicateDeclarations` inspects values, not just types.
-/

open Mathlib.Tactic.DuplicateDecls

run_meta do logInfo "=== Duplicate theorems ==="
run_meta do logInfo m!"{← lintDuplicateDeclarations .theorems}"
run_meta do logInfo "=== Duplicate instances ==="
run_meta do logInfo m!"{← lintDuplicateDeclarations .instances}"
run_meta do logInfo "=== Duplicate defs ==="
run_meta do logInfo m!"{← lintDuplicateDeclarations .defs}"
