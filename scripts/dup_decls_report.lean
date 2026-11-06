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

-- We don't `open Lean`, since that would shorten `Lean.*` names in the report.
open Mathlib.Tactic.DuplicateDecls

-- Each scan below traverses the entire environment, which exceeds the default heartbeat limit.
set_option maxHeartbeats 0

run_meta do Lean.logInfo "=== Duplicate theorems ==="
run_meta do Lean.logInfo m!"{← lintDuplicateDeclarations .theorems}"
run_meta do Lean.logInfo "=== Duplicate instances ==="
run_meta do Lean.logInfo m!"{← lintDuplicateDeclarations .instances}"
run_meta do Lean.logInfo "=== Duplicate defs ==="
run_meta do Lean.logInfo m!"{← lintDuplicateDeclarations .defs}"
