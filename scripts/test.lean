/-
Copyright (c) 2024 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
open IO.Process
open System

/--
Run tests, via the Batteries test runner.

When https://github.com/leanprover/lean4/issues/4121
"allow using an upstream executable as a lake `@[test_runner]`"
is resolved, this file can be replaced with a line in `lakefile.lean`.
-/
def main (args : List String) : IO Unit := do
  -- ProofWidgets may not have been built by `lake build` yet, but it is needed by some tests.
  _ ← (← spawn { cmd := "lake", args := #["build", "ProofWidgets"] }).wait
  let exitcode ← (← spawn { cmd := "lake", args := #["exe", "batteries/test"] ++ args }).wait
  exit exitcode.toUInt8
