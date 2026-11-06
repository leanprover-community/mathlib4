/-
Copyright (c) 2026 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public meta import Lean.Data.Options
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
meta import Mathlib.Tactic.Linter.Header  -- shake: keep

/-!
# Preparation for the `convert` tactic.

This file defines a linter option for the `convert` tactic, in a separate file since linter options
should be imported by `Mathlib.Init`.
-/

public meta section

/-- Check while running `convert!` that it can be replaced with `convert`.

This roughly doubles the running time for `convert!` so it is not enabled by default.
-/
register_option linter.convertExclamation : Bool := {
  defValue := false
  descr := "enable the `convert!` to `convert` replacement linter"
}
