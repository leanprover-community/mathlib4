/-
Copyright (c) 2025 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/

-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
import Mathlib.Tactic.Linter.Header

/-! # "Warning as error" wrapper

This file contains a wrapper `Lean.Meta.withWarningAsError : MetaM α → MetaM α`, which causes a
`MetaM` program to fail if it is noisy.
-/

open Lean Elab Term Command Linter

/-- A wrapper for a `MetaM` program, causing it to fail if it produces unreported messages. -/
def Lean.Meta.withWarningAsError {α : Type} (m : MetaM α) : MetaM α := do
  let a ← m
  let msgs := (← getThe Core.State).messages.unreported
  if msgs.isEmpty then
    return a
  else
    throwError "{msgs.size} unreported messages"
