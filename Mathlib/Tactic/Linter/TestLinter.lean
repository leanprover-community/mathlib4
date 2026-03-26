/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public import Lean.Elab.Command
import Mathlib.Lean.Elab.InfoTree

/-! For benching. -/

open Lean Elab

/--
If `pos` is a `String.Pos`, then `getNamesFrom pos` returns the array of identifiers
for the names of the declarations whose syntax begins in position at least `pos`.
-/
def getNamesAndRanges {m} [Monad m] [MonadEnv m] [MonadFileMap m] (pos : String.Pos.Raw) :
    m (Array (Name × DeclarationRanges)) := do
  -- declarations from parallelism branches should not be interesting here, so use `local`
  let drs := declRangeExt.getState (asyncMode := .local) (← getEnv)
  let fm ← getFileMap
  let pos := fm.toPosition pos
  let mut nms := #[]
  for nmWithRange in drs do
    unless nmWithRange.2.range.pos.lt pos do
      nms := nms.push nmWithRange
  return nms

/-- Does work. -/
def workLinter : Linter where
  run cmd := do
    let some pos := cmd.getPos? | return
    let _ ← getNamesAndRanges pos

initialize addLinter workLinter
