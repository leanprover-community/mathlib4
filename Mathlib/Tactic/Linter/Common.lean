/-
Copyright (c) 2024 Moritz Firsching All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Moritz Firsching
-/

import Lean.Elab.Command

/-!
This file contains functions that are used by multiple linters.
-/

open Lean Parser Elab Command Meta
namespace Mathlib.Linter

/--
If `stx` is a declaration, then `getNames stx` returns the array of identifiers
for the name of the declarations whose syntax range is contained in `stx`.
-/
def getNames {m} [Monad m] [MonadEnv m] [MonadFileMap m] (stx : Syntax) : m (Array Syntax) := do
  let drs := declRangeExt.getState (← getEnv)
  let stxPos := stx.getRange?.getD default
  let fm ← getFileMap
  let stxPos1 := stxPos.start
  let stxPos2 := stxPos.stop
  let mut nms := #[]
  for (nm, rgs) in drs do
    if stxPos1 ≤ fm.ofPosition rgs.range.pos && fm.ofPosition rgs.range.pos ≤ stxPos2 then
      let ofPos1 := fm.ofPosition rgs.selectionRange.pos
      let ofPos2 := fm.ofPosition rgs.selectionRange.endPos
      nms := nms.push (mkIdentFrom (.ofRange ⟨ofPos1, ofPos2⟩) nm)
  return nms
