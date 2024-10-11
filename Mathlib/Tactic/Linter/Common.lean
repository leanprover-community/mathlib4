/-
Copyright (c) 2024 Moritz Firsching All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Moritz Firsching
-/

import Lean.DeclarationRange

/-!
This file contains functions that are used by multiple linters.
-/

open Lean Parser Elab Command Meta
namespace Mathlib.Linter

/--
If `pos` is a `String.Pos`, then `getNamesFrom pos` returns the array of identifiers
for the names of the declarations whose syntax begins in position at least `pos`.
-/
def getNamesFrom {m} [Monad m] [MonadEnv m] [MonadFileMap m] (pos : String.Pos) :
    m (Array Syntax) := do
  let drs := declRangeExt.getState (← getEnv)
  let fm ← getFileMap
  let mut nms := #[]
  for (nm, rgs) in drs do
    if pos ≤ fm.ofPosition rgs.range.pos then
      let ofPos1 := fm.ofPosition rgs.selectionRange.pos
      let ofPos2 := fm.ofPosition rgs.selectionRange.endPos
      nms := nms.push (mkIdentFrom (.ofRange ⟨ofPos1, ofPos2⟩) nm)
  return nms
