/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean

/-!
# Code to move to `Mathlib.Lean` or (eventually) core.

Mostly additional functions to deal with `InfoTree`.
-/

open Lean Elab Meta

-- Weird, why isn't this available in core already?
instance [MonadLift m n] : MonadLift (StateT α m) (StateT α n) where
  monadLift := fun f s => f s

namespace Lean.Syntax

-- TODO better implementation
def isSorry (stx : Syntax) : Bool := s!"{stx}" = "(Tactic.tacticSorry \"sorry\")"

end Lean.Syntax

namespace Lean.Elab

/-- Extract the range of a `Syntax` expressed as lines and columns. -/
-- Extracted from the private declaration `Lean.Elab.formatStxRange`,
-- in `Lean.Elab.InfoTree.Main`.
def stxRange (fileMap : FileMap) (stx : Syntax) : Position × Position :=
let pos    := stx.getPos?.getD 0
let endPos := stx.getTailPos?.getD pos
(fileMap.toPosition pos, fileMap.toPosition endPos)

end Lean.Elab

namespace Lean.Elab.InfoTree

/-- Analogue of `Lean.Elab.InfoTree.findInfo?`. -/
partial def findAllInfo (t : InfoTree) (ctx : Option ContextInfo) (p : Info → Bool) :
    List (Info × Option ContextInfo) :=
match t with
| context ctx t => t.findAllInfo ctx p
| node i ts  => (if p i then [(i, ctx)] else []) ++ ts.toList.bind (fun t => t.findAllInfo ctx p)
| _ => []

/-- Return all `TacticInfo` nodes in an `InfoTree` corresponding to explicit invocations of `sorry`,
each equipped with its relevant `ContextInfo`. -/
partial def findSorryNodes (t : InfoTree) : List (TacticInfo × ContextInfo) :=
let infos := t.findAllInfo none fun i => match i with
  | .ofTacticInfo i => i.stx.isSorry
  | _ => false
infos.filterMap fun p => match p with
| (.ofTacticInfo i, some ctx) => (i, ctx)
| _ => none

/--
Finds all appearances of `sorry` in an `InfoTree`, reporting
* the `ContextInfo` at that point,
* the `MVarId` for the goal that was closed by `sorry`,
* and the start and end positions of the `sorry` in the file.
-/
partial def sorries (t : InfoTree) : List (ContextInfo × MVarId × Position × Position) :=
t.findSorryNodes.map fun ⟨i, ctx⟩ =>
  ({ ctx with mctx := i.mctxBefore }, i.goalsBefore.head!, stxRange ctx.fileMap i.stx)

end Lean.Elab.InfoTree
