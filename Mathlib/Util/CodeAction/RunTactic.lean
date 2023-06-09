/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Std.CodeAction.Misc
import Mathlib.Tactic.LibrarySearch

/-!
# Run tactics in holes.

A helper function to run a `MVarId → MetaM Unit` whenever the cursor is at a `_` or `sorry`.
-/

open Lean Meta Server RequestM
open Std.CodeAction
open Mathlib.Tactic.LibrarySearch

namespace Mathlib.CodeAction

/--
Whenever the cursor is at a `_` or `sorry`, try running the given tactic,
reporting a successful result via a code action.
-/
def runTacticInHole (name : String) (tac : MVarId → MetaM Unit) : HoleCodeAction :=
  fun params _ ctx info => do
    let some ty := info.expectedType? | return #[]
    let result ← info.runMetaM ctx do
      let g ← mkFreshExprMVar ty
      tac g.mvarId!
      ppExpr (← instantiateMVars g)
    let eager := {
      title := s!"Use a solution provided by {name}."
      kind? := "quickfix"
      isPreferred? := true
    }
    let doc ← readDoc
    let holePos := info.stx.getPos?.get!
    return #[{
      eager
      lazy? := some <| pure
        { eager with
          edit? := some <| .ofTextEdit params.textDocument.uri {
            range := doc.meta.text.utf8RangeToLspRange ⟨holePos, info.stx.getTailPos?.get!⟩
            newText := toString result
          } }
    }]

/--
Run `library_search` against any hole or sorry that you put the cursor on.
-/
@[hole_code_action] partial def librarySearchAction : HoleCodeAction :=
  runTacticInHole "library_search" librarySearchSolve

end Mathlib.CodeAction
