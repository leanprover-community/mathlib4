/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Std.CodeAction.Misc
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Hint

/-!
# Run `hint` in holes.
-/

open Lean Meta Server RequestM
open Std.CodeAction
open Mathlib.Tactic.LibrarySearch

namespace Mathlib.CodeAction

open Lean Elab Term Tactic

def hint (stx : Syntax) (ty : Expr) : MetaM Unit := TermElabM.run' do
  let g ← mkFreshExprMVar ty
  _ ← Tactic.run g.mvarId! (Hint.hint stx)

/--
Whenever the cursor is at a `_` or `sorry`, run `hint`.
-/
@[hole_code_action] def runHintInHole : HoleCodeAction :=
  fun _ _ ctx info => do
    let some ty := info.expectedType? | return #[]
    info.runMetaM ctx do
      hint info.stx ty
    return #[]

end Mathlib.CodeAction

register_hint decide

example : 1 + 2 = 3 := _
