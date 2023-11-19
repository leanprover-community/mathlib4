/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Std.CodeAction.Misc
import Mathlib.Tactic.Hint

/-!
# Run `hint` in holes, providing code actions for successful tactics.
-/

open Std.CodeAction
open Std.Tactic.TryThis
open Mathlib.Tactic.Hint
open Lean Meta Server RequestM Elab Term Tactic

namespace Mathlib.CodeAction

/-- Turn `Suggestion`s into `LazyCodeAction`s. -/
def toCodeActions (ctx : ContextInfo) (info : TermInfo) (suggestions : Array Suggestion) :
    RequestM (Array LazyCodeAction) := do
  let doc ← readDoc
  let mut result := #[]
  for h : i in [:suggestions.size] do
    let newText := s!"by {← info.runMetaM ctx do suggestions[i]'h.2 |>.suggestion.pretty}"
    let range := doc.meta.text.utf8RangeToLspRange
      ⟨info.stx.getPos?.get!, info.stx.getTailPos?.get!⟩
    result := result.push {
      eager.title := "Try this: " ++ newText
      eager.kind? := "quickfix"
      -- Only make the first option preferred
      eager.isPreferred? := if i = 0 then true else none
      eager.edit? := some <| .ofTextEdit doc.versionedIdentifier { range,  newText }
    }
  return result

/--
Whenever the cursor is at a term mode `_` or `sorry`,
run `hint` and generate a code action for each successful tactic.
-/
@[hole_code_action] def runHintInHole : HoleCodeAction :=
  fun _ _ ctx info => do
    let some ty := info.expectedType? | return #[]
    toCodeActions ctx info <|
      (← info.runMetaM ctx do hints (← mkFreshExprMVar ty).mvarId!).map (·.1)

end Mathlib.CodeAction
