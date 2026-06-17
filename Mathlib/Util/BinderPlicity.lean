/-
Copyright (c) 2026 Fernando Leal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Leal, Thomas Murrills
-/
module

-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public import Mathlib.Tactic.Linter.Header -- shake: keep
public meta import Lean.Server.CodeActions.Basic

/-!
# Binder plicity code action

A code action that allows one to switch between explicit and implicit binders.

 - `(x : Nat)` turns into `{x : Nat}`
 - `{x : nat}` turns into `(x : Nat)`

## Implementation notes

We make use of `Syntax.reprint` to transform our new syntax into
a `String`. Since `Syntax.reprint` adds whitespace when working
over synthetic syntax nodes, we produce the new syntax by modifying
the old one instead of creating it from scratch.
-/

namespace Mathlib.CodeAction

public meta section

open Lean Server Lsp Parser.Term

/-- A code action to switch between explicit and implicit binders -/
@[code_action_provider]
def binderPlicity : CodeActionProvider := fun params snap => do
  let doc ← RequestM.readDoc
  let mkCodeAction kind range newText : LazyCodeAction := {
      eager.title := s!"Make {kind}: {newText}"
      eager.kind? := "refactor.rewrite"
      eager.edit? := some <| .ofTextEdit doc.versionedIdentifier { range, newText } }
  let mut codeActions := #[]
  for stx in snap.stx.topDown do
    let some stxRange := stx.getRange? | continue
    let lspRange := doc.meta.text.utf8RangeToLspRange stxRange
    unless lspRange.start ≤ params.range.end do continue
    unless params.range.start ≤ lspRange.end do continue
    if stx.isOfKind ``explicitBinder then
      -- This code action does not support explicit binders with optional values
      unless stx[3].isNone do continue
      let newStx := stx.modifyArg 0 fun lparen => Syntax.atom lparen.getHeadInfo "{"
      let newStx := newStx.modifyArg 4 fun rparen => Syntax.atom rparen.getHeadInfo "}"
      let some newText := newStx.unsetTrailing.reprint | continue
      codeActions := codeActions.push <| mkCodeAction "implicit" lspRange newText
    else if stx.isOfKind ``implicitBinder then
      let newStx := stx.modifyArg 0 fun lparen => Syntax.atom lparen.getHeadInfo "("
      let newStx := newStx.modifyArg 3 fun rparen => Syntax.atom rparen.getHeadInfo ")"
      let some newText := newStx.unsetTrailing.reprint | continue
      codeActions := codeActions.push <| mkCodeAction "explicit" lspRange newText
  return codeActions
