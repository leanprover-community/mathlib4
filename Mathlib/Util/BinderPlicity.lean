/-
Copyright (c) 2026 Fernando Leal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Leal, Thomas Murrills
-/
module

public meta import Lean.Server.CodeActions.Basic

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
                     |>.modifyArg 4 fun rparen => Syntax.atom rparen.getHeadInfo "}"
      let some newText := newStx.unsetTrailing.reprint | continue
      codeActions := codeActions.push <| mkCodeAction "implicit" lspRange newText
    else if stx.isOfKind ``implicitBinder then
      let newStx := stx.modifyArg 0 fun lparen => Syntax.atom lparen.getHeadInfo "("
                     |>.modifyArg 3 fun rparen => Syntax.atom rparen.getHeadInfo ")"
      let some newText := newStx.unsetTrailing.reprint | continue
      codeActions := codeActions.push <| mkCodeAction "explicit" lspRange newText
  return codeActions
where 
