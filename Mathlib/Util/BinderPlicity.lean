/-
Copyright (c) 2026 Fernando Leal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Leal, Thomas Murrills
-/
module

public meta import Lean

public meta section
open Lean Meta Server Lsp

open Lean.Parser.Term in
/-- A code action to switch between explicit and implicit binders -/
@[code_action_provider]
def binderPlicity : CodeActionProvider := fun params snap => do
  let mut binders := #[]
  let doc ← RequestM.readDoc
  for stx in snap.stx.topDown do
    let some stxRange := stx.getRange? | continue
    let lspRange := doc.meta.text.utf8RangeToLspRange stxRange
    unless lspRange.start ≤ params.range.end do continue
    unless params.range.start ≤ lspRange.end do continue
    if stx.isOfKind ``explicitBinder then
      -- This code action does not support explicit binders with optional values
      unless stx[3]!.isNone do continue
      let newStx := stx.modifyArg 0 (fun lparen => .atom lparen.getHeadInfo "{")
      let newStx := newStx.modifyArg 4 (fun rparen => .atom rparen.getHeadInfo "}")
      binders := binders.push ("implicit", newStx, lspRange)
    if stx.isOfKind ``implicitBinder then
      let newStx := stx.modifyArg 0 (fun lparen => .atom lparen.getHeadInfo "(")
      let newStx := newStx.modifyArg 3 (fun rparen => .atom rparen.getHeadInfo ")")
      binders := binders.push ("explicit", newStx, lspRange)

  let mut codeActions := #[]
  for (kind, stx, range) in binders do
    let some newText := stx.unsetTrailing.reprint | continue
    let edit : TextEdit := { range, newText }
    let title := s!"Make {kind}: {newText}"
    codeActions := codeActions.push {
      eager.title := title
      eager.kind? := "refactor.rewrite"
      eager.edit? := some <| .ofTextEdit doc.versionedIdentifier edit
    }
  return codeActions
