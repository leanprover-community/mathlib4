/-
Copyright (c) 2026 Fernando Leal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Leal
-/
module

public meta import Lean
public import Mathlib

public meta section
open Lean Meta Server Lsp

open Lean.Parser.Term in
@[code_action_provider]
def binderPlicity : CodeActionProvider := fun params snap => do
  /- TODO: Options for finding things in syntax -/
  let mut binders := #[]
  let doc ← RequestM.readDoc
  for stx in snap.stx.topDown do
    let some stxRange := stx.getRange? | continue
    let lspRange := doc.meta.text.utf8RangeToLspRange stxRange
    unless lspRange.start.line ≤ params.range.end.line do continue
    unless params.range.start.line ≤ lspRange.end.line do continue
    if stx.isOfKind ``explicitBinder then
      -- This code action does not support explicit binders with optional values
      unless stx[3]!.isNone do continue
      let newStx := stx.modifyArg 0 (fun lparen => .atom lparen.getHeadInfo "{")
      let newStx := newStx.modifyArg 4 (fun rparen => .atom rparen.getHeadInfo "}")
      binders := binders.push (BinderInfo.default, newStx, lspRange)
    if stx.isOfKind ``implicitBinder then
      let newStx := stx.modifyArg 0 (fun lparen => .atom lparen.getHeadInfo "(")
      let newStx := newStx.modifyArg 3 (fun rparen => .atom rparen.getHeadInfo ")")
      binders := binders.push (BinderInfo.implicit, newStx, lspRange)

  let mut codeActions := #[]
  for (bi, stx, range) in binders do
    let some s := stx.unsetTrailing.reprint | continue
    let edit : TextEdit := { range, newText := s }
    let title? := match bi with 
      | .default => some s!"Make explicit: {s}"
      | .implicit => some s!"Make implicit: {s}"
      | _ => none -- TODO: This is currently unreachable
    let some title := title? | continue -- TODO: I can't do `continue` inside the match :/
    codeActions := codeActions.push {
      eager.title := title
      eager.kind? := "refactor.rewrite"
      eager.edit? := some <| .ofTextEdit doc.versionedIdentifier edit
    }
  return codeActions
