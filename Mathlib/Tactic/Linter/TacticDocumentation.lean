/-
Copyright (c) 2025 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public meta import Lean.Elab.Tactic.Doc
public meta import Lean.Parser.Tactic.Doc
public import Mathlib.Tactic.Linter.Header  -- shake: keep
public import Batteries.Tactic.Lint.Basic
public import Lean.Elab.Tactic.Doc

/-! # The `tacticDocs` linter

The `tacticDocs` environment linter checks that all tactics defined in a module come with
a (nonempty) docstring.
-/

open Lean Parser Elab Command

open Tactic.Doc

/-- Does this tactic have a docstring, or an `extensionDoc` defined later? -/
meta def isNonemptyDoc (doc : TacticDoc) : Bool :=
  doc.docString.isSome || doc.extensionDocs.any (! ·.isEmpty)

/-- Check that all tactics available in Mathlib have a docstring. -/
@[env_linter] public meta def tacticDocs : Batteries.Tactic.Lint.Linter where
  noErrorsFound := "No tactics are missing documentation."
  errorsFound := "TACTICS ARE MISSING DOCUMENTATION STRINGS:"
  test tac := do
    let env ← getEnv

    -- Only run on unique tactics (where tactics are defined as parsers in the tactic kind).
    if !isTactic env tac || (alternativeOfTactic env tac).isSome then
      return none

    -- Find the associated documentation.
    let docs ← Tactic.Doc.allTacticDocs
    let docMap : NameMap _ := docs.foldl (init := {}) fun m doc =>
      m.insert doc.internalName doc
    -- This `get?` should not return `none` for normally declared tactics,
    -- but if we do environment manipulation it might give us weird results.
    -- So we should allow the case of `none`.
    let doc := docMap.get? tac
    let name := (doc.map (·.userName)).getD tac.toString

    if let some doc := doc then
      if isNonemptyDoc doc then
        return none

    return m!"tactic `{name}` missing documentation string"
