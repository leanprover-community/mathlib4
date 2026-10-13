/-
Copyright (c) 2025 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public meta import Lean.DocString
public meta import Lean.Elab.Tactic.Doc
public meta import Lean.Parser.Tactic.Doc
public import Batteries.Tactic.Lint.Basic
public import Lean.Elab.Tactic.Doc
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public import Mathlib.Tactic.Linter.Header  -- shake: keep

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

    if (← findDocString? env tac).isSome || (getTacticExtensions env tac).any (! ·.isEmpty) then
      return none

    let name := (← firstTacticTokens).getD tac tac.toString
    return m!"tactic `{name}` missing documentation string"

/-- Check tactics with the same user-facing name (usually: first syntax token) get a `@[tactic_alt]`
attribute. -/
@[env_linter] public meta def tacticAlt : Batteries.Tactic.Lint.Linter where
  noErrorsFound := "No tactics sharing the same user-facing name."
  errorsFound := "TACTICS ARE MISSING `@[tactic_alt]` ATTRIBUTES:"
  test tac := do
    let env ← getEnv
    if !isTactic env tac || (alternativeOfTactic env tac).isSome then
      return none
    -- Find duplicates, those with the same user-facing name but that aren't declared
    -- to be alternatives.
    let some tactics := (Lean.Parser.parserExtension.getState env).categories.find? `tactic
      | return none
    let names ← firstTacticTokens
    let name := names.getD tac tac.toString
    let tacNames := tactics.kinds.foldl (init := #[]) fun acc other _ =>
      if names.getD other other.toString == name && (alternativeOfTactic env other).isNone then
        acc.push other
      else acc
    -- If we have duplicates, complain.
    if tacNames.size <= 1 then return none
    return m!"tactic `{name}` has multiple declarations {tacNames} one of which should \
    be marked as `@[tactic_alt]` of the other(s).\n\
    Hint: you can use the `tactic_extension` command to extend the documentation."
