/-
Copyright (c) 2026 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:  David Thrane Christiansen, Michael Rothgang
-/
module

public meta import Lean.DocString
public meta import Lean.Elab.DocString
public meta import Lean.Elab.Term.TermElabM
import Lean.Elab -- only needed for Parser.inline below
import all Init.Prelude -- doc-string for Nat, as an example

/-! # Verso docs role to include one docstring in another

Prototype quality code: needs more polish, and possibly more work on verso to make nice!
-/

open Lean Doc Elab Command

public section

-- TODO: this is an early hacky version, just to test how well things work now
open Doc in
/-- Writing `{insertDocstringOf foo}` inside a verso doc-string inserts the doc-string of
declaration `foo` in the current environment, as a separate paragraph.
If `foo` does not exist or has no doc-string, it throws an error.
-/
@[doc_command] meta def _root_.insertDocstringOf (n : Ident) :
    DocM <| Block ElabInline ElabBlock := do
  let doc ← realizeGlobalConstNoOverloadWithInfo n
  let some docStr ← findDocString? (← getEnv) doc
    | throwError "No doc-string for `{.ofConstName doc}`"
  -- Future: once there is a better auto-converter between markdown and verso doc-strings,
  -- rewrite this code accordingly!
  -- Perhaps, it could be nice to write .verso here.
  return .para #[.text docStr]

/- bad copy-paste from
https://github.com/leanprover/lean4/blob/master/tests/elab/versoDocCustomRenderer.lean
something's not working... -/
--open scoped Lean.Doc.Syntax

/-- A request to include another declaration's docstring. -/
meta structure IncludeDoc where
  /-- The declaration whose docstring should be included. -/
  target : Name
deriving TypeName

/-- Reads a single code inline and resolves it to a global constant. -/
meta def codeTargetName (xs : TSyntaxArray ``Parser.inline) : DocM Name :=
  match xs with
  -- "unknown identifier InlineView.of"...
  -- | #[stx] => match InlineView.of stx with
  --   | some (.code { content, .. }) =>
  --     realizeGlobalConstNoOverloadWithInfo (mkIdentFrom content content.getVersoCode.toName)
  --   | _ => throwErrorAt stx "expected a code argument"
  | _ => throwError "expected one code argument"

/-
/-- Includes another declaration's docstring. The target is looked up when rendering to Markdown. -/
-- @[doc_role] doesn't work yet
meta def include_docstring (xs : TSyntaxArray `Lean.Doc.Parser.inline) :
    DocM (Inline ElabInline) := do
  sorry -- return .other { val := .mk (IncludeDoc.mk (← codeTargetName xs)) } #[]

/-- The renderer receives the decoded `IncludeDoc` directly, never a `Dynamic`. -/
@[doc_inline_md]
meta def includeRender : InlineMdRendererOf IncludeDoc := fun _go data _content => do
  match (← (findInternalDocString? (← (getEnv : CoreM _)) data.target : IO _)) with
  | some (.inl str) => return ((str.split '\n').map (·.copy)).toArray
  | some (.inr verso) => ToMarkdown.toMarkdown verso
  | none => return #[]

-- set_option doc.verso true in will fail because the existing code fails
/-- {include_docstring}`Nat` -/
def Bar : Nat := 1
-/

-- This kind of works.
set_option doc.verso true in
/-- {insertDocstringOf Nat} -/
def foo : Nat := 1
