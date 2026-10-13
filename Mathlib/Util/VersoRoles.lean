/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
module

public meta import Lean.Elab.DocString
public meta import Batteries.Util.LibraryNote
public meta import Mathlib.Tactic.Linter.Style -- To silence `defsWithUnderscore` linter
import Mathlib.Tactic.Linter.Header -- Since this file is imported by `Mathlib.Init`.

set_option doc.verso true

/-!
# Verso docstring roles

This module provides custom Verso docstring roles and code blocks used to support Verso syntax
in Mathlib docstrings:

* {lit}`{url}` turns a code literal containing a URL into a link.
* {lit}`{library_note}` references a library note and checks that it exists.
* {lit}`{cite}` references a bibliography entry and renders custom text for it.
* The {lit}`code` code block records a verbatim code listing in the given language.

The roles are declared in the root namespace so that they are available in every docstring without
opening a namespace.
-/

open Lean Lean.Doc
open scoped Lean.Doc.Syntax

public meta section

namespace Mathlib.VersoRoles

/-- A reference to a bibliography entry in {lit}`docs/references.bib`. -/
structure Citation where
  /-- The citation key, as it appears in {lit}`docs/references.bib`. -/
  key : String
deriving TypeName, Repr

/-- A verbatim code listing together with the name of its language. -/
structure CodeWithLanguage where
  /-- The language of the code listing. -/
  language : String
deriving TypeName, Repr

/--
Extracts the single code literal from the contents of a role, such as the {lit}`` `x` ``
in {lit}`` {role}`x` ``.
-/
def soleCode (xs : TSyntaxArray `inline) : DocM StrLit := do
  if h : xs.size ≠ 1 then
    throwError "Expected a single code element"
  else
    match xs[0] with
    | `(inline|code($s)) => return s
    | other => throwErrorAt other "Expected a code element"

/-- Whether {name}`bib` (the contents of {lit}`docs/references.bib`) contains an entry with
the given key. -/
def bibContainsKey (bib : String) (key : String) : Bool := Id.run do
  for line in bib.splitOn "\n" do
    let line := line.trimAscii.copy
    if line.startsWith "@" then
      match line.splitOn "{" with
      | _ :: rest :: _ =>
        if (rest.takeWhile (· != ',')).trimAscii.copy == key then return true
      | _ => pure ()
  return false

end Mathlib.VersoRoles

/--
A link to a URL.

The code literal contains the target, which is also used as the link text, as
in {lit}`` {url}`https://leanprover.org` ``.
-/
@[doc_role]
def url (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  let s ← Mathlib.VersoRoles.soleCode xs
  let target := s.getString
  return .link #[.text target] target

/-- If {name}`doc.verso.libraryNote.warnOnMissing` is enabled, a {lit}`{library_note}`
reference that is not in scope generates a warning.
-/
register_option doc.verso.libraryNote.warnOnMissing : Bool := {
  defValue := true,
  descr := "whether to warn if a `{library_note}` reference cannot be resolved"
}

/--
A reference to a library note.

The code literal contains the note's label, as
in {lit}`` {library_note}`partially-applied ext lemmas` ``.
A warning is reported when no library note with this label is in scope, so that references to notes
defined later are allowed. Set the option {name}`doc.verso.libraryNote.warnOnMissing` to
{lean}`false` to disable this warning.
-/
@[doc_role, nolint defsWithUnderscore] -- This name intentionally contains an underscore.
def «library_note» (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  let s ← Mathlib.VersoRoles.soleCode xs
  let label := s.getString
  if ← doc.verso.libraryNote.warnOnMissing.getM then
    /- Note that `Batteries.Util.LibraryNote.libraryNoteExt` initializes its state by flattening
    all imported library notes into the state array. -/
    let labels := Batteries.Util.LibraryNote.libraryNoteExt.getState (← getEnv)
    if !labels.any (·.toString (escape := false) == label) then
      logWarningAt s m!"No library note with label `{label}`.{.note m!"This warning can be \
        disabled with `set_option {doc.verso.libraryNote.warnOnMissing.name} false`."}"
  return .code label

attribute [nolint defsWithUnderscore] «library_note».getArgs

/--
A reference to a bibliography entry.

The positional argument is the entry's key in {lit}`docs/references.bib`, and the bracketed content
is the text to render, as in {lit}`` {cite "Adamek_Rosicky_1994"}[Adámek–Rosický] ``. A warning is
emitted when the key is not found in {lit}`docs/references.bib`.
-/
@[doc_role]
def cite (key : StrLit) (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  let rendered ← xs.mapM elabInline
  let k := key.getString
  let path : System.FilePath := "docs" / "references.bib"
  if ← path.pathExists then
    let bib ← IO.FS.readFile path
    unless Mathlib.VersoRoles.bibContainsKey bib k do
      logWarningAt key m!"No bibliography entry `{k}` in `docs/references.bib`."
  return .other
    (.custom (.mk (Mathlib.VersoRoles.Citation.mk k)))
    rendered


/--
A verbatim code listing in the language named by the positional argument, as
in {lit}```` ```code python ````.

The language is recorded for later use; the listing itself is rendered verbatim.
-/
@[doc_code_block]
def code (language : Ident) (content : StrLit) : DocM (Block ElabInline ElabBlock) := do
  return .other
    (.custom (.mk (Mathlib.VersoRoles.CodeWithLanguage.mk language.getId.toString)))
    #[.code content.getString]

end
