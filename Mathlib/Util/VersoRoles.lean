/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
module

public meta import Lean.Elab.DocString
public meta import Batteries.Util.LibraryNote
import Mathlib.Tactic.Linter.Header -- Since this file is imported by `Mathlib.Init`.

set_option doc.verso true

/-!
# Verso docstring roles for migration

This module provides custom Verso docstring roles and code blocks used while migrating Mathlib
docstrings to Verso syntax:

* {lit}`{url}` turns a code literal containing a URL into a link.
* {lit}`{library_note}` references a library note and checks that it exists.
* {lit}`{cite}` references a bibliography entry and renders custom text for it.
* The {lit}`code` code block records a language for a verbatim code listing.

The roles are declared in the root namespace so that they are available in every docstring without
opening a namespace.
-/

open Lean Lean.Doc
open scoped Lean.Doc.Syntax

public meta section

namespace Mathlib.Migration

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
  let mut codes : Array StrLit := #[]
  for stx in xs do
    match stx with
    | `(inline|code($s)) => codes := codes.push s
    | `(inline|$s:str) =>
      unless s.getString.all (·.isWhitespace) do throwErrorAt stx "Expected a code element"
    | other => throwErrorAt other "Expected a code element"
  if h : codes.size = 1 then return codes[0]
  else throwError "Expected a single code element"

/-- The labels of all library notes available in the current environment. -/
def libraryNoteLabels (env : Environment) : Array String :=
  let imported := (Batteries.Util.LibraryNote.libraryNoteExt.toEnvExtension.getState env)
    |>.importedEntries.flatten
  let local_ := Batteries.Util.LibraryNote.libraryNoteExt.getEntries env
  (imported ++ local_).map fun (n : Name) => n.toString (escape := false)

/-- Whether {lit}`docs/references.bib` contains an entry with the given key. -/
def bibContainsKey (bib : String) (key : String) : Bool := Id.run do
  for line in bib.splitOn "\n" do
    let line := line.trimAscii.copy
    if line.startsWith "@" then
      match line.splitOn "{" with
      | _ :: rest :: _ =>
        if (rest.takeWhile (· != ',')).trimAscii.copy == key then return true
      | _ => pure ()
  return false

end Mathlib.Migration

/--
A link to a URL.

The code literal contains the target, which is also used as the link text, as
in {lit}`` {url}`https://leanprover.org` ``.
-/
@[doc_role]
def url (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  let s ← Mathlib.Migration.soleCode xs
  let target := s.getString
  return .link #[.text target] target

/--
A reference to a library note.

The code literal contains the note's label, as
in {lit}`` {library_note}`partially-applied ext lemmas` ``.
A warning is reported when no library note with this label is in scope, so that references to notes
defined later are allowed.
-/
@[doc_role]
def «library_note» (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  let s ← Mathlib.Migration.soleCode xs
  let label := s.getString
  let labels := Mathlib.Migration.libraryNoteLabels (← getEnv)
  unless labels.contains label do
    logWarningAt s m!"No library note with label `{label}`."
  return .code label

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
    unless Mathlib.Migration.bibContainsKey bib k do
      logWarningAt key m!"No bibliography entry `{k}` in `docs/references.bib`."
  return .other
    (.custom (.mk (Mathlib.Migration.Citation.mk k)))
    rendered


/--
A verbatim code listing in the language named by the positional argument, as
in {lit}```` ```code python ````.

The language is recorded for later use; the listing itself is rendered verbatim.
-/
@[doc_code_block]
def code (language : Ident) (content : StrLit) : DocM (Block ElabInline ElabBlock) := do
  return .other
    (.custom (.mk (Mathlib.Migration.CodeWithLanguage.mk language.getId.toString)))
    #[.code content.getString]

end
