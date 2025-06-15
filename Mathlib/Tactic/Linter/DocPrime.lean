/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Elab.Command
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
import Mathlib.Tactic.Linter.Header

/-!
# The "docPrime" linter

The "docPrime" linter emits a warning on declarations that have no doc-string and whose
name ends with a `'`. Such declarations are expected to have a documented explanation
for the presence of a `'` in their name. This may consist of discussion of the difference relative
to an unprimed version of that declaration, or an explanation as to why no better naming scheme
is possible.
-/

open Lean Elab Linter

namespace Mathlib.Linter

/--
The "docPrime" linter emits a warning on declarations that have no doc-string and whose
name ends with a `'`.

The file `scripts/nolints_prime_decls.txt` contains a list of temporary exceptions to this linter.
This list should not be appended to, and become emptied over time.
-/
register_option linter.docPrime : Bool := {
  defValue := false
  descr := "enable the docPrime linter"
}

namespace DocPrime

@[inherit_doc Mathlib.Linter.linter.docPrime]
def docPrimeLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless getLinterValue linter.docPrime (← getLinterOptions) do
    return
  if (← get).messages.hasErrors then
    return
  unless [``Lean.Parser.Command.declaration, `lemma].contains stx.getKind do return
  -- ignore private declarations
  if (stx.find? (·.isOfKind ``Lean.Parser.Command.private)).isSome then return
  -- ignore examples
  if (stx.find? (·.isOfKind ``Lean.Parser.Command.example)).isSome then return
  let docstring := stx[0][0]
  -- The current declaration's id, possibly followed by a list of universe names.
  let declId :=
    if stx[1].isOfKind ``Lean.Parser.Command.instance then
      stx[1][3][0]
    else
      stx[1][1]
  if let .missing := declId then return
  -- The name of the current declaration, with namespaces resolved.
  let declName : Name :=
    if let `_root_ :: rest := declId[0].getId.components then
      rest.foldl (· ++ ·) default
    else (← getCurrNamespace) ++ declId[0].getId
  let msg := m!"`{declName}` is missing a doc-string, please add one.\n\
      Declarations whose name ends with a `'` are expected to contain an explanation for the \
      presence of a `'` in their doc-string. This may consist of discussion of the difference \
      relative to the unprimed version, or an explanation as to why no better naming scheme \
      is possible."
  if docstring[0][1].getAtomVal.isEmpty && declName.toString.back == '\'' then
    if ← System.FilePath.pathExists "scripts/nolints_prime_decls.txt" then
      if (← IO.FS.lines "scripts/nolints_prime_decls.txt").contains declName.toString then
        return
      else
        Linter.logLint linter.docPrime declId msg
    else
      Linter.logLint linter.docPrime declId msg

initialize addLinter docPrimeLinter

end DocPrime

end Mathlib.Linter
