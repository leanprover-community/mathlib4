/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Elab.Command
import Lean.Linter.Util

/-!
#  The "docPrime" linter

The "docPrime" linter emits a warning on declarations that have no doc-string and whose
name contains a `'`.
-/

open Lean Elab

namespace Mathlib.Linter

/--
The "docPrime" linter emits a warning on declarations that have no doc-string and whose
name contains a `'`.
-/
register_option linter.docPrime : Bool := {
  defValue := false
  descr := "enable the docPrime linter"
}

namespace DocPrime

@[inherit_doc Mathlib.Linter.linter.docPrime]
def docPrimeLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.docPrime (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return
  unless [``Lean.Parser.Command.declaration, `lemma].contains stx.getKind  do return
  let docstring := stx[0][0]
  let declId :=
    if stx[1].isOfKind ``Lean.Parser.Command.instance then
      stx[1][3][0]
    else
      stx[1][1]
  if docstring[0][1].getAtomVal.isEmpty && declId[0].getId.toString.contains '\'' then
    Linter.logLint linter.docPrime declId
      m!"`{declId}` is missing doc-string, please add one.\n\
        Declarations whose name contains a `'` are expected to contain a justification for the \
        presence of a `'` in their doc-string."

initialize addLinter docPrimeLinter

end DocPrime

end Mathlib.Linter
