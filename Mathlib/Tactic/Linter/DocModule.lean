/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Elab.Command
import Lean.Linter.Util

/-!
The "DocModule" style linter checks that a file starts with
```
import*
/-! Module docstring -/
```
It emits a warning if a file does not have a module doc-string right after its `import` statements.
-/

open Lean Elab

namespace Mathlib.Linter

/--
The "DocModule" linter checks that a file starts with
```
import*
/-! Module docstring -/
```
It emits a warning if a file does not have a module docstring string right after the `import`s.
-/
register_option linter.docModule : Bool := {
  defValue := true
  descr := "enable the docModule linter"
}

namespace Style.DocModule

@[inherit_doc Mathlib.Linter.linter.docModule]
def docModuleLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.docModule (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return
  -- `test` files are not required to have a module doc-string.
  if (← getMainModule).getRoot == `test then return
  -- if we reached the end of the file, we reset to false the `undocumented` counter and
  -- report nothing: thus, `import`-only files do not get flagged by the linter
  if Parser.isTerminalCommand stx then
    if !stx.isOfKind ``Lean.Parser.Command.moduleDoc then
      Linter.logLint linter.docModule stx
        m!"`Mathlib` files must contain a module doc-string before their first non-`import` \
          command.\nPlease add the module doc-string before this command."

initialize addLinter docModuleLinter

end Style.DocModule

end Mathlib.Linter
