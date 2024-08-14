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
/-! doc-module -/
```
It emits a warning if a file does not have a doc-module string right after the `import`s.
-/

open Lean Elab

namespace Mathlib.Linter

/--
The "DocModule" linter checks that a file starts with
```
import*
/-! doc-module -/
```
It emits a warning if a file does not have a doc-module string right after the `import`s.
-/
register_option linter.docModule : Bool := {
  defValue := true
  descr := "enable the docModule linter"
}

/--
`undocumented` is the main vehicle to transfer information across syntax parsed by the linter.
It is initially set to `false` and it is reset to `false` at the end of the file.
After parsing *any* command, the linter sets `undocumented` to `true`.
This means that after any non-`import` command, `undocumented` is `true`.
Thus, from the linter's perspective, `undocumented` is `false` only when it reads the first
non-`import` command of each file.
If `undocumented` is `false` at the start of the linter parsing,
then the linter emits a warning, unless the parsed syntax is a doc-module string.
-/
initialize undocumented : IO.Ref Bool ← IO.mkRef false

namespace Style.DocModule

@[inherit_doc Mathlib.Linter.linter.docModule]
def docModuleLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.docModule (← getOptions) do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  let undoc? ← undocumented.get
  if Parser.isTerminalCommand stx then undocumented.set false
  unless ! undoc? do return
  if undoc? || !stx.isOfKind ``Lean.Parser.Command.moduleDoc then
    Linter.logLint linter.docModule stx
      m!"Add the doc-module string before this command\n\
        `{stx.getKind}` appears too late: it can only be preceded by `import` statements \
        doc-module strings and other `assert_not_exists` statements."
  undocumented.set true

initialize addLinter docModuleLinter

end Style.DocModule

end Mathlib.Linter
