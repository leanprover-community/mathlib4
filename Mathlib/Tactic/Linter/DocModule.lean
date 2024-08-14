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
  if (← get).messages.hasErrors then
    return
  -- `test` files are not required to have a doc-module string
  if let `test::_ := (← getMainModule).components then return
  let undoc? ← undocumented.get
  -- `terminal?` is `true` iff `stx` is the end of the file, or
  -- (unreachable by the linter) `import X`
  let terminal? := Parser.isTerminalCommand stx
  -- if we reached the end of the file, we reset to false the `undocumented` counter and
  -- report nothing: thus, `import`-only files do not get flagged by the linter
  if terminal? then
    undocumented.set false
    return
  unless ! undoc? do return
  if !stx.isOfKind ``Lean.Parser.Command.moduleDoc then
    Linter.logLint linter.docModule stx
      m!"Add the doc-module string before this command\n\
        `Mathlib` files must contain a doc-module string before their first non-`import` command."
  undocumented.set true

initialize addLinter docModuleLinter

end Style.DocModule

end Mathlib.Linter
