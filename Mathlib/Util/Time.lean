/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Init
import Lean

/-!
# Defines `#time` command.

Time the elaboration of a command, and print the result (in milliseconds).
-/

section
open Lean Elab Command

syntax (name := timeCmd) "#time " command : command

/--
Time the elaboration of a command, and print the result (in milliseconds).

Example usage:
```
set_option maxRecDepth 100000 in
#time example : (List.range 500).length = 500 := rfl
```
-/
@[command_elab timeCmd] def timeCmdElab : CommandElab
  | `(#time%$tk $stx:command) => do
    let start ← IO.monoMsNow
    elabCommand stx
    logInfoAt tk m!"time: {(← IO.monoMsNow) - start}ms"
  | _ => throwUnsupportedSyntax

end
