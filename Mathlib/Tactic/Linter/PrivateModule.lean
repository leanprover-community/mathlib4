/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public import Mathlib.Init
public import Lean.Environment
import all Lean.Environment

/-!
# Private module linter

This linter lints against nonempty modules that have only private declarations, and suggests adding
`@[expose] public section` to the top.

## Implementation notes

All new declarations, whether added synchronously with `addDecl` or otherwise, get added to
`asyncConstsMap`.

`asyncConstsMap.public` and `asyncConstsMap.private` seem to contain exactly the same declarations.
The difference between public and private declarations is encoded via the presence of the name
prefix `_private` in the declaration's name. The code here should be robust to potential future
changes that put public declarations only in `.public` and private ones only in `.private`.
-/


meta section

open Lean Elab Command Linter

namespace Mathlib.Linter

/-- The `privateModule` linter lints against nonempty modules that have only private declarations,
and suggests adding `@[expose] public section` to the top. -/
public register_option linter.privateModule : Bool := {
  defValue := false
  descr := "Enable the `privateModule` linter, which lints against nonempty modules that have only \
    private declarations."
}

def privateModule : Linter where
  run stx := do
    if stx.isOfKind ``Parser.Command.eoi then
      unless getLinterValue linter.privateModule (← getLinterOptions) do
        return
      if (← getEnv).header.isModule then
        -- Wait for everything (necessary?)
        let _ := (← getEnv).checked.get
        unless (← getEnv).asyncConstsMap.public.revList.any
            (!(`_private).isPrefixOf ·.constInfo.name) do
          if (← getEnv).asyncConstsMap.private.size ≠ 0 then
            let topOfFileRef := Syntax.atom (.synthetic ⟨0⟩ ⟨0⟩) ""
            logLint linter.privateModule topOfFileRef
              "The current module only contains private declarations.\n\n\
              Consider adding `@[expose] public section` at the beginning of the module."

initialize addLinter privateModule

end Mathlib.Linter
