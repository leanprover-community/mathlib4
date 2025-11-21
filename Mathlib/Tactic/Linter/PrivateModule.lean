/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public meta import Lean.Elab.Command
public import Lean.Linter.Basic
public import Lean.Environment
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
import Mathlib.Tactic.Linter.Header

/-!
# Private module linter

This linter lints against nonempty modules that have only private declarations, and suggests adding
`@[expose] public section` to the top or selectively marking declarations as `public`.

## Implementation notes

`env.constants.map₂` contains all locally-defined constants, and accessing this waits until all
declarations are added. By linting (only) the `eoi` token, we can capture all constants defined in
the file.

Note that private declarations are exactly those which satisfy `isPrivateName`, whether private due
to an explicit `private` or due to not being made `public`.
-/

meta section

open Lean Elab Command Linter

namespace Mathlib.Linter

/-- The `privateModule` linter lints against nonempty modules that have only private declarations,
and suggests adding `@[expose] public section` or selectively marking declarations as `public`. -/
public register_option linter.privateModule : Bool := {
  defValue := false
  descr := "Enable the `privateModule` linter, which lints against nonempty modules that have only \
    private declarations."
}

/--
The `privateModule` linter lints against nonempty modules that have only private declarations,
and suggests adding `@[expose] public section` to the top.

This linter only acts on the end-of-input `Parser.Command.eoi` token, and ignores all other syntax.
It logs its message at the top of the file.
-/
def privateModule : Linter where run stx := do
  if stx.isOfKind ``Parser.Command.eoi then
    unless getLinterValue linter.privateModule (← getLinterOptions) do
      return
    if (← getEnv).header.isModule then
      -- Don't lint an imports-only module:
      if !(← getEnv).constants.map₂.isEmpty then
        -- Exit if any declaration is public:
        for (decl, _) in (← getEnv).constants.map₂ do
          if !isPrivateName decl then return
        -- Lint if all names are private:
        let topOfFileRef := Syntax.atom (.synthetic ⟨0⟩ ⟨0⟩) ""
        logLint linter.privateModule topOfFileRef
          "The current module only contains private declarations.\n\n\
          Consider adding `@[expose] public section` at the beginning of the module, \
          or selectively marking declarations as `public`."

initialize addLinter privateModule

end Mathlib.Linter
