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
-/

-- TODO: `module` is not enabled in MathlibTest yet, so tests should be written for this once it is.

meta section

open Lean Elab Command Linter

/-- The `privateModule` linter lints against nonempty modules that have only private declarations,
and suggests adding `@[expose] public section` to the top. -/
register_option linter.privateModule : Bool := {
  defValue := true
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
        -- TODO: why doesn't this work?
        -- if (← getEnv).asyncConstsMap.public.size = 0 then
        --   if (← getEnv).asyncConstsMap.private.size ≠ 0 then
        unless (← getEnv).asyncConstsMap.public.revList.any
            (!(`_private).isPrefixOf ·.constInfo.name) do
          if (← getEnv).asyncConstsMap.private.size ≠ 0 then
            let topOfFileRef := Syntax.atom (.synthetic ⟨0⟩ ⟨0⟩) ""
            logLint linter.privateModule topOfFileRef
              "Module only contains private declarations.\n\n\
              Consider adding `@[expose] public section` at the beginning of the module."

initialize addLinter privateModule
