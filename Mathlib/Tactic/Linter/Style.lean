/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Lean.Elab.Command
import Lean.Linter.Util

/-!
## Style linters

Ported from the `lint-style.py` script.
-/

open Lean Elab Command

namespace Mathlib.Linter.Style

/-- Whether a syntax element is a `set_option` call:
Return the name of the option being set, if any. -/
def parse_set_option : Syntax → Option (Ident)
  -- TODO: output "name" instead! optional: validate value!
  -- TODO how to escape set_option
  --| `(set_optionS $name:ident) => some ("profiler.42")
  --| `(set_optionS $name:ident Sin) => some ("42") -- how to escape "in"
  --| `(command|set_option $name:ident true) => some name
  | `(command|set_option $name:ident $val) => some name
  -- test if true or false are handled here! if not, duplicate!!
  -- four cases; times three more!
  --| `(set_optionS $name:ident $_val:term Sin) => some ("42") -- escape in
  | _ => none

def is_set_option : Syntax → Bool :=
  fun stx ↦ match parse_set_option stx with
  | some _name => true
  | none => false

/-- The `setOption` linter emits a warning on a `set_option ...`. -/
register_option linter.setOption : Bool := {
  defValue := true
  descr := "enable the `setOption` linter"
}

/-- Gets the value of the `linter.setOption` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.setOption o

def setOptionLinter : Linter where
  run := withSetOptionIn fun stx => do
    unless getLinterHash (← getOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    match stx.findStack? (fun _ ↦ true) is_set_option with
    | some ((head, _n)::_chain) =>
      match parse_set_option head with
      | some (name) =>
        if name.startsWith "pp." || name.startsWith "profiler." || name.startsWith "trace." then
          Linter.logLint linter.setOption head m!"Forbidden set_option {name}; please remove"
      | _ => return
    | _ => return

initialize addLinter setOptionLinter

def parse_import : Syntax → Option (String)
  | `(import $name:ident) => some ("profiler.42")
  | _ => none

def is_import : Syntax → Bool :=
  fun stx ↦ match parse_import stx with
  | some _name => true
  | none => false

/-- The `broadImport` linter emits a warning on broad import, like
  `import Mathlib.Tactic` in a mathlib file. -/
register_option linter.broadImport : Bool := {
  defValue := true
  descr := "enable the `broadImport` linter"
}

/-- Gets the value of the `linter.broadImport` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.broadImport o


end Mathlib.Linter.Style
