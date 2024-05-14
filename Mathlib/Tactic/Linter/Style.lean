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
def parse_set_option : Syntax → Option (String)
  -- TODO: output "name" instead! optional: validate value!
  | `(set_optionS $name:ident) => some ("profiler.42")
  | `(set_optionS $name:ident Sin) => some ("42") -- how to escape "in"
  | `(set_optionS $name:ident $_val:term) => some ("!")
  | `(set_optionS $name:ident $_val:term Sin) => some ("42") -- escape in
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

end Mathlib.Linter.Style
