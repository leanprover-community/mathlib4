/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Lean.Elab.Command
import Mathlib.Tactic.Linter.Common

/-!
## Style linters

This file contains (currently one, eventually more) linters about stylistic aspects:
these are only about coding style, but do not affect correctness nor global coherence of mathlib.

Historically, some of these were ported from the `lint-style.py` Python script.
-/

open Lean Parser Elab Command Meta

namespace Mathlib.Linter

/-- The `setOption` linter emits a warning on a `set_option` command, term or tactic
which sets a `pp`, `profiler` or `trace` option. -/
register_option linter.style.setOption : Bool := {
  defValue := false
  descr := "enable the `setOption` linter"
}

namespace Style.setOption

/-- Whether a syntax element is a `set_option` command, tactic or term:
Return the name of the option being set, if any. -/
def parse_set_option : Syntax → Option Name
  -- This handles all four possibilities of `_val`: a string, number, `true` and `false`.
  | `(command|set_option $name:ident $_val) => some name.getId
  | `(set_option $name:ident $_val in $_x) => some name.getId
  | `(tactic|set_option $name:ident $_val in $_x) => some name.getId
  | _ => none

/-- Whether a given piece of syntax is a `set_option` command, tactic or term. -/
def is_set_option : Syntax → Bool :=
  fun stx ↦ parse_set_option stx matches some _name

/-- The `setOption` linter: this lints any `set_option` command, term or tactic
which sets a `pp`, `profiler` or `trace` option.

**Why is this bad?** These options are good for debugging, but should not be
used in production code.
**How to fix this?** Remove these options: usually, they are not necessary for production code.
(Some tests will intentionally use one of these options; in this case, simply allow the linter.)
-/
def setOptionLinter : Linter where run := withSetOptionIn fun stx => do
    unless Linter.getLinterValue linter.style.setOption (← getOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    if let some head := stx.find? is_set_option then
      if let some name := parse_set_option head then
        let forbidden := [`debug, `pp, `profiler, `trace]
        if forbidden.contains name.getRoot then
          Linter.logLint linter.style.setOption head
            m!"Setting options starting with '{"', '".intercalate (forbidden.map (·.toString))}' \
               is only intended for development and not for final code. \
               If you intend to submit this contribution to the Mathlib project, \
               please remove 'set_option {name}'."

initialize addLinter setOptionLinter

end Style.setOption

/-- The `nameCheck` linter emits a warning on declarations whose name is non-standard style.
(Currently, this only includes declarations whose name includes a double underscore.)

**Why is this bad?** Double underscores in theorem names can be considered non-standard style and
probably have been introduced by accident.
**How to fix this?** Use single underscores to separate parts of a name, following standard naming
conventions.
-/
register_option linter.style.nameCheck : Bool := {
  defValue := false
  descr := "enable the `nameCheck` linter"
}

namespace Style.nameCheck

/-- Checks whether the original input of a given syntax contains "__". -/
def contains_double_underscore (stx : Syntax) : Bool :=
  match stx.getSubstring? with
  | some str => 1 < (str.toString.splitOn "__").length
  | none => false

@[inherit_doc linter.style.nameCheck]
def doubleUnderscore: Linter where run := withSetOptionIn fun stx => do
    unless Linter.getLinterValue linter.style.nameCheck (← getOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    for name in (← getNames stx) do
      if contains_double_underscore name then
        Linter.logLint linter.style.nameCheck name
          m!"The declaration '{name}' contains '__', which does not follow the mathlib naming \
             conventions. Consider using single underscores instead."

initialize addLinter doubleUnderscore

end Style.nameCheck

end Mathlib.Linter
