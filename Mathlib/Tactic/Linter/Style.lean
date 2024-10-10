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

open Lean Elab Command

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

/-- The `check_declID` linter: if it emits a warning, then a declID is considered
non-standard style.  -/
register_option linter.style.check_declID : Bool := {
  defValue := false
  descr := "enable the `setOption` linter"
}


namespace Style.checkDeclID

/-- Checks whether a given identifier name contains "__". -/
def contains_double_underscore (stx : Syntax) : Bool :=
  1 < ((stx.getSubstring?.get!).toString.splitOn "__").length

/-- The `checkDeclID` linter: if this linter emits a warning, then a declID is considered
non-standard style. Currently we only check if it contains a double underscore ("__") as a
substring.

**Why is this bad?** Double underscores in theorem names can be considered non-standard style and
probably have been introduced by accident
**How to fix this?** Use single underscores to separate parts of a name, following standard naming
conventions.
-/
def checkDeclIDLinter: Linter where
  run := withSetOptionIn fun _stx => do
    unless Linter.getLinterValue linter.style.check_declID (← getOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    for stx in (Mathlib.Linter.getIds _stx) do
      if (contains_double_underscore stx) then
        Linter.logLint linter.style.check_declID stx
          m!"The declID '{stx}' contains '__', which does not follow naming conventions. \
              Consider using single underscores instead."
      else
        continue

initialize addLinter checkDeclIDLinter

end Style.checkDeclID

end Mathlib.Linter
