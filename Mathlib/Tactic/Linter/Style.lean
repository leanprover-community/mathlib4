/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Lean.Elab.Command

/-!
## Style linters

This file contains (currently one, eventually more) linters about stylistic aspects:
these are only about coding style, but do not affect correctness nor global coherence of mathlib.

Historically, these were ported from the `lint-style.py` Python script.
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
If true, return the syntax for the option name and the value of the option being set.
-/
def parse_set_option : Syntax → Option (Syntax × TSyntax [`str, `num])
  -- This handles all four possibilities of `val`: a string, number, `true` and `false`.
  | `(command|set_option $name:ident $val) => some (name, val)
  | `(set_option $name:ident $val in $_x) => some (name, val)
  | `(tactic|set_option $name:ident $val in $_x) => some (name, val)
  | _ => none


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
    if let some (opt, val) := parse_set_option stx then
      let name := opt.getId
      if name == `autoImplicit && val.raw matches .atom _ "true" then
        -- We do not lint mathlib's test directory (but do lint this linter's test).
        let mod := ← getMainModule
        if mod.getRoot == `test && mod != `test.LintStyle then
          return
        Linter.logLint linter.style.setOption opt
          m!"Using `autoImplicit true` is deprecated in mathlib: \
          please try to rewrite your code to avoid it. \n\
          (If using this option makes the code much better and you conciously prefer to \
          use autoImplicit,\nplease add a comment why you are disabling this linter.)"
      let forbidden := [`debug, `pp, `profiler, `trace]
      if forbidden.contains name.getRoot then
        Linter.logLint linter.style.setOption opt
          m!"Setting options starting with '{"', '".intercalate (forbidden.map (·.toString))}' \
             is only intended for development and not for final code. \
             If you intend to submit this contribution to the Mathlib project, \
             please remove 'set_option {name}'."

initialize addLinter setOptionLinter

end Style.setOption

end Mathlib.Linter
