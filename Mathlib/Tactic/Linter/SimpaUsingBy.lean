/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public meta import Lean.Elab.Command
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public meta import Mathlib.Tactic.Linter.Header  -- shake: keep
public import Lean.Message

/-!
# Linter against `simpa [...] using by tactic`

The `simpaUsingBy` linter flags any invocation of the form `simpa ... using by tactic`.

This is rather misleading since `by tactic` is always elaborated at the very last so this
is effectively equivalent to `simp; tactic`, and it has the potential to sneak non-terminal simps
past the flexible linter.

-/

meta section

open Lean Elab Command Linter

namespace Mathlib.Linter

/-- Lint on any occurrence of `simpa ... using by tactic`.
This is a hack to bypass flexible linters. -/
public register_option linter.simpaUsingBy : Bool :=
  { defValue := true
    descr := "enable the simpaUsingBy linter" }

namespace simpaUsingByLinter

/-- Gets the value of the `linter.simpaUsingBy` option. -/
def getLinterSimpaUsingBy (o : LinterOptions) : Bool :=
  getLinterValue linter.simpaUsingBy o

def isSimpaUsingBy : Syntax → Bool
  | `(tactic| simpa $[?]? $[!]? $_:optConfig $(_)? $[only]? $[[$args,*]]? using by $_) => true
  | `(tactic| simpa! $_:optConfig $(_)? $[only]? $[[$args,*]]? using by $_) => true
  | _ => false


/--
The `simpaUsingBy` linter flags any invocation of the form `simpa ... using by tactic`.

This is rather misleading since `by tactic` is always elaborated at the very last so this
is effectively equivalent to `simp; tactic`, and it has the potential to sneak non-terminal simps
past the flexible linter.
-/
def simpaUsingBy : Linter where run := withSetOptionIn fun stx => do
  unless getLinterSimpaUsingBy (← getLinterOptions) do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  for s in stx.topDown do
    if isSimpaUsingBy s then
      Linter.logLint linter.simpaUsingBy s m!
"`simpa ... using by tactic` is a convoluted way to write `simp; tactic`
that potentially by-passes the flexible linter. Please change this to `simp; tactic`,
and adjust accordingly if this is flagged by the flexible linter."

initialize addLinter simpaUsingBy

end simpaUsingByLinter

end Mathlib.Linter
