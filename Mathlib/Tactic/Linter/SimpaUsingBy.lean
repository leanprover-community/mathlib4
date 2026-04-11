/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public meta import Mathlib.Lean.Linter

/-!
# Linter against `simpa [...] using by tactic`

The `simpaUsingBy` linter flags any invocation of the form `simpa ... using by tactic`.

This is rather misleading since `by tactic` is always elaborated at the very last so this
is effectively equivalent to `simp; tactic`, and it has the potential to sneak non-terminal simps
past the flexible linter.

-/

meta section

open Lean Elab Command Linter

namespace Mathlib.Linter.Style

/--
The `simpaUsingBy` linter flags any invocation of the form `simpa ... using by tactic`.

Since `by tactic` is always elaborated at the very last, this is effectively equivalent to
`simp; tactic`. `simpa ... using by tactic` not only makes the intent less clear, and has a
potential to sneak non-terminal simps past the flexible linter. -/
public register_option linter.style.simpaUsingBy : Bool :=
  { defValue := true
    descr := "enable the simpaUsingBy linter" }

namespace simpaUsingByLinter

/-- Parse a syntax to check for `simpa ... using by tactic` syntaxes,
and returns `tactic` if it finds one. -/
def getSimpaUsingByTactic? : Syntax → Option Syntax
  | `(tactic| simpa $[?]? $[!]? $_:optConfig $(_)? $[only]? $[[$_,*]]? using by $tac) => return tac
  | `(tactic| simpa! $_:optConfig $(_)? $[only]? $[[$_,*]]? using by $tac) => return tac
  | _ => failure

@[inherit_doc linter.style.simpaUsingBy]
def simpaUsingBy : Linter where run := whenLinterActivated linter.style.simpaUsingBy fun stx ↦ do
  for s in stx.topDown do
    if let .some tac := getSimpaUsingByTactic? s then
      let tacMsg := toMessageData tac
      let tacStr := if (← tacMsg.toString).length > 20 then tacMsg else "tactic"
      Linter.logLint linter.style.simpaUsingBy s m!
"`simpa ... using by tactic` is a convoluted way to write `simp; tactic`
that potentially by-passes the flexible linter. Please change this to `simp; {tacStr}`,
and adjust accordingly if this is flagged by the flexible linter."

initialize addLinter simpaUsingBy

end simpaUsingByLinter

end Mathlib.Linter.Style
