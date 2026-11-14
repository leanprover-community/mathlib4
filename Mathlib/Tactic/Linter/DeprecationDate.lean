/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public meta import Lean.Elab.Command
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public meta import Mathlib.Tactic.Linter.Header  -- shake: keep
public meta import Std.Time.Format

/-!
# The "deprecationDate" linter

Checks that the `(since := ...)` field of the `@[deprecated]` and `@[deprecated_arg]` attributes
and of the `deprecated_module` and `deprecated_syntax` commands is a date of the form `YYYY-MM-DD`.

Lean core accepts an arbitrary string in this field, but in mathlib we always use dates of the
form `YYYY-MM-DD`. `#clear_deprecations` (see `Mathlib/Tactic/Linter/FindDeprecations.lean`)
compares the `since` field against a date range as a string, so a malformed date would cause
unintended behaviour.
-/

meta section

open Lean Elab Command Linter

namespace Mathlib.Linter

/--
The "deprecationDate" linter checks that the `(since := ...)` field of a deprecation is a date of
the form `YYYY-MM-DD`.
-/
public register_option linter.style.deprecationDate : Bool := {
  defValue := true
  descr := "enable the deprecationDate linter"
}

namespace DeprecationDate

/-- The four deprecation syntax node kinds carrying a `(since := ...)` field. -/
def deprecationKinds : Array SyntaxNodeKind :=
  #[``Lean.deprecated, ``Lean.deprecated_arg, ``Lean.Parser.Command.deprecated_module,
    ``Lean.Parser.Command.deprecatedSyntax]

@[inherit_doc Mathlib.Linter.linter.style.deprecationDate]
def deprecationDateLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless getLinterValue linter.style.deprecationDate (← getLinterOptions) do
    return
  if (← get).messages.hasErrors then
    return
  for s in stx.topDown do
    unless deprecationKinds.contains s.getKind do continue
    let some sinceField := s.getArgs.find? (fun a =>
      a.isOfKind nullKind && a.getNumArgs == 5 && a[1].getAtomVal == "since") | continue
    let some date := sinceField[3].isStrLit? | continue
    unless (Std.Time.PlainDate.fromLeanDateString date).isOk do
      Linter.logLint linter.style.deprecationDate sinceField[3]
        m!"'{date}' is not a valid date; `(since := ...)` must have the form `YYYY-MM-DD`."

initialize addLinter deprecationDateLinter

end DeprecationDate

end Mathlib.Linter
