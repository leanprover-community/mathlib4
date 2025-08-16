/-
Copyright (c) 2025 ChatGPT. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ChatGPT
-/

import Lean.Elab.Command
import Std.Time
import Mathlib.Tactic.DeclarationNames
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
import Mathlib.Tactic.Linter.Header

/-!
# Linter for stale `deprecated` attributes

This linter reports declarations tagged with `@[deprecated]` whose
`since` date lies more than three months in the past. Such declarations
should usually have the `deprecated` attribute removed.
-/

open Lean Elab Command Linter

namespace Mathlib.Linter

/--
The `linter.deprecated.attr` linter flags declarations with a
`@[deprecated]` attribute whose `since` date is more than three months
in the past.
-/
register_option linter.deprecated.attr : Bool := {
  defValue := true
  descr := "enable the stale deprecated attribute linter"
}

namespace DeprecatedAttr

/-- Return `true` if the given ISO date string is more than three months in the past. -/
def outdated (since : String) : IO Bool := do
  match Std.Time.PlainDate.fromLeanDateString since with
  | .error _ =>
    return false
  | .ok date =>
    let today ← Std.Time.PlainDate.now
    let threshold := date.addMonthsClip (3 : Std.Time.Month.Offset)
    return compare threshold today == .lt

@[inherit_doc linter.deprecated.attr]
def deprecatedAttr : Linter where
  run := withSetOptionIn fun stx => do
    unless getLinterValue linter.deprecated.attr (← getLinterOptions) do
      return
    if (← get).messages.hasErrors then
      return
    for id in ← getNamesFrom (stx.getPos?.getD default) do
      let declName := id.getId
      let some info := Lean.Linter.deprecatedAttr.getParam? (← getEnv) declName | continue
      let some since := info.since? | continue
      if (← outdated since) then
        let disable := m!"note: this linter can be disabled with `set_option {linter.deprecated.attr.name} false`"
        logInfoAt id (.tagged linter.deprecated.attr.name
          m!"`{declName}` was deprecated on {since}, more than three months ago\n{disable}")

initialize addLinter deprecatedAttr

end DeprecatedAttr

end Mathlib.Linter

