/-
Copyright (c) 2024 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
import Mathlib.Command.Linter.LintingRules

/-! # Deprecated syntax

Registers the `deprecated` `linting_rules` category.
-/

open Lean Linter

/--
The `deprecated` `linting_rules` category can be used to deprecate syntax.

Example:
```lean
linting_rules : deprecated
| `(node|stx) => do
  ...
  return (msg : MessageData)
```
-/
register_linting_rules_cat deprecated := {
  Out := MessageData
  resolve := fun msg => do
    logWarning <| .tagged ``deprecatedAttr msg
    return .done
  opt := .existing linter.deprecated
}
