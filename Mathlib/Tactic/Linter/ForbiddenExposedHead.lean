/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public meta import Mathlib.Tactic.Linter.Header  -- shake: keep
public import Batteries.Tactic.Lint.Basic

/-!
## The Forbidden Exposed Head Linter

This file defines a linter that checks every definitions against a list of head symbols
(mostly non-constructive data producer such as `Classical.choose`, `Exist.choose`, `Nonempty.some`, etc.),
and ensure that definitions with this head symbol are not exposed. -/


meta section

namespace Mathlib.Linter

open Lean Parser Elab Command Meta Linter

/-- The list of forbidden head names for the `forbiddenExposed` linter. -/
public def forbiddenExposed.forbiddenHeads : Array Name := #[
  `Classical.choose,
  `Classical.choice,
  `Exists.choose,
  `Nonempty.some ]

open Batteries.Tactic.Lint in
/-- Linter that checks if definitions are exposed `def`s with a known forbidden-for-exposure head
constant (defined in the `forbiddenExposed.forbiddenHeads` array). -/
@[env_linter] public def forbiddenExposed : Batteries.Tactic.Lint.Linter where
  noErrorsFound := "no exposed definitions with a forbidden head symbol."
  errorsFound := "FOUND exposed definitions with a forbidden head symbol"
  test declName := do
    let c ← getConstInfo declName
    -- skip non-definitions, automatic declarations, and definitions without an exposed body
    unless c.isDefinition && !(← isAutoDecl declName) && (← getEnv).hasExposedBody declName do return none
    let some body := c.value? | return none
    let (_, _, b) ← lambdaMetaTelescope body
    let n := b.getAppFn.constName
    if forbiddenExposed.forbiddenHeads.any (· == n) then
      return m!"The definition `{declName}` is exposed and has
        `{n}` as head symbol of its body. \
        Please mark this definition with `@[no_expose]` or move it in a non-exposed section
        and provide specification lemmas for this definition."
    else return none
