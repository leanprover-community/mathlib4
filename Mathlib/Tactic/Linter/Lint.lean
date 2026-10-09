/-
Copyright (c) 2023 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

-- This module imports all of `Batteries.Tactic.Lint`, not just `Batteries.Tactic.Lint.Basic`.
-- It is responsible for making `#lint` available through `Mathlib.Init`.
-- TODO: consider removing `-- shake: keep` after batteries#1613
public import Batteries.Tactic.Lint -- shake: keep
public import Lean.Linter.Deprecated
public import Mathlib.Tactic.DeclarationNames

/-!
# Linters for Mathlib

In this file we define additional linters for mathlib,
which concern the *behaviour* of the linted code, and not issues of code style or formatting.

Perhaps these should be moved to Batteries in the future.
-/

meta section

namespace Batteries.Tactic.Lint
open Lean Meta

/--
Linter that checks whether a structure should be in Prop.
-/
@[env_linter] public def structureInType : Linter where
  noErrorsFound := "no structures that should be in Prop found."
  errorsFound := "FOUND STRUCTURES THAT SHOULD BE IN PROP."
  test declName := do
    unless isStructure (← getEnv) declName do return none
    -- remark: using `Lean.Meta.isProp` doesn't suffice here, because it doesn't (always?)
    -- recognize predicates as propositional.
    let isProp ← forallTelescopeReducing (← inferType (← mkConstWithLevelParams declName))
      fun _ ty ↦ return ty == .sort .zero
    if isProp then return none
    let projs := (getStructureInfo? (← getEnv) declName).get!.fieldNames
    if projs.isEmpty then return none -- don't flag empty structures
    let allProofs ← projs.allM (do isProof <| ← mkConstWithLevelParams <| declName ++ ·)
    unless allProofs do return none
    return m!"all fields are propositional but the structure isn't."

/-- Linter that check that all `deprecated` tags come with `since` dates. -/
@[env_linter] public def deprecatedNoSince : Linter where
  noErrorsFound := "no `deprecated` tags without `since` dates."
  errorsFound := "FOUND `deprecated` tags without `since` dates."
  test declName := do
    let some info := Lean.Linter.deprecatedAttr.getParam? (← getEnv) declName | return none
    match info.since? with
    | some _ => return none -- TODO: enforce `YYYY-MM-DD` format
    | none => return m!"`deprecated` attribute without `since` date"

end Batteries.Tactic.Lint
