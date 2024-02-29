/-
Copyright (c) 2023 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Std.Tactic.Lint

/-!
# Linters for Mathlib

In this file we define additional linters for mathlib.

Perhaps these should be moved to Std in the future.
-/

namespace Std.Tactic.Lint
open Lean Meta

/--
Linter that checks whether a structure should be in Prop.
-/
@[std_linter] def structureInType : Linter where
  noErrorsFound := "no structures that should be in Prop found."
  errorsFound := "FOUND STRUCTURES THAT SHOULD BE IN PROP."
  test declName := do
    unless isStructure (← getEnv) declName do return none
    -- remark: using `Lean.Meta.isProp` doesn't suffice here, because it doesn't (always?)
    -- recognize predicates as propositional.
    let isProp ← forallTelescopeReducing (← inferType (← mkConstWithLevelParams declName))
      fun _ ty => return ty == .sort .zero
    if isProp then return none
    let projs := (getStructureInfo? (← getEnv) declName).get!.fieldNames
    if projs.isEmpty then return none -- don't flag empty structures
    let allProofs ← projs.allM (do isProof <| ← mkConstWithLevelParams <| declName ++ ·)
    unless allProofs do return none
    return m!"all fields are propositional but the structure isn't."

/--
Linter that checks whether a theorem statement contains `Classical.propDecidable`.
-/
-- To do: maybe also check definition bodies? I expect more false positives there.
@[std_linter] def illegalClassical : Linter where
  noErrorsFound := "no classicality in theorem statements found."
  errorsFound := "FOUND PROPDECIDABLE IN THEOREM STATEMENTS."
  test declName := do
    let declInfo ← getConstInfo declName
    if declInfo.type.getUsedConstants.contains `Classical.propDecidable then
      return m!"theorem statement contains `Classical.propDecidable`."
    return none

-- open Classical
-- variable (p : Prop)

-- theorem f : 0 = if p then 0 else 1 := sorry
-- theorem g [Decidable p] : 0 = if p then 0 else 1 := sorry

-- #lint
