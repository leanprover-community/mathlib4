/-
Copyright (c) 2026 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Batteries.Tactic.Lint.Basic
public import Mathlib.Tactic.Linter.UnusedInstancesInType
import all Mathlib.Tactic.Linter.UnusedInstancesInType -- for collectUnnecessaryInstanceBinderIdxsWhere

/-! # The bundled morphism class linter

The "bundled morphism classes" linter (under construction) checks that certain design
considerations regarding bundled morphism classes are upheld in mathlib.

- definitions should be phrased using concrete morphisms, not their morphism classes:
  a definition `LinearMapClass.ker` (taking an argument which is a `LinearMapClass`) would be bad,
  `LinearMap.ker` (defined on a `LinearMap`) is better
- FUTURE:
  theorems whose statement mentions a definition on a bundled morphism
  should take in a concrete morphism as argument, not a morphism class.
  for example, a theorem involving `LinearMap.ker` should be phrased for a `LinearMap`
  (On the other hand, if these definitions are only mentioned in the proof, that is fine.)
  TODO: how to detect the list of such definitions nicely?
- FUTURE:
  a theorem about bundled morphisms whose statement involves coercions to functions
  (but not the underlying morphism class) can be stated for the general class
  (and perhaps should?)

The list of such classes is manually hard-coded for now.

-/

open Lean

meta def morphismClassesToLint : Array Name := #[
  `LinearMapClass,
  `SemilinearMapClass,
  `StarRingHomClass,
  `StarRingEquivClass,
  `NonUnitalStarAlgHomClass,
  `StarAlgHomClass,
  `StarAlgEquivClass,
]

open Batteries.Tactic.Lint in
/-- Linter that checks for definitions which take a bundled morphism class (such as
`LinearMapClass`) as an argument: usually, this is a bad idea. -/
@[env_linter] public meta def defsWithMorphismClass : Batteries.Tactic.Lint.Linter where
  noErrorsFound := "no definitions with a bundled morphism argument found."
  errorsFound := "FOUND definitions with a bundled morphism argument."
  test declName := do
    -- We still lint in the presence of sorries: completing a sorry should not influence this check.
    let constantInfo := ((← getEnv).find? declName).get!
    if !constantInfo.isDefinition then return none
    -- TODO: can I check if `declName` is an instance, and return if so?


    -- Attempt one at a proper check, re-using the `unusedInstancesInType` linter's logic.
    -- let unusedInstances ← constantInfo.type.collectUnnecessaryInstanceBinderIdxsWhere (fun e ↦
    --   morphismClassesToLint.any fun cls ↦ e.isConstOf cls)
    -- Did not appear to work.

    -- Attempt two: does any of the constants we care about appear in the type?
    let classConstantsUsed := constantInfo.type.getUsedConstantsAsSet |>.filter (morphismClassesToLint.contains ·)
    if !classConstantsUsed.isEmpty then
      return m!"The definition `{.ofConstName declName true}` takes a `LinearMapClass` argument.\n\
      Per https://github.com/leanprover-community/mathlib4/issues/31365, this is (usually) a bad \
      idea:\nplease the definition to take in a `LinearMap` argument instead.\n\
      Note that this linter has false positives if a LinearMapClass is just coerced to a function."
    return none

    -- return m!"unusedInstances is {unusedInstances}, constants used is {constantInfo.type.getUsedConstantsAsSet.toArray}"
    -- -- HACKY check: print the type and check for occurrences of `LinearMapClass`
    -- let typeStr ← (m!"{constantInfo.type}").toString
    -- let hackyCheck := morphismClassesToLint.any (fun cls ↦ (typeStr.contains (cls.toString.drop 1)))
    -- if hackyCheck && classConstantsUsed.isEmpty then
    --   return m!"The definition `{.ofConstName declName true}` takes a `LinearMapClass` argument.\n\
    --     Per https://github.com/leanprover-community/mathlib4/issues/31365, this is (usually) a bad \
    --     idea:\nplease change the definition to take in a `LinearMap` argument instead.\n\
    --     Note that this linter has false positives if a LinearMapClass is just coerced to a function.\n\
    --     Note: the 'proper' linter check doesn't fire here; there's still a bug to fix!"
    -- else if classConstantsUsed.isEmpty then
    --   if !hackyCheck then return m!"curious: proper check reports errors; hacky check succeeds:\n\
    --     definition's type is {constantInfo.type}, proper check reports is {classConstantsUsed.toArray}"
    --   else
    --     return m!"The definition `{.ofConstName declName true}` takes a `LinearMapClass` argument.\n\
    --       Per https://github.com/leanprover-community/mathlib4/issues/31365, this is (usually) a bad \
    --       idea:\nplease the definition to take in a `LinearMap` argument instead.\n\
    --       Note that this linter has false positives if a LinearMapClass is just coerced to a function."
    -- return none
