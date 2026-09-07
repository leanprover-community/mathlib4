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

open Lean Meta

/-- List of bundled morphism classes whose definitions we lint.
TODO: replace with an auto-generated list, once the list of exceptions is shorter. -/
meta def morphismClassesToLint : Array Name := #[
  `LinearMapClass, `SemilinearMapClass,
  `ContinuousSemilinearMapClass, `ContinuousLinearMapClass,
  `RingHomClass, `RingEquivClass, `AlgHomClass, `AlgEquivClass,
  `StarRingHomClass,
  `StarRingEquivClass,
  `NonUnitalStarAlgHomClass,
  `StarAlgHomClass, `StarAlgEquivClass,
  `AlgHomClass, `AlgEquivClass,
  `CompletelyPositiveMapClass, `SemilinearIsometryClass,
  `CoalgHomClass, `CoalgEquivClass,
  `RingInvoClass,
  `ContinuousAlgEquivClass, `ContinuousAlgEquivClass,
  `ContinuousLinearEquivClass, `ContinuousSemilinearEquivClass,
  `CompletelyPositiveMapClass,
  `OrderRingHomClass, `OrderRingIsoClass,
]

/-- For each class `FooHomClass`, generate the name `FooHomClass.toFoo`. -/
meta def falseProjectionNames : Array Name :=
  (morphismClassesToLint.map fun n ↦ n.str <| ("to" ++ n.getString!.dropEnd 5))
  ++ #[`CompletelyPositiveMapClass.toCompletelyPositiveLinearMap]

open Batteries.Tactic.Lint in
/-- Linter that checks for definitions which take a bundled morphism class (such as
`LinearMapClass`) as an argument: usually, this is a bad idea. -/
@[env_linter] public meta def defsWithMorphismClass : Batteries.Tactic.Lint.Linter where
  noErrorsFound := "no definitions with a bundled morphism argument found."
  errorsFound := "FOUND definitions with a bundled morphism argument."
  test declName := do
    -- Don't check auto-generated declarations.
    if (← getEnv).isAutoDecl declName then return none
    -- We skip linting instances: an instance from one morphism class to another is totally fine.
    if ← isInstance declName then return none
    -- We still lint in the presence of sorries: completing a sorry should not influence this check.

    let constantInfo := ((← getEnv).find? declName).get!
    if !constantInfo.isDefinition then
      return none
    -- Check if any of the constants we care about appears in the type.
    let morphismClassesAppearing :=
      constantInfo.type.getUsedConstantsAsSet.filter (morphismClassesToLint.contains ·)
    if morphismClassesToLint.isEmpty then return none
    else if #[`ofClass, `casesOn, `recOn].contains (declName.components.getLastD `dummy) then
      -- Heuristic: if a definition is named literally `ofClass`, don't warn.
      -- We also exclude auto-generated declarations `recOn` and `casesOn`.
      return none
    else if Lean.Linter.isDeprecated (← getEnv) declName then
      -- We don't warn about deprecated declarations either: those will be removed soon anyway.
      return none
    else if falseProjectionNames.contains declName then
      -- If the declaration in question is named like a morphism class to morphism coercion,
      -- we also don't error. (If anything, this should raise a different error.)
      return none

    if !morphismClassesAppearing.isEmpty then
      let clsName := morphismClassesAppearing.toArray[0]! |>.toString.dropEnd 5
      return m!"The definition `{.ofConstName declName true}` takes a `{clsName}Class` argument.\n\
      Per https://github.com/leanprover-community/mathlib4/issues/31365, this is a bad \
      idea:\nplease change the definition to take in a `{clsName}` argument instead."
      -- Note that this linter has false positives if a `{clsName}Class` is just coerced to a function."
    return none
