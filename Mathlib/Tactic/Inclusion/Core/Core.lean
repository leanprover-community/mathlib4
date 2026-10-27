/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Inclusion.Core.Inclusion
public meta import Lean.Meta.Native

/-!
# Core implementation of the `inclusion` tactic

This file defines the `TacticM` core of the `inclusion` tactic.

## Implimentation Notes

The approach to the implimentation of the `kernel == true` and `native == true` options mirrors
the approach used by the `decide` tactic (and reuses the code where possible).

-/

@[expose] public meta section

open Lean Meta

namespace Inclusion

/-- Configuration for the `inclusion` tactic. -/
structure InclusionConfig where
  /-- If `kernel == true` then skip the compiled check. -/
  kernel : Bool := false
  /-- If `native == true` then use compiled computation in the proof (warning: this adds the Lean
  compiler to the trusted codebase). -/
  native : Bool := false
  /-- A map from inclusion parameter names to their user-supplied values. -/
  paramSettings : NameMap Expr := {}
  /-- The names of the enabled inclusion extension families. -/
  families : Array Name := #[]

/-- Compile and evaluate the closed `IntervalBool` expression `inclusionExpr`. -/
def compileInclusionCheck (inclusionExpr : Expr) : MetaM IntervalBool :=
  unsafe evalExpr IntervalBool (mkConst ``IntervalBool) inclusionExpr

/-- Check that `inclusionExpr` equals `IntervalBool.true` using a compiled computation, and then
pass the proof term to the kernel (where it will be verified again by reflection). -/
def mkInclusionTrueProof (inclusionExpr : Expr) : MetaM Expr := do
  match ← compileInclusionCheck inclusionExpr with
  | .true => return mkIntervalBoolRefl inclusionExpr
  | .false => throwError "The proposition is provably false"
  | .undetermined => throwError "The proposition was not proven true or false."

/-- Prove that `inclusionExpr` equals `IntervalBool.true` using kernel reduction
(without any prior compiled check). -/
def mkKernelInclusionTrueProof (inclusionExpr : Expr) : MetaM Expr := do
  let expectedType ← mkEq inclusionExpr (mkConst ``IntervalBool.true)
  let lemmaLevels := (collectLevelParams {} expectedType).params.toList
  try
    let lemmaName ← withOptions (Elab.async.set · false) do
      mkAuxLemma lemmaLevels expectedType (mkIntervalBoolRefl inclusionExpr)
    return mkConst lemmaName (lemmaLevels.map .param)
  catch _ =>
    throwError "The kernel failed to verify the proposition."

/-- Use native evaluation to prove that `inclusionExpr` equals `IntervalBool.true`. -/
def mkNativeInclusionTrueProof (inclusionExpr : Expr) : MetaM Expr := do
  let result := mkApp (mkConst ``IntervalBool.isTrue) inclusionExpr
  match ← nativeEqTrue `inclusion result (axiomDeclRange? := (← getRef)) with
  | .success proof => mkAppM ``IntervalBool.eq_true_of_isTrue_eq_true #[proof]
  | .notTrue => throwError "Native computation could not verify the proposition."

/-- Prove `goal`, by constructing an `exprInclusion` for it and verifying that
`exprInclusion.inclusion` evaluates to `IntervalBool.true`. -/
def inclusionCore (goal : Expr) (config : InclusionConfig) : MetaM Expr := do
  if config.kernel && config.native then
    throwError "Cannot simultaneously enable +kernel and +native"
  let goal ← instantiateMVars goal
  unless ← isProp goal do
    throwError "The goal is not a proposition"
  let exprInclusion ← (toExprInclusion goal).run config.paramSettings config.families
  let inclusionExpr := exprInclusion.inclusion
  let inclusionProof ←
    if config.native then
      mkNativeInclusionTrueProof inclusionExpr
    else if config.kernel then
      mkKernelInclusionTrueProof inclusionExpr
    else
      mkInclusionTrueProof inclusionExpr
  return exprInclusion.mkGoalProof goal inclusionProof

end Inclusion
