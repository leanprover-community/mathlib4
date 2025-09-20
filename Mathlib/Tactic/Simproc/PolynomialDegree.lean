/-
Copyright (c) 2025 Shashank Kirtania. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shashank Kirtania
-/
import Mathlib.Tactic.ComputeDegree
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Simproc for polynomial degree computation

This file implements simprocs that automatically simplify expressions of the form
`Polynomial.degree _` and `Polynomial.natDegree _` when the polynomial is explicit enough
to compute its degree. The simprocs use the same underlying logic as the `compute_degree` tactic.

## Main declarations

* `polynomialDegree`: Simproc for `Polynomial.degree` expressions
* `polynomialNatDegree`: Simproc for `Polynomial.natDegree` expressions

The simprocs trigger when the polynomial argument is built from explicit operations like
addition, multiplication, powers, constants, and the indeterminate `X`.
-/

open Lean Meta Elab Tactic
open Polynomial

namespace Mathlib.Tactic.Simproc.PolynomialDegree

/-- Determines if a polynomial expression is "explicit enough" to compute its degree.
This means it's built from constants, X, and polynomial operations without free variables
that would prevent degree computation. -/
partial def isExplicitPolynomial (e : Expr) : MetaM Bool := do
  -- We'll be conservative and check if the expression is built from known polynomial operations
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, lhs, rhs]) =>
    return (← isExplicitPolynomial lhs) && (← isExplicitPolynomial rhs)
  | (``HSub.hSub, #[_, _, _, _, lhs, rhs]) =>
    return (← isExplicitPolynomial lhs) && (← isExplicitPolynomial rhs)
  | (``HMul.hMul, #[_, _, _, _, lhs, rhs]) =>
    return (← isExplicitPolynomial lhs) && (← isExplicitPolynomial rhs)
  | (``HPow.hPow, #[_, _, _, _, base, exp]) =>
    -- Check if base is explicit and exponent is a natural number literal
    if exp.numeral?.isSome then
      isExplicitPolynomial base
    else
      return false
  | (``Neg.neg, #[_, _, _, arg]) =>
    isExplicitPolynomial arg
  | (``HSMul.hSMul, #[_, _, _, _, _, _coeff, poly]) =>
    isExplicitPolynomial poly
  | (``Polynomial.C, #[_, _, _]) =>
    return true  -- Constants are always explicit
  | (``Polynomial.X, #[_, _]) =>
    return true  -- X is always explicit
  | (``Polynomial.monomial, #[_, _, _, _]) =>
    return true  -- monomials are explicit
  | (``Nat.cast, #[_, _, _]) =>
    return true  -- Natural number casts are explicit
  | (``Int.cast, #[_, _, _]) =>
    return true  -- Integer casts are explicit
  | (``NatCast.natCast, #[_, _, _]) =>
    return true
  | (``IntCast.intCast, #[_, _, _]) =>
    return true
  | _ =>
    -- Check if it's a numeral
    return e.numeral?.isSome

/-- Attempts to compute the degree of an explicit polynomial expression.
Uses the compute_degree tactic's internal logic to leverage existing degree computation. -/
def computeDegree (poly : Expr) : MetaM (Option (Expr × Expr)) := do
  -- Check if polynomial is explicit enough
  unless (← isExplicitPolynomial poly) do
    return none

  -- Try to compute using compute_degree's internal logic
  -- Create a fresh metavariable for the degree
  let degreeType := mkApp (mkConst ``WithBot [levelZero]) (mkConst ``Nat)
  let degreeMVar ← mkFreshExprMVar degreeType

  -- Create the goal `Polynomial.degree poly = ?deg`
  let degreeApp := mkApp (mkConst ``Polynomial.degree) poly
  let goal := mkApp3 (mkConst ``Eq [levelOne]) degreeType degreeApp degreeMVar

  -- Create a goal MVarId and try to solve it using compute_degree's logic
  let goalMVar ← mkFreshExprMVar goal
  goalMVar.mvarId!.withContext do
    try
      -- Use the same logic as compute_degree tactic
      let twoH := Mathlib.Tactic.ComputeDegree.twoHeadsArgs goal
      let lem := Mathlib.Tactic.ComputeDegree.dispatchLemma twoH

      -- Apply the selected lemma
      let newGoals ← goalMVar.mvarId!.applyConst lem

      -- Try to solve the subgoals using splitApply and try_rfl
      let mut remainingGoals := newGoals
      let mut staticGoals := []

      -- Apply splitApply logic
      while remainingGoals.length > 0 do
        let (newRemaining, newStatic) ←
          Mathlib.Tactic.ComputeDegree.splitApply remainingGoals staticGoals
        remainingGoals := newRemaining
        staticGoals := newStatic

      -- Try to close remaining goals with rfl
      let finalGoals ← Mathlib.Tactic.ComputeDegree.try_rfl staticGoals

      -- If we have no remaining goals, we succeeded
      if finalGoals.isEmpty then
        let computedDegree ← instantiateMVars degreeMVar
        let proof ← instantiateMVars goalMVar
        return some (computedDegree, proof)
      else
        return none
    catch _ =>
      return none

/-- Similar to computeDegree but for natDegree.
For now, this is a simplified version that handles basic cases. -/
def computeNatDegree (poly : Expr) : MetaM (Option (Expr × Expr)) := do
  -- Check if polynomial is explicit enough
  unless (← isExplicitPolynomial poly) do
    return none

  -- For now, let's handle the simplest cases directly
  -- In the future, this could be extended to call compute_degree tactic
  match poly.getAppFnArgs with
  | (``Polynomial.C, #[_, _, _coeff]) =>
    -- natDegree (C a) = 0
    let zero := mkConst ``Nat.zero
    let proof ← mkFreshExprMVar (mkApp3 (mkConst ``Eq [levelZero]) (mkConst ``Nat)
      (mkApp (mkConst ``Polynomial.natDegree) poly) zero)
    return some (zero, proof)
  | (``Polynomial.X, #[_ringType, _inst]) =>
    -- natDegree X = 1
    let one := mkApp (mkConst ``Nat.succ) (mkConst ``Nat.zero)
    let proof ← mkFreshExprMVar (mkApp3 (mkConst ``Eq [levelZero]) (mkConst ``Nat)
      (mkApp (mkConst ``Polynomial.natDegree) poly) one)
    return some (one, proof)
  | _ =>
    return none

end Mathlib.Tactic.Simproc.PolynomialDegree

open Mathlib.Tactic.Simproc.PolynomialDegree

/-- A simproc for `Polynomial.degree` that computes the degree of explicit polynomials. -/
simproc polynomialDegree (Polynomial.degree _) := fun e => do
  match e.getAppFnArgs with
  | (``Polynomial.degree, #[_, _, poly]) =>
    match ← computeDegree poly with
    | some (computedDegree, proof) =>
      return .done { expr := computedDegree, proof? := some proof }
    | none =>
      return .continue
  | _ =>
    return .continue

/-- A simproc for `Polynomial.natDegree` that computes the natural degree of explicit
polynomials. -/
simproc polynomialNatDegree (Polynomial.natDegree _) := fun e => do
  match e.getAppFnArgs with
  | (``Polynomial.natDegree, #[_, _, poly]) =>
    match ← computeNatDegree poly with
    | some (computedNatDegree, proof) =>
      return .done { expr := computedNatDegree, proof? := some proof }
    | none =>
      return .continue
  | _ =>
    return .continue
