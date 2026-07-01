/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Bird
public meta import Mathlib.Util.Qq

/-!
# Reification support for the determinant tactic

This file contains the meta-level parser used by `normalizeBirdDet` to parse
`BirdDet.birdDet` calls into `BirdDetInfo`, that is used by the
certificate-chaining evaluator.

## Main definitions

- `reifyBirdDet`: Parse a call to `BirdDet.birdDet` into `BirdDetInfo`

-/

public meta section

open Lean Meta Qq

namespace Mathlib.Tactic.Determinant

/-- Parse an array literal into an array of element expressions.

Compared to `getArrayLit?`, this also performs `whnf`.
-/
def arrayLiteral? (e : Expr) : MetaM (Option (Array Expr)) := do
  if let some elems ← getArrayLit? e then return some elems
  let e ← whnf e
  match_expr e with
  | Array.mk _ xs => getListLit? xs
  | _ => return none

/-- The matrix data parsed from a `birdDet` call. -/
structure BirdDetData {u : Level} {α : Q(Type u)} (rα : Q(CommRing $α)) where
  /-- The dimension of the reified matrix -/
  dimension : ℕ
  /-- The quoted dimension expression from the reified determinant call. -/
  dimensionLit : Q(ℕ)
  /-- The array of matrix entries as an Expr -/
  arrayExpr : Q(Array $α)
  /-- An array of matrix entry `Expr`s` -/
  arrayEntries : Array Q($α)

/-- Information parsed by `reifyBirdDet`. -/
structure BirdDetInfo where
  /-- The universe level associated with the `birdDet` call -/
  {u : Level}
  /-- The type of a matrix entry -/
  {α : Q(Type u)}
  /-- The `CommRing` instance for matrix entries -/
  rα : Q(CommRing $α)
  /-- The typed matrix data parsed from the determinant expression. -/
  data : BirdDetData rα

/-- Recognise a `birdDet` call and reify the matrix argument into `BirdDetInfo`. -/
def reifyBirdDet (e : Expr) : MetaM BirdDetInfo := do
  let e ← instantiateMVars e
  let ⟨_, α, _⟩ ← inferTypeQ' e
  let_expr BirdDet.birdDet _ birdRingInst dimensionExpr arrayExpr := e
    | throwError "expected an application of `birdDet, got {e}"
  let some rα ← checkTypeQ birdRingInst q(CommRing $α)
    | throwError "expected `birdDet` ring instance to have type {q(CommRing $α)}"
  let dimensionExpr ← whnf dimensionExpr
  let some dimensionLit ← checkTypeQ dimensionExpr q(ℕ)
    | throwError "expected the dimension to have type `ℕ`, got {dimensionExpr}"
  let some dimension ← getNatValue? dimensionLit
    | throwError "expected the dimension to be a `ℕ` literal, got {dimensionLit}"
  let some arrayExpr ← checkTypeQ arrayExpr q(Array $α)
    | throwError "expected the array to have type {q(Array $α)}"
  let some arrayEntries ← arrayLiteral? arrayExpr
    | throwError "expected an array literal matrix, got {arrayExpr}"
  unless arrayEntries.size == dimension * dimension do
    throwError "matrix size mismatch: array has {arrayEntries.size} entries, \
      expected {dimension * dimension}"
  let arrayEntries ← arrayEntries.mapM fun entry => do
    let some entry ← checkTypeQ entry α
      | throwError "expected array entry to have type {α}"
    return entry
  return {
    rα
    data := {
      dimension
      dimensionLit
      arrayExpr
      arrayEntries
    }
  }

end Mathlib.Tactic.Determinant

end
