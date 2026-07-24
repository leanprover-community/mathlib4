/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Correctness
public import Mathlib.Tactic.Determinant.Bird.Cert

/-!
# `norm_det` simproc and `eval_det` tactic

A tactic for normalizing matrix determinants.
-/

public meta section

open Lean Meta Elab Tactic Simp Qq
open Mathlib.Tactic.Determinant

/-- Normalize a `BirdDet.birdDet` expression. -/
def normalizeBirdDet (e : Expr) : MetaM Simp.Result := do
  let ⟨rα, ctx⟩ ← reifyBirdDet e
  let detNorm ← certBirdDet (rα := rα) |>.run' {} |>.run ctx |>.run .reducible
  Mathlib.Tactic.RingNF.cleanup {} {expr := detNorm.norm, proof? := some detNorm.proof}

/-- Normalize expressions of the form `Matrix.det (Matrix.ofArray (m := n) (n := n) A hA)`. -/
def normalizeDetOfArray? (e : Expr) : MetaM (Option Simp.Result) := do
  let e ← instantiateMVars e
  let ⟨_, α, e⟩ ← inferTypeQ' e
  let_expr Matrix.det _ _ _ _ detRingInst matrix := e
    | return none
  let some detRingInst ← checkTypeQ detRingInst q(CommRing $α)
    | throwError "expected determinant ring instance to have type {q(CommRing $α)}"
  let_expr Matrix.ofArray _ rowsExpr colsExpr arrayExpr sizeProof := matrix
    | return none
  let some rowsExpr ← checkTypeQ rowsExpr q(ℕ)
    | throwError "expected row dimension to have type `ℕ`, got {rowsExpr}"
  let some colsExpr ← checkTypeQ colsExpr q(ℕ)
    | throwError "expected column dimension to have type `ℕ`, got {colsExpr}"
  unless ← isDefEq rowsExpr colsExpr do
    throwError "expected square `ofArray` under `Matrix.det`"
  let some arrayExpr ← checkTypeQ arrayExpr q(Array $α)
    | throwError "expected flat array to have type {q(Array $α)}"
  let expectedSizeType := q(Array.size $arrayExpr = $rowsExpr * $rowsExpr)
  let sizeProof ← mkExpectedTypeHint sizeProof expectedSizeType
  let some sizeProof ← checkTypeQ sizeProof expectedSizeType
    | throwError "expected size proof to have type {expectedSizeType}"
  let some lhs ← checkTypeQ e α
    | throwError "expected determinant expression to have type {α}"
  let birdExpr := q(@BirdDet.birdDet $α $detRingInst $rowsExpr $arrayExpr)
  let arrayDet :=
    q(Matrix.det (Matrix.ofArray (m := $rowsExpr) (n := $rowsExpr) $arrayExpr $sizeProof))
  have : $lhs =Q $arrayDet := ⟨⟩
  let bridge : Q($lhs = $birdExpr) :=
    q(@BirdDet.det_eq_birdDet $α $detRingInst $rowsExpr $arrayExpr $sizeProof)
  let birdNorm ← normalizeBirdDet birdExpr
  let bridgeResult : Simp.Result := {
    expr := birdExpr
    proof? := some bridge
  }
  let result ← bridgeResult.mkEqTrans birdNorm
  return some result

/-- Normalize a literal `birdDet` call using the certificate-chain evaluator. -/
simproc_decl norm_det (BirdDet.birdDet _ _) := fun e => do
  return .done (← normalizeBirdDet e)

/-- Normalize `Matrix.det (Matrix.ofArray _)` calls by rewriting through `BirdDet.birdDet`. -/
simproc_decl norm_matrix_det (Matrix.det _) := fun e => do
  match ← normalizeDetOfArray? e with
  | some result => return .done result
  | none => return .continue

/-- Normalize `birdDet` calls in the target using the certificate-chain simproc. -/
macro (name := evalDet) "eval_det" : tactic => `(tactic| simp only [norm_det])

end
