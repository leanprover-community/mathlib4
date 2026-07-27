/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
meta import Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Correctness
public meta import Mathlib.Tactic.Determinant.Bird.Cert

/-!
# `norm_det` simproc and `eval_det` tactic

This module defines the `norm_det` simproc and the `eval_det` tactic for
normalizing determinants of matrix literals over a commutative ring.
-/

public meta section

open Lean Meta Qq
open Mathlib.Tactic.Determinant

/-- reify a `BirdDet` call and normalize it using the certificate-chain evaluator -/
private def normalizeBirdDet (e : Expr) : MetaM Simp.Result := do
  let ⟨rα, ctx⟩ ← reifyBirdDet e
  let detNorm ← certBirdDet (rα := rα) |>.run' {} |>.run ctx |>.run .reducible
  Mathlib.Tactic.RingNF.cleanup {} {expr := detNorm.norm, proof? := some detNorm.proof}

/-- Normalize the determinant of `A` from its `entries` in row-major order -/
private def normalizeDetFromEntries {u : Level} {α : Q(Type u)} {n : Q(ℕ)} (rα : Q(CommRing $α))
  (A : Q(Matrix (Fin $n) (Fin $n) $α)) (entries : Array Q($α)) :
    MetaM Simp.Result := do
  let arrayExpr : Q(Array $α) ← mkArrayLit α entries.toList
  let hA ← mkDecideProofQ q(Array.size $arrayExpr = $n * $n)
  have : $arrayExpr =Q Array.ofFn fun k : Fin ($n * $n) ↦ $A k.divNat k.modNat := ⟨⟩
  let ofArrayEqA := q(Matrix.ofArray_ofFn $A)
  let birdDet := q(BirdDet.birdDet $n $arrayExpr)
  let detEqBirdDet := q($ofArrayEqA ▸ BirdDet.det_eq_birdDet $arrayExpr $hA)
  let birdDetNorm ← normalizeBirdDet birdDet
  let detEqBirdDetRes : Simp.Result := ⟨birdDet, some detEqBirdDet, true⟩
  detEqBirdDetRes.mkEqTrans birdDetNorm

/-- Extract the entries of a square `!![...]` matrix literal in row-major order.
Returns `none` if `A` is not an `n × n` matrix literal. -/
private def entriesOfMatrixLiteral? {u : Level} {α : Q(Type u)} {n : Q(ℕ)}
    (A : Q(Matrix (Fin $n) (Fin $n) $α)) :
    MetaM (Option (Array Q($α))) := do
  let some dim ← getNatValue? n | return none
  let ~q(Matrix.of $rows) := A | return none
  let (matrixRows, _, _) ← Matrix.matchVecConsPrefix n rows
  unless matrixRows.length == dim do return none
  let entriesByRow ← matrixRows.mapM fun row => do
    let (entries, _, _) ← Matrix.matchVecConsPrefix n row
    return entries
  unless entriesByRow.all (·.length == dim) do return none
  let entries ← entriesByRow.flatten.mapM fun entry => do
    let some entry ← checkTypeQ entry α | throwError "expected matrix entry to have type {α}"
    return entry
  return some entries.toArray

/-- The `norm_det` simproc normalizes determinants of matrices written using `!![...]`
notation over a commutative ring. -/
simproc_decl norm_det (Matrix.det _) := fun e => do
  let e ← instantiateMVars e
  let ⟨_, _, e⟩ ← inferTypeQ' e
  let ~q(@Matrix.det (Fin $n) _ _ _ $rα $matrix) := e | return .continue
  let some entries ← entriesOfMatrixLiteral? matrix | return .continue
  return .done (← normalizeDetFromEntries rα matrix entries)

/--
`eval_det` normalizes determinants of matrices written using `!![...]` notation
over a commutative ring.

Examples:

```lean
example : Matrix.det (R := ℤ) !![1, 2; 3, 4] = -2 := by
  eval_det

example {R : Type*} [CommRing R] (a b c d : R) :
    Matrix.det !![a, b; c, d] = a * d - b * c := by
  eval_det
  ring
```
-/
macro (name := evalDet) "eval_det" : tactic => `(tactic| simp only [norm_det])

end
