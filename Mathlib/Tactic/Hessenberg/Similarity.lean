/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.Data.Matrix.Reflection  -- shake: keep (Qq dependency)
public import Mathlib.LinearAlgebra.Matrix.Hessenberg.Similarity  -- shake: keep (Qq dependency)
public import Mathlib.Tactic.Echelon.Cert
public import Mathlib.Tactic.Echelon.Rat
public import Mathlib.Tactic.Hessenberg.Reduce
public import Mathlib.Tactic.Matrix.MulExpand
public import Mathlib.Tactic.Matrix.OfLists  -- shake: keep (Qq dependency)
public meta import Mathlib.Tactic.Echelon.Cert
public meta import Mathlib.Tactic.Echelon.Rat
public meta import Mathlib.Tactic.Hessenberg.Reduce
public meta import Mathlib.Tactic.Matrix.MulExpand

/-!
# The Hessenberg similarity driver

Given a `ℚ`-entried matrix literal `A`, the entry point `mkHessenbergSimilarity` runs the
reduction `reduce` and elaborates a certificate `Hessenberg.Similarity A` from its data.

## Main definitions

- `mkHessenbergSimilarity`: produce and elaborate the certificate of a matrix literal.
- `SimilarityResult`: the elaborated certificate together with the reduction data.
- `certifySimilarityEq`: prove the similarity from the rows of its matrices.

## Implementation notes

The matrices of the certificate are `ofLists` terms on their lists of rows. The similarity
`A.submatrix σ σ * L = L * H` is proved on those lists, as two products expanded by `proveMul`.
The shapes of `L` and `H` are decided. The recurrence runs on a literal of the row-major array of
`H`, which is identified with `H.toArray` by one evaluation of the list of the entries of `H`.
-/

public meta section

open Lean Meta Qq Mathlib.Tactic.Matrix

namespace Mathlib.Tactic.Hessenberg

/-- Build the numeral of a rational in `ℚ`: an integer numeral, or `p / q` with the sign
outside the division. -/
def mkRatExpr (r : Rat) : MetaM Q(ℚ) := do
  if r.den == 1 then Echelon.mkIntNumeral q(ℚ) r.num
  else
    have p : Q(ℚ) := ← mkNumeral q(ℚ) r.num.natAbs
    have q : Q(ℚ) := ← mkNumeral q(ℚ) r.den
    return if r.num < 0 then q(-($p / $q)) else q($p / $q)

/-- Three views of one matrix literal. -/
structure MatrixViews (m n : ℕ) where
  /-- The matrix, the `ofLists` term on `lit`. -/
  matrix : Q(Matrix (Fin $m) (Fin $n) ℚ)
  /-- The entries as a list of rows. -/
  lit : Q(List (List ℚ))
  /-- The row-major entries. -/
  entries : List (List Q(ℚ))

/-- Build the `MatrixViews` of the row-major entries `rows`. -/
def mkMatrixViews (m n : ℕ) (rows : Array (Array Q(ℚ))) : MatrixViews m n :=
  let entries := rows.toList.map Array.toList
  have lit : Q(List (List ℚ)) :=
    mkListLitQ (u := .zero) (α := q(List ℚ)) (entries.map (mkListLitQ (u := .zero) (α := q(ℚ))))
  { matrix := q(ofLists $m $n $lit), lit, entries }

/-- Prove the product `X * Y = Z` from the rows of the views. -/
def certifyMulEq {l m n : ℕ} (X : MatrixViews l m) (Y : MatrixViews m n) (Z : MatrixViews l n) :
    MetaM Q($(X.matrix) * $(Y.matrix) = $(Z.matrix)) := do
  let r := proveMul (α := q(ℚ)) q(inferInstance) q(inferInstance) q(inferInstance) l m n
    X.entries Y.entries
  -- the kernel evaluates the sums of products against the entries of `Z`
  let hZ := mkExpectedPropHint (← mkEqRefl r.expr) (← mkEq r.expr Z.lit)
  mkAppM ``ofLists_mul #[← mkEqTrans r.proof hZ]

/-- Prove the similarity `A.submatrix σ σ * L = L * H`, where the entries of `Aσ` are those of
`A` arranged by `σ`, and `P` is the common value of `Aσ * L` and `L * H`. -/
def certifySimilarityEq {n : ℕ} (A : Q(Matrix (Fin $n) (Fin $n) ℚ)) (σ : Q(Equiv.Perm (Fin $n)))
    (Aσ L H P : MatrixViews n n) :
    MetaM Q((($A).submatrix $σ $σ) * $(L.matrix) = $(L.matrix) * $(H.matrix)) := do
  have Aσm := Aσ.matrix
  have Lm := L.matrix
  have Hm := H.matrix
  have Pm := P.matrix
  have hperm : Q(($A).submatrix $σ $σ = $Aσm) :=
    mkExpectedPropHint q((Matrix.etaExpand_eq (($A).submatrix $σ $σ)).symm)
      q(($A).submatrix $σ $σ = $Aσm)
  have hAL : Q($Aσm * $Lm = $Pm) := ← certifyMulEq Aσ L P
  have hLH : Q($Lm * $Hm = $Pm) := ← certifyMulEq L H P
  have h : Q((($A).submatrix $σ $σ) * $Lm = $Lm * $Hm) := q($hperm ▸ ($hAL).trans ($hLH).symm)
  return h

/-- The result of producing a Hessenberg similarity of `A`. -/
structure SimilarityResult {n : ℕ} (A : Q(Matrix (Fin $n) (Fin $n) ℚ)) where
  /-- The elaborated `Hessenberg.Similarity` certificate term. -/
  cert : Q(Hessenberg.Similarity $A)
  /-- The literal of the row-major array of the Hessenberg matrix of the certificate. -/
  Harr : Q(Array ℚ)
  /-- The proof that `Harr` is the array of the Hessenberg matrix of the certificate. -/
  toArray_eq : Q(($cert).H.toArray = $Harr)
  /-- The reduction data underlying the certificate. -/
  red : Reduction

/-- Produce the `Hessenberg.Similarity` certificate and corresponding `Reduction` of the `n × n`
matrix literal `A` over `ℚ` with rows of entries `entries`. -/
def mkHessenbergSimilarity (n : ℕ) (A : Q(Matrix (Fin $n) (Fin $n) ℚ))
    (entries : Array (Array Expr)) : MetaM (SimilarityResult A) := do
  let vals ← entries.mapM (·.mapM (Echelon.evalRatEntry true))
  let red := reduce n vals
  let σ ← Echelon.mkPerm n red.swaps
  let arrange {β : Type} [Inhabited β] (M : Array (Array β)) : Array (Array β) :=
    red.perm.map fun i => red.perm.map fun j => (M[i]!)[j]!
  let rows (M : Array (Array Rat)) : List (List Rat) := M.toList.map Array.toList
  let pVals := ListMatrix.mul n n n (rows (arrange vals)) (rows red.L)
  have Aσ := mkMatrixViews n n (arrange entries)
  have L := mkMatrixViews n n (← red.L.mapM (·.mapM mkRatExpr))
  have H := mkMatrixViews n n (← red.H.mapM (·.mapM mkRatExpr))
  have P := mkMatrixViews n n ((← pVals.mapM (·.mapM mkRatExpr)).map List.toArray).toArray
  have Lm := L.matrix
  have Hm := H.matrix
  have hmul : Q((($A).submatrix $σ $σ) * $Lm = $Lm * $Hm) := ← certifySimilarityEq A σ Aσ L H P
  let hhess ← mkDecideProofQ q(($Hm).IsUpperHessenberg)
  let hlower ← mkDecideProofQ q(($Lm).IsLowerTriangular)
  let hdiag ← mkDecideProofQ q(∀ i, ($Lm).diag i ≠ 0)
  have cert : Q(Hessenberg.Similarity $A) := q(⟨$Lm, $σ, $Hm, $hmul, $hlower, $hdiag, $hhess⟩)
  have lH : Q(List ℚ) := ← mkListLit q(ℚ) H.entries.flatten
  have hofn : Q((List.ofFn fun k : Fin ($n * $n) => $Hm k.divNat k.modNat) = $lH) :=
    mkExpectedPropHint q(Eq.refl $lH)
      q((List.ofFn fun k : Fin ($n * $n) => $Hm k.divNat k.modNat) = $lH)
  have toArray_eq : Q(($cert).H.toArray = List.toArray $lH) :=
    mkExpectedPropHint q(List.toArray_ofFn.symm.trans (congrArg List.toArray $hofn))
      q(($cert).H.toArray = List.toArray $lH)
  return { cert, Harr := q(List.toArray $lH), toArray_eq, red }

end Mathlib.Tactic.Hessenberg
