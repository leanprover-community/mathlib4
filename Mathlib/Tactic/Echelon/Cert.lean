/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.LinearAlgebra.Matrix.Echelon.Decomposition  -- shake: keep (Qq dependency)
public import Mathlib.Tactic.Echelon.Core
public import Mathlib.Tactic.Echelon.Reflection  -- shake: keep (Qq dependency)
public import Mathlib.Tactic.Matrix.MulExpand
public import Mathlib.Util.Qq
public meta import Mathlib.Tactic.Echelon.Core
public meta import Mathlib.Tactic.Matrix.MulExpand

/-!
# Certificate construction for the Bareiss decomposition

`certifyDecomposition` builds the `Echelon.Decomposition` certificate from the decomposition
data, proving each certificate condition by kernel evaluation, or from proofs of the
individual entries supplied by an entry certifier.

## Main definitions

- `certifyDecomposition`: build the `Echelon.Decomposition` certificate of a matrix literal.
- `mkMatrixViews`: elaborate the row list of a matrix literal and its `ofLists` term.
- `mkPerm`, `mkPivotList`: elaborate the row permutation and the pivot list.

## Implementation notes

The elimination records its echelon form `U`, making the product a certificate obligation
of its own, `L * A_σ = U`, decided separately from the pivot condition on `U`.

The product is proved on the row lists of the literals: `ListMatrix.mul` on them is expanded
to the sums of products of the entries, which the certifier proves equal to the recorded
entries of `U`, and the equation of the matrix literals follows by a single definitional hint.
Stated entrywise on the matrices, every entry would carry indexed reads, which the kernel
evaluates by walking the literal.
-/

public meta section

open Lean Meta Qq Mathlib.Tactic.Matrix

namespace Mathlib.Tactic.Echelon

/-- Build the numeral of `i` in `Fin $n`. -/
def mkFinNumeral (n : ℕ) (i : ℕ) : MetaM Q(Fin $n) :=
  mkNumeral q(Fin $n) i

/-- Three views of one matrix literal. -/
structure MatrixViews (u : Level) (m n : ℕ) (α : Q(Type u)) where
  /-- The matrix, the `ofLists` term on `lit`. -/
  matrix : Q(Matrix (Fin $m) (Fin $n) $α)
  /-- The entries as a list of rows. -/
  lit : Q(List (List $α))
  /-- The row-major entries. -/
  entries : List (List Q($α))

/-- Build the `MatrixViews` of the row-major entries `rows`. -/
def mkMatrixViews {u : Level} {α : Q(Type u)} (_cr : Q(CommRing $α)) (m n : Nat)
    (rows : Array (Array Q($α))) : MatrixViews u m n α :=
  let entries := rows.toList.map Array.toList
  have lit : Q(List (List $α)) := mkListLitQ (α := q(List $α)) (entries.map mkListLitQ)
  { matrix := q(ofLists $m $n $lit), lit, entries }

/-- Build the list of pivot columns `[c₀, c₁, …]`. -/
def mkPivotList (n : Nat) (pivots : Array Nat) : MetaM Q(List (Fin $n)) := do
  let cols ← pivots.toList.mapM (mkFinNumeral n)
  return mkListLitQ (u := .zero) (α := q(Fin $n)) cols

/-- Build the permutation `σ = swap a₀ b₀ * swap a₁ b₁ * ⋯` from the recorded swaps. -/
def mkPerm (m : Nat) (swaps : Array (Nat × Nat)) : MetaM Q(Equiv.Perm (Fin $m)) := do
  let mut acc : Q(Equiv.Perm (Fin $m)) := q(Equiv.refl (Fin $m))
  for (a, b) in swaps do
    acc := q((Equiv.swap $(← mkFinNumeral m a) $(← mkFinNumeral m b)).trans $acc)
  return acc

/-- Prove `L.IsLowerTriangular` and `∀ i, L.diag i ≠ 0` from the rows of `L`, with `certifier`
proving the diagonal entries nonzero. -/
def certifyLowerTriangularDiag {u : Level} {m : ℕ} {α : Q(Type u)} (_cr : Q(CommRing $α))
    (L : MatrixViews u m m α) (certifier : EntryCertifier) :
    MetaM (Q(($(L.matrix)).IsLowerTriangular) × Q(∀ i, ($(L.matrix)).diag i ≠ 0)) := do
  have rows : Q(List (List $α)) := L.lit
  -- one cell per row: the nonzero diagonal entry, then the `Eq.refl` of the zeros after it
  let chain : Expr ← L.entries.zipIdx.foldrM (init := q(True.intro)) fun (row, k) rest => do
    have entry : Q($α) := row[k]!
    have c : Q(ℕ) := mkNatLit (m - (k + 1))
    let hz : Q(List.replicate $c (0 : $α) = List.replicate $c 0) := q(Eq.refl _)
    mkAppM ``And.intro #[← certifier q($entry ≠ 0), ← mkAppM ``And.intro #[hz, rest]]
  have h : Q(IsLowerTriangularDiag $m 0 $m $rows) := chain
  return (mkExpectedPropHint q(isLowerTriangular_ofLists $h) q(($(L.matrix)).IsLowerTriangular),
    mkExpectedPropHint q(diag_ofLists_ne_zero $h) q(∀ i, ($(L.matrix)).diag i ≠ 0))

/-- Prove `U.IsPivotedBy pivot` from the rows of `U` and the pivot list. -/
def certifyPivotedBy {u : Level} {m n : ℕ} {α : Q(Type u)} (_cr : Q(CommRing $α))
    (U : MatrixViews u m n α) (cols : Q(List (Fin $n))) (pivots : Array Nat)
    (certifier : EntryCertifier) : MetaM Q(($(U.matrix)).IsPivotedBy (pivotOfList $m $cols)) := do
  have rows : Q(List (List $α)) := U.lit
  have hinc : Q(isStrictlyIncreasing $cols = true) :=
    mkExpectedPropHint q(Eq.refl true) q(isStrictlyIncreasing $cols = true)
  -- the rows beyond the pivots are zero rows
  have r : Q(ℕ) := mkNatLit (m - pivots.size)
  let zeroRows : Expr := q(Eq.refl (List.replicate $r (List.replicate $n (0 : $α))))
  -- one cell per pivot row: the nonzero pivot entry, then the `Eq.refl` of the zeros before it
  let chain : Expr ← pivots.toList.zipIdx.foldrM (init := zeroRows) fun (p, i) rest => do
    have entry : Q($α) := (U.entries[i]!)[p]!
    have pQ : Q(ℕ) := mkNatLit p
    let hz : Q(List.replicate $pQ (0 : $α) = List.replicate $pQ 0) := q(Eq.refl _)
    mkAppM ``And.intro #[← certifier q($entry ≠ 0), ← mkAppM ``And.intro #[hz, rest]]
  have h : Q(IsPivotedList $n $cols $rows) := chain
  return mkExpectedPropHint q(isPivotedBy_ofLists (m := $m) $hinc $h)
    q(($(U.matrix)).IsPivotedBy (pivotOfList $m $cols))

/-- Prove the row arrangement `A.submatrix σ id = Aσ`. -/
def certifyPermEq {u : Level} {m n : ℕ} {α : Q(Type u)} (A : Q(Matrix (Fin $m) (Fin $n) $α))
    (Aσ : Q(Matrix (Fin $m) (Fin $n) $α)) (σ : Q(Equiv.Perm (Fin $m))) :
    MetaM Q(($A).submatrix $σ id = $Aσ) := do
  mkExpectedTypeHint
    q(congrArg (fun f => Matrix.of f) (FinVec.etaExpand_eq (fun i => $A ($σ i))).symm)
    q(($A).submatrix $σ id = $Aσ)

/-- Prove the product `L * Aσ = U` from the rows of the views. -/
def certifyProductEq {u : Level} {m n : ℕ} {α : Q(Type u)} (_cr : Q(CommRing $α))
    (L : MatrixViews u m m α) (Aσ U : MatrixViews u m n α) (certifier? : Option EntryCertifier) :
    MetaM Q($(L.matrix) * $(Aσ.matrix) = $(U.matrix)) := do
  let r := proveMul (← synthInstanceQ q(Zero $α)) (← synthInstanceQ q(Add $α))
    (← synthInstanceQ q(Mul $α)) m m n L.entries Aσ.entries
  have F : Q(List (List $α)) := r.expr
  have listU : Q(List (List $α)) := U.lit
  let hV : Q($F = $listU) ← match certifier? with
    | none => pure (mkExpectedPropHint q(Eq.refl $F) q($F = $listU))
    | some certifier => do
      let rowEqs ← r.rows.zipIdx.mapM fun (row, i) =>
        mkListCongr <$> row.zipIdx.mapM fun (fold, j) => do
          have entry : Q($α) := (U.entries[i]!)[j]!
          return ⟨fold, entry, ← certifier q($fold = $entry)⟩
      let ⟨_, _, h⟩ := mkListCongr (α := q(List $α)) rowEqs
      pure h
  let pf ← mkEqTrans
    (← mkEqSymm (← mkAppM ``ofLists_mul #[toExpr m, toExpr m, toExpr n, r.A, r.B]))
    (← mkCongrArg (← mkAppOptM ``ofLists #[α, none, toExpr m, toExpr n])
      (← mkEqTrans r.proof hV))
  return mkExpectedPropHint pf q($(L.matrix) * $(Aσ.matrix) = $(U.matrix))

/-- Build the `Echelon.Decomposition` certificate of `A` from the decomposition data and
`entries`, the parsed entries of `A`. -/
def certifyDecomposition {u : Level} {m n : ℕ} {α : Q(Type u)} (_cr : Q(CommRing $α))
    (A : Q(Matrix (Fin $m) (Fin $n) $α)) (entries : Array (Array Q($α)))
    (data : BareissData Expr) (certifier? : Option EntryCertifier) :
    MetaM Q(Echelon.Decomposition $A) := do
  have L := mkMatrixViews _cr m m data.L
  have U := mkMatrixViews _cr m n data.U
  let aEntries := data.rowOrder.map (entries[·]!)
  have Aσ := mkMatrixViews _cr m n aEntries
  let σ ← mkPerm m data.swaps
  let cols ← mkPivotList n data.pivot
  have Lm := L.matrix
  have Aσm := Aσ.matrix
  have Um := U.matrix
  let hperm ← certifyPermEq A Aσm σ
  have hprod : Q($Lm * $Aσm = $Um) := ← certifyProductEq _cr L Aσ U certifier?
  have hU : Q($Lm * ($A).submatrix $σ id = $Um) := q($hperm ▸ $hprod)
  let certifier := certifier?.getD mkDecideProofQ
  have hpivot : Q(($Um).IsPivotedBy (pivotOfList $m $cols)) :=
    ← certifyPivotedBy _cr U cols data.pivot certifier
  let ⟨hlower, hdiag⟩ ← certifyLowerTriangularDiag _cr L certifier
  have hlower : Q(($Lm).IsLowerTriangular) := hlower
  have hdiag : Q(∀ i, ($Lm).diag i ≠ 0) := hdiag
  return q(⟨$Lm, $σ, pivotOfList $m $cols, $hU ▸ $hpivot, $hlower, $hdiag⟩)

end Mathlib.Tactic.Echelon
