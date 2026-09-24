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

`certifyDecomposition` builds the certificates of the conditions of an `Echelon.Decomposition`
from the decomposition data, proving each condition by kernel evaluation, or from proofs of the
individual entries supplied by an entry certifier.

## Implementation notes

The elimination records its echelon form `U`, making the product `L * A_σ = U` a certificate
obligation of its own.

The product is proved on the row lists of the literals. `ListMatrix.mul` on them is expanded
to the sums of products of the entries, each proved equal to the recorded entry of `U` by the
entry certifier or by kernel evaluation, and the equation of the matrix literals follows by a
single definitional hint.
Stated entrywise on the matrices, every entry would carry indexed reads, which the kernel
evaluates by walking the literal.
-/

public meta section

open Lean Meta Qq Mathlib.Tactic.Matrix

namespace Mathlib.Tactic.Echelon

/-- Build the literal `⟨i, _⟩ : Fin n` with its bound decided. -/
def mkFinLit (n : Nat) (i : Nat) : MetaM Q(Fin $n) := do
  have iQ : Q(Nat) := mkNatLitQ i
  let hi : Q($iQ < $n) ← mkDecideProofQ q($iQ < $n)
  return q((⟨$iQ, $hi⟩ : Fin $n))

/-- The suffix of the list literal `l` after its first `k` cells. -/
def consDrop (l : Expr) : Nat → Expr
  | 0 => l
  | k + 1 => consDrop l.appArg! k

/-- Three views of one matrix literal. -/
structure MatrixViews (u : Level) (m n : Nat) (α : Q(Type u)) where
  /-- The matrix, the `ofLists` term on `lit`. -/
  matrix : Q(Matrix (Fin $m) (Fin $n) $α)
  /-- The entries as a list of rows. -/
  lit : Q(List (List $α))
  /-- The row-major entries. -/
  entries : List (List Q($α))

/-- The `MatrixViews` of a matrix given as its list literal `lit` and its entries. -/
def MatrixViews.ofLit {u : Level} {α : Q(Type u)} (rα : Q(CommRing $α)) (m n : Nat)
    (lit : Q(List (List $α))) (entries : List (List Q($α))) : MatrixViews u m n α :=
  { matrix := q(ofLists $m $n $lit), lit, entries }

/-- Build the `MatrixViews` of the row-major entries `rows`. -/
def mkMatrixViews {u : Level} {α : Q(Type u)} (rα : Q(CommRing $α)) (m n : Nat)
    (rows : Array (Array Q($α))) : MatrixViews u m n α :=
  let entries := rows.toList.map Array.toList
  .ofLit rα m n (mkListLitQ (α := q(List $α)) (entries.map mkListLitQ)) entries

/-- Build the list of pivot columns `[c₀, c₁, …]`, each with its bound. -/
def mkPivotList (n : Nat) (pivots : Array Nat) : MetaM Q(List (Fin $n)) := do
  let cols ← pivots.toList.mapM (mkFinLit n)
  return mkListLitQ (u := .zero) (α := q(Fin $n)) cols

/-- Build the permutation `σ = swap a₀ b₀ * swap a₁ b₁ * ⋯` from the recorded swaps. -/
def mkPerm (m : Nat) (swaps : Array (Nat × Nat)) : MetaM Q(Equiv.Perm (Fin $m)) := do
  let mut acc : Q(Equiv.Perm (Fin $m)) := q(Equiv.refl (Fin $m))
  for (a, b) in swaps do
    acc := q((Equiv.swap $(← mkFinLit m a) $(← mkFinLit m b)).trans $acc)
  return acc

/-- Prove `L.IsLowerTriangular` and `∀ i, L.diag i ≠ 0` from the rows of `L`, with `certifier`
proving the diagonal entries nonzero. -/
def certifyLowerTriangularDiag {u : Level} {m : Nat} {α : Q(Type u)} (rα : Q(CommRing $α))
    (L : MatrixViews u m m α) (certifier : EntryCertifier) :
    MetaM (Q(($(L.matrix)).IsLowerTriangular) × Q(∀ i, ($(L.matrix)).diag i ≠ 0)) := do
  have rows : Q(List (List $α)) := L.lit
  -- one cell per row: the nonzero diagonal entry, then the `Eq.refl` of the zeros after it
  let chain : Expr ← L.entries.zipIdx.foldrM (init := q(True.intro)) fun (row, k) rest => do
    have entry : Q($α) := row[k]!
    have c : Q(Nat) := mkNatLitQ (m - (k + 1))
    mkAppM ``And.intro #[← certifier q($entry ≠ 0),
      ← mkAppM ``And.intro #[q(Eq.refl (List.replicate $c (0 : $α))), rest]]
  have h : Q(IsLowerTriangularDiagList 0 $m $rows) := chain
  return (mkExpectedPropHint q(isLowerTriangular_ofLists $h) q(($(L.matrix)).IsLowerTriangular),
    mkExpectedPropHint q(diag_ofLists_ne_zero $h) q(∀ i, ($(L.matrix)).diag i ≠ 0))

/-- Prove `U.IsPivotedBy pivot` from the rows of `U` and the pivot list. -/
def certifyPivotedBy {u : Level} {m n : Nat} {α : Q(Type u)} (rα : Q(CommRing $α))
    (U : MatrixViews u m n α) (cols : Q(List (Fin $n))) (pivots : Array Nat)
    (certifier : EntryCertifier) :
    MetaM Q(($(U.matrix)).IsPivotedBy fun i : Fin $m ↦ pivotOfList $cols i) := do
  have rows : Q(List (List $α)) := U.lit
  let hsorted ← mkDecideProofQ q(($cols).SortedLT)
  -- one cell per pivot row, the nonzero pivot entry and the `Eq.refl` of the zeros before it, on
  -- the `Eq.refl` of the zero rows beyond the pivots
  have tail : Q(List (List $α)) := consDrop U.lit pivots.size
  let zeroRows := q(Eq.refl $tail)
  let chain : Expr ← pivots.toList.zipIdx.foldrM (init := zeroRows) fun (k, i) rest => do
    have entry : Q($α) := (U.entries[i]!)[k]!
    have kQ : Q(Nat) := mkNatLitQ k
    mkAppM ``And.intro #[← certifier q($entry ≠ 0),
      ← mkAppM ``And.intro #[q(Eq.refl (List.replicate $kQ (0 : $α))), rest]]
  have h : Q(IsPivotedList $cols $rows) := chain
  return mkExpectedPropHint q(isPivotedBy_ofLists (m := $m) $hsorted $h)
    q(($(U.matrix)).IsPivotedBy fun i : Fin $m ↦ pivotOfList $cols i)

/-- Prove the row arrangement `A.submatrix σ id = Aσ`. -/
def certifyPermEq {u : Level} {m n : Nat} {α : Q(Type u)} (A : Q(Matrix (Fin $m) (Fin $n) $α))
    (Aσ : Q(Matrix (Fin $m) (Fin $n) $α)) (σ : Q(Equiv.Perm (Fin $m))) :
    Q(($A).submatrix $σ id = $Aσ) :=
  mkExpectedPropHint
    q(congrArg (fun f ↦ Matrix.of f) (FinVec.etaExpand_eq (fun i ↦ $A ($σ i))).symm)
    q(($A).submatrix $σ id = $Aσ)

/-- Prove the row literals of `rows₁` and `rows₂` equal from the entrywise equations `a = b`,
each proved by `certifier`. Returns the two literals with the proof. -/
def certifyRowsEq {u : Level} {α : Q(Type u)} (certifier : EntryCertifier)
    (rows₁ rows₂ : List (List Q($α))) :
    MetaM ((l₁ : Q(List (List $α))) × (l₂ : Q(List (List $α))) × Q($l₁ = $l₂)) := do
  let rowEqs ← rows₁.zipWithM (bs := rows₂) fun row₁ row₂ =>
    mkListCongr <$> row₁.zipWithM (bs := row₂) fun a b => do
      return ⟨a, b, ← certifier q($a = $b)⟩
  return mkListCongr (α := q(List $α)) rowEqs

/-- Prove the product `L * Aσ = U` from the expansion `mulEq` of the product of the row lists of
`L` and `Aσ`, whose literals are `mulEq.A` and `mulEq.B`. -/
def certifyProductEq {u : Level} {m n : Nat} {α : Q(Type u)} (rα : Q(CommRing $α))
    {zα : Q(Zero $α)} {aα : Q(Add $α)} {mα : Q(Mul $α)} (mulEq : MulEq zα aα mα m m n)
    (U : MatrixViews u m n α) (certifier? : Option EntryCertifier) :
    MetaM Q((ofLists $m $m $(mulEq.A)) * ofLists $m $n $(mulEq.B) = $(U.matrix)) := do
  let hmul : Q(ListMatrix.mul $m $m $n $(mulEq.A) $(mulEq.B) = $(U.lit)) ← match certifier? with
    | none =>
      -- Returns a proof with RHS being `mulEq.expr` without a bridge to
      -- `U.lit`. A model passes `none` when equality of its literals is settled by kernel
      -- evaluation, so the kernel establishes the defeq itself at the closing hint entry-wise
      -- under `ofLists`.
      pure mulEq.proof
    | some certifier => do
      let ⟨_, _, hrows⟩ ← certifyRowsEq certifier mulEq.rows U.entries
      mkEqTrans mulEq.proof hrows
  let pf ← mkAppM ``ofLists_mul #[hmul]
  return mkExpectedPropHint pf
    q((ofLists $m $m $(mulEq.A)) * ofLists $m $n $(mulEq.B) = $(U.matrix))

/-- The certificates of a decomposition with the terms they are stated on. Every intermediate
certificate is kept, beyond the part `Echelon.Decomposition` exposes, so downstream tactics need
not rebuild them. -/
structure DecompositionCert {u : Level} {m n : Nat} {α : Q(Type u)} (rα : Q(CommRing $α))
    (A : Q(Matrix (Fin $m) (Fin $n) $α)) where
  /-- The transformation matrix. -/
  L : Q(Matrix (Fin $m) (Fin $m) $α)
  /-- The row permutation. -/
  σ : Q(Equiv.Perm (Fin $m))
  /-- The pivot function of the echelon form. -/
  pivot : Q(Fin $m → WithTop (Fin $n))
  /-- The echelon form. -/
  U : Q(Matrix (Fin $m) (Fin $n) $α)
  /-- The product equation. -/
  mul_eq : Q($L * ($A).submatrix $σ id = $U)
  /-- The pivot condition of the echelon form. -/
  isPivotedBy : Q(($U).IsPivotedBy $pivot)
  /-- Lower triangularity of the transformation matrix. -/
  L_lowerTriangular : Q(($L).IsLowerTriangular)
  /-- The nonzero diagonal of the transformation matrix. -/
  L_diag_ne_zero : Q(∀ i, ($L).diag i ≠ 0)

/-- The `Echelon.Decomposition` certificate assembled from the parts. -/
def DecompositionCert.toDecomposition {u : Level} {m n : Nat} {α : Q(Type u)}
    {rα : Q(CommRing $α)}
    {A : Q(Matrix (Fin $m) (Fin $n) $α)} (cert : DecompositionCert rα A) :
    Q(Echelon.Decomposition $A) :=
  -- the fields as locals: Qq identifies a spliced term only by its variable
  let ⟨L, σ, pivot, _U, mul_eq, isPivotedBy, L_lowerTriangular, L_diag_ne_zero⟩ := cert
  q(⟨$L, $σ, $pivot, $mul_eq ▸ $isPivotedBy, $L_lowerTriangular, $L_diag_ne_zero⟩)

/-- Build the `DecompositionCert` of `A` from the decomposition data and the parsed entries
of `A`. -/
def certifyDecomposition {u : Level} {m n : Nat} {α : Q(Type u)} (rα : Q(CommRing $α))
    (A : Q(Matrix (Fin $m) (Fin $n) $α)) (entries : Array (Array Q($α)))
    (data : BareissData Expr) (certifier? : Option EntryCertifier) :
    MetaM (DecompositionCert rα A) := do
  let zα : Q(Zero $α) ← synthInstanceQ q(Zero $α)
  let aα : Q(Add $α) ← synthInstanceQ q(Add $α)
  let mα : Q(Mul $α) ← synthInstanceQ q(Mul $α)
  let lRows : List (List Q($α)) := data.L.toList.map Array.toList
  let aRows : List (List Q($α)) := (data.rowOrder.map (entries[·]!)).toList.map Array.toList
  -- `proveMul` first, so that the views of `L` and `Aσ` are stated on the literals it built
  let mulEq := proveMul zα aα mα m m n lRows aRows
  have L := MatrixViews.ofLit rα m m mulEq.A lRows
  have Aσ := MatrixViews.ofLit rα m n mulEq.B aRows
  have U := mkMatrixViews rα m n data.U
  let σ ← mkPerm m data.swaps
  let cols : Q(List (Fin $n)) ← mkPivotList n data.pivot
  let pivot : Q(Fin $m → WithTop (Fin $n)) := q(fun i : Fin $m ↦ pivotOfList $cols i)
  have Lm := L.matrix
  have Aσm := Aσ.matrix
  have Um := U.matrix
  have hperm : Q(($A).submatrix $σ id = $Aσm) := certifyPermEq A Aσm σ
  let hprod : Q($Lm * $Aσm = $Um) ← certifyProductEq rα mulEq U certifier?
  let hU : Q($Lm * ($A).submatrix $σ id = $Um) := q($hperm ▸ $hprod)
  let certifier := certifier?.getD mkDecideProofQ
  let hpivot : Q(($Um).IsPivotedBy $pivot) ← certifyPivotedBy rα U cols data.pivot certifier
  let ⟨hlower, hdiag⟩ ← certifyLowerTriangularDiag rα L certifier
  have hlower : Q(($Lm).IsLowerTriangular) := hlower
  have hdiag : Q(∀ i, ($Lm).diag i ≠ 0) := hdiag
  return { L := Lm, σ, pivot, U := Um, mul_eq := hU, isPivotedBy := hpivot,
           L_lowerTriangular := hlower, L_diag_ne_zero := hdiag }

end Mathlib.Tactic.Echelon
