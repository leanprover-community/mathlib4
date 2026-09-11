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
- `mkPerm`, `mkPivotLit`: elaborate the row permutation and the pivot function.

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

/-- Build the pivot literal `![↑c₀, …, ⊤, …] : Fin m → WithTop (Fin n)`, sending the
first rows to their pivot columns and the remaining rows to `⊤`. -/
def mkPivotLit (m n : Nat) (pivots : Array Nat) : MetaM Q(Fin $m → WithTop (Fin $n)) := do
  let entries : Array Q(WithTop (Fin $n)) ← Array.ofFnM (n := m) fun i => do
    if hi : i < pivots.size then
      return q(WithTop.some $(← mkFinNumeral n pivots[i]))
    else
      return q(⊤ : WithTop (Fin $n))
  return PiFin.mkLiteralQ (α := q(WithTop (Fin $n))) (n := m) fun i => entries[i]!

/-- Build the permutation `σ = swap a₀ b₀ * swap a₁ b₁ * ⋯` from the recorded swaps. -/
def mkPerm (m : Nat) (swaps : Array (Nat × Nat)) : MetaM Q(Equiv.Perm (Fin $m)) := do
  let mut acc : Q(Equiv.Perm (Fin $m)) := q(Equiv.refl (Fin $m))
  for (a, b) in swaps do
    acc := q((Equiv.swap $(← mkFinNumeral m a) $(← mkFinNumeral m b)).trans $acc)
  return acc

/-- The proof of `l.Forall p` from the proofs of `p x` along `l`, folded from the last proof
since `Forall` ends with its last conjunct. -/
def mkForallChain (proofs : List Expr) : MetaM Expr :=
  match proofs.reverse with
  | [] => pure q(True.intro)
  | last :: rest => rest.foldlM (fun acc h => mkAppM ``And.intro #[h, acc]) last

/-- Prove `∀ i, L.diag i ≠ 0` from the rows of `L`. -/
def certifyNonzeroDiag {u : Level} {m : ℕ} {α : Q(Type u)} (_cr : Q(CommRing $α))
    (L : MatrixViews u m m α) (certifier? : Option EntryCertifier) :
    MetaM Q(∀ i, ($(L.matrix)).diag i ≠ 0) := do
  have rows : Q(List (List $α)) := L.lit
  let hnz : Q(∀ x ∈ diag 0 $m $rows, x ≠ 0) ← match certifier? with
    | none => mkDecideProofQ q(∀ x ∈ diag 0 $m $rows, x ≠ 0)
    | some certifier => do
      let proofs ← L.entries.zipIdx.mapM fun (row, i) => do
        have entry : Q($α) := row[i]!
        certifier q($entry ≠ 0)
      have hForall : Q((diag 0 $m $rows).Forall (· ≠ 0)) := ← mkForallChain proofs
      pure q(List.forall_iff_forall_mem.mp $hForall)
  return mkExpectedPropHint q(diag_ofLists_ne_zero $hnz) q(∀ i, ($(L.matrix)).diag i ≠ 0)

/-- Prove `L.IsLowerTriangular` from the rows of `L`. -/
def certifyLowerTriangular {u : Level} {m : ℕ} {α : Q(Type u)} (_cr : Q(CommRing $α))
    (L : MatrixViews u m m α) : MetaM Q(($(L.matrix)).IsLowerTriangular) := do
  have rows : Q(List (List $α)) := L.lit
  have n : Q(Nat) := mkNatLit (m * (m - 1) / 2)
  have hrep : Q(aboveDiagonal 0 $rows = List.replicate $n (0 : $α)) :=
    mkExpectedPropHint q(Eq.refl (aboveDiagonal 0 $rows))
      q(aboveDiagonal 0 $rows = List.replicate $n (0 : $α))
  return mkExpectedPropHint q(isLowerTriangular_ofLists (m := $m) $hrep)
    q(($(L.matrix)).IsLowerTriangular)

/-- Prove `U.IsPivotedBy pivot` from the rows of `U` and the pivot list. -/
def certifyPivotedBy {u : Level} {m n : ℕ} {α : Q(Type u)} (_cr : Q(CommRing $α))
    (U : MatrixViews u m n α) (pivot : Q(Fin $m → WithTop (Fin $n))) (pivots : Array Nat)
    (certifier? : Option EntryCertifier) : MetaM Q(($(U.matrix)).IsPivotedBy $pivot) := do
  have rows : Q(List (List $α)) := U.lit
  let psEntries : List Q(WithTop (Fin $n)) ← (List.range m).mapM fun i => do
    if h : i < pivots.size then
      return q(WithTop.some $(← mkFinNumeral n pivots[i]))
    else
      return q(⊤ : WithTop (Fin $n))
  have ps : Q(List (WithTop (Fin $n))) :=
    mkListLitQ (u := .zero) (α := q(WithTop (Fin $n))) psEntries
  have hps : Q(List.ofFn $pivot = $ps) :=
    mkExpectedPropHint q(Eq.refl (List.ofFn $pivot)) q(List.ofFn $pivot = $ps)
  let hchain ← mkDecideProofQ q(($ps).IsChain PivotStep)
  let numBefore := pivots.toList.sum + ((U.entries.drop pivots.size).map List.length).sum
  have nQ : Q(ℕ) := mkNatLit numBefore
  have hzero : Q(pivotPrefixes $ps $rows = List.replicate $nQ (0 : $α)) :=
    mkExpectedPropHint q(Eq.refl (pivotPrefixes $ps $rows))
      q(pivotPrefixes $ps $rows = List.replicate $nQ (0 : $α))
  let hnz : Q(∀ x ∈ pivotEntries $ps $rows, x ≠ 0) ← match certifier? with
    | none => mkDecideProofQ q(∀ x ∈ pivotEntries $ps $rows, x ≠ 0)
    | some certifier => do
      let proofs ← pivots.toList.zipIdx.mapM fun (p, i) => do
        have entry : Q($α) := (U.entries[i]!)[p]!
        certifier q($entry ≠ 0)
      have hForall : Q((pivotEntries $ps $rows).Forall (· ≠ 0)) := ← mkForallChain proofs
      pure q(List.forall_iff_forall_mem.mp $hForall)
  return mkExpectedPropHint q(isPivotedBy_ofLists $hps $hchain $hzero $hnz)
    q(($(U.matrix)).IsPivotedBy $pivot)

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
  let pivot ← mkPivotLit m n data.pivot
  have Lm := L.matrix
  have Aσm := Aσ.matrix
  have Um := U.matrix
  let hperm ← certifyPermEq A Aσm σ
  have hprod : Q($Lm * $Aσm = $Um) := ← certifyProductEq _cr L Aσ U certifier?
  have hU : Q($Lm * ($A).submatrix $σ id = $Um) := q($hperm ▸ $hprod)
  have hpivot : Q(($Um).IsPivotedBy $pivot) := ← certifyPivotedBy _cr U pivot data.pivot certifier?
  have hlower : Q(($Lm).IsLowerTriangular) := ← certifyLowerTriangular _cr L
  have hdiag : Q(∀ i, ($Lm).diag i ≠ 0) := ← certifyNonzeroDiag _cr L certifier?
  return q(⟨$Lm, $σ, $pivot, $hU ▸ $hpivot, $hlower, $hdiag⟩)

end Mathlib.Tactic.Echelon
