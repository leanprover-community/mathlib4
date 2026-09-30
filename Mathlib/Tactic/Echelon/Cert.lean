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
public meta import Mathlib.Tactic.Echelon.Core
public meta import Mathlib.Tactic.Matrix.MulExpand
import Mathlib.Util.Qq

/-!
# Certificate construction for the Bareiss decomposition

`certifyDecomposition` builds the certificates of the conditions of an `Echelon.Decomposition`
from the decomposition data, proving each condition by kernel evaluation, or from proofs of the
individual entries supplied by an entry certifier.

## Implementation notes

The elimination records its echelon form `U`, making the product `L * A_σ = U` a certificate
obligation of its own.

The product is proved on the list representation which the kernel checks more cheaply.
-/

public meta section

open Lean Meta Qq Mathlib.Tactic.Matrix

namespace Mathlib.Tactic.Echelon

/-- Three views of one matrix literal. This makes the argument list more succinct when a cert
construction function needs to use multiple representations. -/
structure MatrixViews (u : Level) (m n : Nat) (α : Q(Type u)) where
  /-- The matrix, the `ofLists` term on `lit`. -/
  matrix : Q(Matrix (Fin $m) (Fin $n) $α)
  /-- The list literal of the rows. -/
  lit : Q(List (List $α))
  /-- The entries of `lit`. -/
  entries : List (List Q($α))

/-- The `MatrixViews` of the matrix with rows `rows`. -/
def MatrixViews.ofArray {u : Level} {α : Q(Type u)} (zα : Q(Zero $α)) (m n : Nat)
    (rows : Array (Array Q($α))) : MatrixViews u m n α :=
  let entries := rows.toList.map Array.toList
  let lit : Q(List (List $α)) := mkListLitQ (α := q(List $α)) (entries.map mkListLitQ)
  { matrix := q(ofLists $m $n $lit), lit, entries }

/-- Build the permutation `σ = swap a₀ b₀ * swap a₁ b₁ * ⋯` from the recorded swaps. -/
def mkPerm (m : Nat) (swaps : Array (Nat × Nat)) : MetaM Q(Equiv.Perm (Fin $m)) := do
  let mut acc : Q(Equiv.Perm (Fin $m)) := q(Equiv.refl (Fin $m))
  for (a, b) in swaps do
    acc := q((Equiv.swap $(← mkFinLitQ m a) $(← mkFinLitQ m b)).trans $acc)
  return acc

/-- Construct the list-based `IsLowerTriangularDiagList k c rows` cert. -/
def certifyLowerTriangularDiagList {u : Level} {α : Q(Type u)} (zα : Q(Zero $α))
    (certifier : EntryCertifier) (k c : Nat) (kQ cQ : Q(Nat)) (rows : Q(List (List $α))) :
    MetaM Q(IsLowerTriangularDiagList $kQ $cQ $rows) :=
  match c with
  | 0 => do
    have : $cQ =Q 0 := ⟨⟩
    return q(IsLowerTriangularDiagList.nil)
  | c + 1 => do
    let ⟨row, rowsTl, _⟩ ← unconsListLitQ rows
    let ⟨entry, _, _⟩ ← unconsListLitQ (dropListLitQ k row)
    have k₁Q : Q(Nat) := mkNatLitQ (k + 1)
    have c₁Q : Q(Nat) := mkNatLitQ c
    let rest ← certifyLowerTriangularDiagList zα certifier (k + 1) c k₁Q c₁Q rowsTl
    let hd : Q($entry ≠ 0) ← certifier q($entry ≠ 0)
    have hdrop : List.drop $kQ $row =Q $entry :: List.replicate $c₁Q (0 : $α) := ⟨⟩
    have : $cQ =Q $c₁Q + 1 := ⟨⟩
    have : $k₁Q =Q $kQ + 1 := ⟨⟩
    return q(IsLowerTriangularDiagList.cons $hdrop $hd $rest)

/-- Prove that `ofLists m m rows` is lower triangular with a nonzero diagonal. -/
def certifyLowerTriangularDiag {u : Level} {α : Q(Type u)} (zα : Q(Zero $α)) (m : Nat)
    (rows : Q(List (List $α))) (certifier : EntryCertifier) :
    MetaM (Q((ofLists $m $m $rows).IsLowerTriangular) ×
      Q(∀ i, (ofLists $m $m $rows).diag i ≠ 0)) := do
  let h ← certifyLowerTriangularDiagList zα certifier 0 m q(0) q($m) rows
  return (q(isLowerTriangular_ofLists $h), q(diag_ofLists_ne_zero $h))

/-- Construct the list-based `IsPivotedList pivots rows` cert. -/
def certifyPivotedList {u : Level} {n : Nat} {α : Q(Type u)} (zα : Q(Zero $α))
    (certifier : EntryCertifier) (cols : List Nat) (pivots : Q(List (Fin $n)))
    (rows : Q(List (List $α))) : MetaM Q(IsPivotedList $pivots $rows) :=
  match cols with
  | [] => do
    have hz : $rows =Q ($rows).map fun _ ↦ List.replicate $n (0 : $α) := ⟨⟩
    have : $pivots =Q ([] : List (Fin $n)) := ⟨⟩
    return q(IsPivotedList.nil $hz)
  | k :: ks => do
    let ⟨pivot, pivotsTl, _⟩ ← unconsListLitQ pivots
    let ⟨row, rowsTl, _⟩ ← unconsListLitQ rows
    let ⟨entry, suffix, _⟩ ← unconsListLitQ (dropListLitQ k row)
    let rest ← certifyPivotedList zα certifier ks pivotsTl rowsTl
    let hd : Q($entry ≠ 0) ← certifier q($entry ≠ 0)
    have : $row =Q List.replicate ($pivot : Nat) 0 ++ $entry :: $suffix := ⟨⟩
    return q(IsPivotedList.cons rfl $hd $rest)

/-- Prove that `U` is pivoted by `pivotOfList pivots` from the rows of `U`, with `certifier`
proving the pivot entries nonzero. -/
def certifyPivotedBy {u : Level} {m n : Nat} {α : Q(Type u)} (zα : Q(Zero $α))
    (U : MatrixViews u m n α) (cols : List Nat) (pivots : Q(List (Fin $n)))
    (certifier : EntryCertifier) :
    MetaM Q(($(U.matrix)).IsPivotedBy fun i : Fin $m ↦ pivotOfList $pivots i) := do
  let hsorted ← mkDecideProofQ q(($pivots).SortedLT)
  let h ← certifyPivotedList zα certifier cols pivots U.lit
  return mkExpectedPropHint q(isPivotedBy_ofLists (m := $m) $hsorted $h)
    q(($(U.matrix)).IsPivotedBy fun i : Fin $m ↦ pivotOfList $pivots i)

/-- Prove the row arrangement `A.submatrix σ id = Aσ`. -/
def certifyPermEq {u : Level} {m n : Nat} {α : Q(Type u)} (A : Q(Matrix (Fin $m) (Fin $n) $α))
    (Aσ : Q(Matrix (Fin $m) (Fin $n) $α)) (σ : Q(Equiv.Perm (Fin $m))) :
    Q(($A).submatrix $σ id = $Aσ) :=
  mkExpectedPropHint
    q(congrArg (fun f ↦ Matrix.of f) (FinVec.etaExpand_eq (fun i ↦ $A ($σ i))).symm)
    q(($A).submatrix $σ id = $Aσ)

/-- Prove the row literals of `rows₁` and `rows₂` equal from the entrywise equations `a = b`,
each proved by `certifier`. -/
def certifyRowsEq {u : Level} {α : Q(Type u)} (certifier : EntryCertifier)
    (rows₁ rows₂ : List (List Q($α))) :
    MetaM ((l₁ : Q(List (List $α))) × (l₂ : Q(List (List $α))) × Q($l₁ = $l₂)) := do
  let rowEqs ← rows₁.zipWithM (bs := rows₂) fun row₁ row₂ =>
    mkListCongr <$> row₁.zipWithM (bs := row₂) fun a b => do
      return ⟨a, b, ← certifier q($a = $b)⟩
  return mkListCongr (α := q(List $α)) rowEqs

/-- Prove the product `L * Aσ = U` from the expansion `mulEq` of the product of the row lists of
`L` and `Aσ`, whose literals are `mulEq.A` and `mulEq.B`. -/
def certifyProductEq {u : Level} {m n : Nat} {α : Q(Type u)} (cα : Q(AddCommMonoid $α))
    {zα : Q(Zero $α)} {aα : Q(Add $α)} {mα : Q(Mul $α)} (mulEq : MulEq zα aα mα m m n)
    (U : MatrixViews u m n α) (certifier? : Option EntryCertifier) :
    MetaM Q((ofLists $m $m $(mulEq.A)) * ofLists $m $n $(mulEq.B) = $(U.matrix)) := do
  let hmul : Q(ListMatrix.mul $m $m $n $(mulEq.A) $(mulEq.B) = $(U.lit)) ← match certifier? with
    | none =>
      -- Returns a proof with RHS being `mulEq.expr` without a bridge to `U.lit`.
      -- A model passes `none` when equality of its literals is settled by kernel
      -- evaluation, so the kernel establishes the defeq itself at `ofLists_mul`.
      pure mulEq.proof
    | some certifier => do
      let ⟨_, _, hrows⟩ ← certifyRowsEq certifier mulEq.rows U.entries
      mkEqTrans mulEq.proof hrows
  -- `hmul` is stated with the `Zero` and `Add` given to `proveMul`, while `ofLists_mul` uses those
  -- derived from `cα`.
  assertInstancesCommute
  return mkExpectedPropHint q(ofLists_mul $hmul)
    q((ofLists $m $m $(mulEq.A)) * ofLists $m $n $(mulEq.B) = $(U.matrix))

/-- An internal structure recording the `Echelon.Decomposition` certificate of `A` together with
the intermediate certificates that downstream tactics reuse (the echelon form `U` and the product
equation stated on it). -/
structure DecompositionCert {u : Level} {m n : Nat} {α : Q(Type u)} (rα : Q(CommRing $α))
    (A : Q(Matrix (Fin $m) (Fin $n) $α)) where
  /-- The decomposition certificate from the theory. -/
  decomp : Q(Echelon.Decomposition $A)
  /-- The views of the echelon form. -/
  U : MatrixViews u m n α
  /-- The product equation. -/
  mul_eq : Q(($decomp).L * ($A).submatrix ($decomp).σ id = $(U.matrix))

/-- Build the `DecompositionCert` of `A` from the decomposition data and the parsed entries
of `A`. -/
def certifyDecomposition {u : Level} {m n : Nat} {α : Q(Type u)} (rα : Q(CommRing $α))
    (A : Q(Matrix (Fin $m) (Fin $n) $α)) (entries : Array (Array Q($α)))
    (data : BareissData Expr) (certifier? : Option EntryCertifier) :
    MetaM (DecompositionCert rα A) := do
  let zα : Q(Zero $α) ← synthInstanceQ q(Zero $α)
  let aα : Q(Add $α) ← synthInstanceQ q(Add $α)
  let mα : Q(Mul $α) ← synthInstanceQ q(Mul $α)
  let cα : Q(AddCommMonoid $α) ← synthInstanceQ q(AddCommMonoid $α)
  let U := MatrixViews.ofArray zα m n data.U
  let σ ← mkPerm m data.swaps
  let cols := data.pivot.toList
  let pivots : Q(List (Fin $n)) := mkListLitQ (← cols.mapM (mkFinLitQ n))
  have pivot : Q(Fin $m → WithTop (Fin $n)) := q(fun i : Fin $m ↦ pivotOfList $pivots i)
  let lRows : List (List Q($α)) := data.L.toList.map Array.toList
  let aRows : List (List Q($α)) := (data.rowOrder.map (entries[·]!)).toList.map Array.toList
  let mulEq := proveMul zα aα mα m m n lRows aRows
  -- `L` and `Aσ` reuse the literals `proveMul` built
  have Lm : Q(Matrix (Fin $m) (Fin $m) $α) := q(ofLists $m $m $(mulEq.A))
  let Aσm : Q(Matrix (Fin $m) (Fin $n) $α) := q(ofLists $m $n $(mulEq.B))
  let Um := U.matrix
  have hperm : Q(($A).submatrix $σ id = $Aσm) := certifyPermEq A Aσm σ
  let hprod : Q($Lm * $Aσm = $Um) ← certifyProductEq cα mulEq U certifier?
  let hU : Q($Lm * ($A).submatrix $σ id = $Um) := q($hperm ▸ $hprod)
  let certifier := certifier?.getD mkDecideProofQ
  let hpivot : Q(($Um).IsPivotedBy $pivot) ← certifyPivotedBy zα U cols pivots certifier
  let ⟨hlower, hdiag⟩ ← certifyLowerTriangularDiag zα m mulEq.A certifier
  have hlower : Q(($Lm).IsLowerTriangular) := hlower
  have hdiag : Q(∀ i, ($Lm).diag i ≠ 0) := hdiag
  assertInstancesCommute
  let decomp : Q(Echelon.Decomposition $A) :=
    q(⟨$Lm, $σ, $pivot, $hU ▸ $hpivot, $hlower, $hdiag⟩)
  return { decomp, U, mul_eq := hU }

end Mathlib.Tactic.Echelon
