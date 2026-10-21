/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public meta import Mathlib.Tactic.Echelon.Core
public meta import Mathlib.Tactic.Matrix.Cert
public import Mathlib.LinearAlgebra.Matrix.Echelon.Decomposition  -- shake: keep (Qq dependency)
public import Mathlib.Tactic.Echelon.Core
public import Mathlib.Tactic.Echelon.Reflection  -- shake: keep (Qq dependency)
public import Mathlib.Tactic.Matrix.Cert
public import Mathlib.Tactic.Matrix.Swaps  -- shake: keep (Qq dependency)

meta import Mathlib.Util.Qq

/-!
# Certificate construction for the Bareiss decomposition

`certifyDecomposition` constructs a proof of `Echelon.Decomposition A L σ pivot` from the given
decomposition data.
It proves that `L * A_σ` has the given pivots (through the product `L * A_σ = U`), and that `L`
is lower triangular with nonzero diagonal entries.

The `certify*` functions assemble these proofs from facts about single entries, including the
arithmetic equalities for the product and the non-zeroness for the diagonal entries of `L` and
the pivots of `U`, which are established by the model's certifier (or the kernel).

## Main definitions

- `certifyDecomposition`: builds the `Echelon.Decomposition` certificate from decomposition data.
- `DecompositionCert`: the internal certificate structure that includes the decomposition data,
  `U` and the product equation for downstream tactics.

## Implementation notes

The elimination records its echelon form `U`, making the product `L * A_σ = U` a certificate
obligation of its own.

The product is proved on the list representation which the kernel checks more cheaply.
-/

public meta section

open Lean Meta Qq Mathlib.Tactic.Matrix

namespace Mathlib.Tactic.Echelon

/-- Construct the list-based `IsLowerTriangularDiagList k c rows` cert. -/
def certifyLowerTriangularDiagList {u : Level} {α : Q(Type u)} (certifier : EntryCertifier α)
    (zα : Q(Zero $α)) (k c : Nat) (kQ cQ : Q(Nat)) (rows : Q(List (List $α))) :
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
    let rest ← certifyLowerTriangularDiagList certifier zα (k + 1) c k₁Q c₁Q rowsTl
    let hd ← certifier.neZero zα entry
    have hdrop : List.drop $kQ $row =Q $entry :: List.replicate $c₁Q (0 : $α) := ⟨⟩
    have : $cQ =Q $c₁Q + 1 := ⟨⟩
    have : $k₁Q =Q $kQ + 1 := ⟨⟩
    return q(IsLowerTriangularDiagList.cons $hdrop $hd $rest)

/-- Prove that `L` is lower triangular with a nonzero diagonal. -/
def certifyLowerTriangularDiag {u : Level} {m : Nat} {α : Q(Type u)}
    (certifier : EntryCertifier α) (zα : Q(Zero $α)) (L : ListMatrixLit α m m) :
    MetaM (Q(($(L.matrix)).IsLowerTriangular) × Q(∀ i, ($(L.matrix)).diag i ≠ 0)) := do
  let h ← certifyLowerTriangularDiagList certifier zα 0 m q(0) q($m) L.lit
  return (mkExpectedPropHint q(isLowerTriangular_ofLists $h) q(($(L.matrix)).IsLowerTriangular),
    mkExpectedPropHint q(diag_ofLists_ne_zero $h) q(∀ i, ($(L.matrix)).diag i ≠ 0))

/-- Construct the list-based `IsPivotedList pivots rows` cert. -/
def certifyPivotedList {u : Level} {n : Nat} {α : Q(Type u)} (certifier : EntryCertifier α)
    (zα : Q(Zero $α)) (cols : List Nat) (pivots : Q(List (Fin $n)))
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
    let rest ← certifyPivotedList certifier zα ks pivotsTl rowsTl
    let hd ← certifier.neZero zα entry
    have : $row =Q List.replicate ($pivot : Nat) 0 ++ $entry :: $suffix := ⟨⟩
    return q(IsPivotedList.cons rfl $hd $rest)

/-- Prove that `U` is pivoted by `pivotOfList pivots` from the rows of `U`, with `certifier`
proving the pivot entries nonzero. -/
def certifyPivotedBy {u : Level} {m n : Nat} {α : Q(Type u)} (certifier : EntryCertifier α)
    (zα : Q(Zero $α)) (U : ListMatrixLit α m n) (cols : List Nat) (pivots : Q(List (Fin $n))) :
    MetaM Q(($(U.matrix)).IsPivotedBy fun i : Fin $m ↦ pivotOfList $pivots i) := do
  let hsorted ← mkDecideProofQ q(($pivots).SortedLT)
  let h ← certifyPivotedList certifier zα cols pivots U.lit
  return mkExpectedPropHint q(isPivotedBy_ofLists (m := $m) $hsorted $h)
    q(($(U.matrix)).IsPivotedBy fun i : Fin $m ↦ pivotOfList $pivots i)

/-- An internal structure recording the `Echelon.Decomposition` certificate of `A` with its data,
together with the intermediate certificates that downstream tactics reuse (the echelon form `U`
and the product equation stated on it). -/
structure DecompositionCert {u : Level} {m n : Nat} {α : Q(Type u)} (rα : Q(CommRing $α))
    (A : Q(Matrix (Fin $m) (Fin $n) $α)) where
  /-- The transformation matrix. -/
  L : ListMatrixLit α m m
  /-- The row swaps. -/
  swaps : Q(List (Fin $m × Fin $m))
  /-- The pivot of the resulting echelon form. -/
  pivot : Q(Fin $m → WithTop (Fin $n))
  /-- The decomposition certificate from the theory. -/
  decomp : Q(Echelon.Decomposition $A $(L.matrix) (permOfSwaps $swaps) $pivot)
  /-- The echelon form. -/
  U : ListMatrixLit α m n
  /-- The product equation. -/
  mul_eq : Q($(L.matrix) * ($A).submatrix (permOfSwaps $swaps) id = $(U.matrix))

/-- Build the `DecompositionCert` of `A` from the decomposition data and the parsed entries
of `A`. -/
def certifyDecomposition {u : Level} {m n : Nat} {α : Q(Type u)}
    (certifier? : Option (EntryCertifier α)) (rα : Q(CommRing $α))
    (A : Q(Matrix (Fin $m) (Fin $n) $α)) (entries : Array (Array Q($α)))
    (data : BareissData Q($α)) : MetaM (DecompositionCert rα A) := do
  let zα : Q(Zero $α) ← synthInstanceQ q(Zero $α)
  let aα : Q(Add $α) ← synthInstanceQ q(Add $α)
  let mα : Q(Mul $α) ← synthInstanceQ q(Mul $α)
  let cα : Q(AddCommMonoid $α) ← synthInstanceQ q(AddCommMonoid $α)
  let swaps ← mkSwapsLitQ m data.swaps
  let σ : Q(Equiv.Perm (Fin $m)) := q(permOfSwaps $swaps)
  let cols := data.pivot.toList
  let pivots : Q(List (Fin $n)) := mkListLitQ (← cols.mapM (mkFinLitQ n))
  have pivot : Q(Fin $m → WithTop (Fin $n)) := q(fun i : Fin $m ↦ pivotOfList $pivots i)
  let lRows : List (List Q($α)) := data.L.toList.map Array.toList
  let aRows : List (List Q($α)) := (data.rowOrder.map (entries[·]!)).toList.map Array.toList
  let mulEq := proveMul zα aα mα m m n lRows aRows
  -- `L` and `Aσ` reuse the literals `proveMul` built.
  have Lm : Q(Matrix (Fin $m) (Fin $m) $α) := q(ofLists $m $m $(mulEq.A))
  let L : ListMatrixLit α m m := { matrix := Lm, lit := mulEq.A, rows := lRows }
  let Aσm : Q(Matrix (Fin $m) (Fin $n) $α) := q(ofLists $m $n $(mulEq.B))
  let U := ListMatrixLit.ofArray zα m n data.U
  let Um := U.matrix
  have hperm : Q(($A).submatrix $σ id = $Aσm) := certifyPermEq A Aσm σ
  let hprod : Q($Lm * $Aσm = $Um) ← certifyProductEq certifier? cα mulEq U
  let hU : Q($Lm * ($A).submatrix $σ id = $Um) := q($hperm ▸ $hprod)
  let certifier := certifier?.getD (decideCertifier α)
  let hpivot : Q(($Um).IsPivotedBy $pivot) ← certifyPivotedBy certifier zα U cols pivots
  let ⟨hlower, hdiag⟩ ← certifyLowerTriangularDiag certifier zα L
  assertInstancesCommute
  let decomp : Q(Echelon.Decomposition $A $Lm $σ $pivot) := q(⟨$hU ▸ $hpivot, $hlower, $hdiag⟩)
  return { L, swaps, pivot, decomp, U, mul_eq := hU }

end Mathlib.Tactic.Echelon
