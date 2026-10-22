/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public meta import Mathlib.Tactic.Matrix.MulExpand
public import Mathlib.LinearAlgebra.Matrix.Array  -- shake: keep (Qq dependency)
public import Mathlib.Tactic.Matrix.MulExpand
public import Mathlib.Tactic.Matrix.OfLists  -- shake: keep (Qq dependency)


/-!
# Certificates for list-based matrix literals

This file contains common utilities for tactics that certify a computation on matrix literals from
proofs about the lists of their rows.

## Main definitions

- `certifyProductEq`: certify that the product of two matrix literals equals a third, given the
  expansion of the product by `MulExpand`.
- `certifyRowsEq`: certify the equality of two row literals from the equations of their entries.
- `decideCertifier`: the entry certifier that leaves each fact to the kernel's `decide`.
- `certifyOfArray`: certifies that the row-major array of a matrix literal is equal to the array of
  the matrix's entries.
-/

public meta section

open Lean Meta Qq

namespace Mathlib.Tactic.Matrix

/-- An entry certifier proves arithmetic facts about expressions of the ring `α` that the
certificates need. `eq` proves an equation `a = b`, such as an unreduced entry of a matrix
product equal to its computed value, and `neZero` proves `a ≠ 0`, such as for a pivot entry.

`eq` is typically built on a normalizer, while `neZero` may depend on bespoke methods if a
normalizer cannot provide a disequality proof.
-/
structure EntryCertifier {u : Level} (α : Q(Type u)) where
  /-- Prove `a = b`. -/
  eq (a b : Q($α)) : MetaM Q($a = $b)
  /-- Prove `a ≠ 0`, stated with the caller's `Zero` instance `zα`. -/
  neZero (zα : Q(Zero $α)) (a : Q($α)) : MetaM Q($a ≠ 0)

/-- Three forms of one list-based matrix literal. This makes the argument list more succinct when
a cert construction function needs to use multiple representations. -/
structure ListMatrixLit {u : Level} (α : Q(Type u)) (m n : Nat) where
  /-- The matrix, the `ofLists` term on `lit`. -/
  matrix : Q(Matrix (Fin $m) (Fin $n) $α)
  /-- The list literal of `rows`. -/
  lit : Q(List (List $α))
  /-- The rows of the matrix. -/
  rows : List (List Q($α))

/-- The `ListMatrixLit` of the matrix with rows `rows`. -/
def ListMatrixLit.ofRows {u : Level} {α : Q(Type u)} (zα : Q(Zero $α)) (m n : Nat)
    (rows : List (List Q($α))) : ListMatrixLit α m n :=
  let lit : Q(List (List $α)) := mkListLitQ (α := q(List $α)) (rows.map mkListLitQ)
  { matrix := q(ofLists $m $n $lit), lit, rows }

/-- The `ListMatrixLit` of the matrix with rows `rows`, given as an array of rows. -/
def ListMatrixLit.ofArray {u : Level} {α : Q(Type u)} (zα : Q(Zero $α)) (m n : Nat)
    (rows : Array (Array Q($α))) : ListMatrixLit α m n :=
  .ofRows zα m n (rows.toList.map Array.toList)

/-- The certifier that leaves each fact to the kernel's `decide`. -/
def decideCertifier {u : Level} (α : Q(Type u)) : EntryCertifier α where
  eq a b := mkDecideProofQ q($a = $b)
  neZero _zα a := mkDecideProofQ q($a ≠ 0)

/-- Prove the row literals of `rows₁` and `rows₂` equal from the entrywise equations `a = b`,
each proved by `certifier`. -/
def certifyRowsEq {u : Level} {α : Q(Type u)} (certifier : EntryCertifier α)
    (rows₁ rows₂ : List (List Q($α))) :
    MetaM ((l₁ : Q(List (List $α))) × (l₂ : Q(List (List $α))) × Q($l₁ = $l₂)) := do
  let rowEqs ← rows₁.zipWithM (bs := rows₂) fun row₁ row₂ =>
    mkListCongr <$> row₁.zipWithM (bs := row₂) fun a b => do
      return ⟨a, b, ← certifier.eq a b⟩
  return mkListCongr (α := q(List $α)) rowEqs

/-- Prove the product `ofLists mulEq.A * ofLists mulEq.B = U` from the list-based expansion of
`mulEq`. -/
def certifyProductEq {u : Level} {m n : Nat} {α : Q(Type u)}
    (certifier? : Option (EntryCertifier α)) (cα : Q(AddCommMonoid $α))
    {zα : Q(Zero $α)} {aα : Q(Add $α)} {mα : Q(Mul $α)} (mulEq : MulEq zα aα mα m m n)
    (U : ListMatrixLit α m n) :
    MetaM Q((ofLists $m $m $(mulEq.A)) * ofLists $m $n $(mulEq.B) = $(U.matrix)) := do
  let hmul : Q(ListMatrix.mul $m $m $n $(mulEq.A) $(mulEq.B) = $(U.lit)) ← match certifier? with
    | none =>
      -- Returns a proof with RHS being `mulEq.expr` without a bridge to `U.lit`.
      -- A caller passes `none` when equality of its literals is settled by kernel
      -- evaluation, so the kernel establishes the defeq itself at `ofLists_mul`.
      pure mulEq.proof
    | some certifier => do
      let ⟨_, _, hrows⟩ ← certifyRowsEq certifier mulEq.rows U.rows
      mkEqTrans mulEq.proof hrows
  -- `hmul` is stated with the `Zero` and `Add` given to `proveMul`, while `ofLists_mul` uses those
  -- derived from `cα`.
  assertInstancesCommute
  return mkExpectedPropHint q(ofLists_mul $hmul)
    q((ofLists $m $m $(mulEq.A)) * ofLists $m $n $(mulEq.B) = $(U.matrix))

/-- The literal of the row-major array of the entries of the matrix literal `L`. -/
def ListMatrixLit.array {u : Level} {m n : Nat} {α : Q(Type u)} (L : ListMatrixLit α m n) :
    Q(Array $α) :=
  q(List.toArray $(mkListLitQ L.rows.flatten))

/-- Prove that the row-major array of the `m × n` matrix literal `L` is the literal `L.array`. -/
def certifyOfArray {u : Level} {m n : Nat} {α : Q(Type u)} (zα : Q(Zero $α))
    (L : ListMatrixLit α m n) : MetaM Q(($(L.matrix)).toArray = $(L.array)) := do
  let l : Q(List $α) := mkListLitQ L.rows.flatten
  have : $(L.matrix) =Q ofLists $m $n $(L.lit) := ⟨⟩
  let hsize ← mkDecideProofQ q((List.toArray $l).size = $m * $n)
  let hrows ← mkDecideProofQ q(∀ row ∈ $(L.lit), row.length = $n)
  have hflat : Q(($(L.lit)).flatten = $l) :=
    mkExpectedPropHint q(Eq.refl $l) q(($(L.lit)).flatten = $l)
  return q(toArray_ofLists $hrows $hflat $hsize)

end Mathlib.Tactic.Matrix

end
