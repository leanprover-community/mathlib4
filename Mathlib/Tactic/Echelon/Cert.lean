/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Data.Fin.Tuple.Reflection  -- shake: keep (Qq dependency)
public import Mathlib.LinearAlgebra.Matrix.Echelon.Decomposition  -- shake: keep (Qq dependency)
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.Echelon.Core
public import Mathlib.Tactic.Matrix.MulExpand
public import Mathlib.Tactic.Matrix.OfLists  -- shake: keep (referenced by name)
public import Mathlib.Util.Qq
public meta import Mathlib.Tactic.Echelon.Core

import Mathlib.Data.List.OfFn

/-!
# Certificate construction for the Bareiss decomposition

`certifyDecomposition` builds the `Echelon.Decomposition` certificate from the decomposition
data, proving each certificate condition by kernel evaluation, or from proofs of the
individual entries supplied by an entry certifier.

## Main definitions

- `certifyDecomposition`: build the `Echelon.Decomposition` certificate of a matrix literal.
- `mkMatrixViews`: elaborate a matrix literal together with its entry view.
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

@[expose] public section

namespace Mathlib.Tactic.Echelon

/-! ### The pivot-function conditions in chain form

The pivot certificates defined in the theory file using `Monotone` and `StrictMonoOn` have
decidable instances but require `O(n^2)` comparisons, since they use the general decidable
instances from `Monotone` which check all pairs. The following part defines a `List.isChain`-based
alternative that can be decided in `O(n) comparisons`.
-/

variable {α : Type*} [Top α]

/-- One step of a pivot function: strictly increasing, with `⊤` absorbing. -/
def PivotStep [LT α] (a b : α) : Prop :=
  a < b ∨ a = ⊤ ∧ b = ⊤

instance [Preorder α] : IsTrans α PivotStep where
  trans a b c h₁ h₂ := by
    simp only [PivotStep] at *
    grind

instance [LT α] [i : ∀ a b : α, Decidable (a < b ∨ a = ⊤ ∧ b = ⊤)] :
    DecidableRel (PivotStep (α := α)) := i

/-- TODO: List.ofFn still brings up a O(n^2) construction. This can be improved by using a
list bridge eventually. -/
theorem isChain_ofFn_iff_monotone_and_strictMonoOn [PartialOrder α] {m : ℕ} (l : Fin m → α) :
    (List.ofFn l).IsChain PivotStep ↔ Monotone l ∧ StrictMonoOn l {i | l i ≠ ⊤} := by
  rw [List.isChain_iff_pairwise, List.pairwise_ofFn]
  simp only [PivotStep, Monotone, StrictMonoOn]
  grind [le_of_lt, LE.le.eq_or_lt]

/-! ### The pivot entry conditions as row sweeps

The entries before the pivot columns and the entries at them are collected along the rows, so
that the zero conditions reduce to one list equation and the nonzero conditions to one list of
entries. -/

section PivotSweeps

open Mathlib.Tactic.Matrix

variable {R : Type*} {n : ℕ}

/-- The entries of each row before its pivot column, collected row by row; a row whose pivot
is `⊤` contributes all its entries. -/
def pivotPrefixes : List (WithTop (Fin n)) → List (List R) → List R
  | [], _ => []
  | (p : Fin n) :: ps, rows => (rows.headD []).take p ++ pivotPrefixes ps rows.tail
  | none :: ps, rows => rows.headD [] ++ pivotPrefixes ps rows.tail

/-- The entry of each row at its pivot column, for the rows whose pivot is a column. -/
def pivotEntries [Zero R] : List (WithTop (Fin n)) → List (List R) → List R
  | [], _ => []
  | (p : Fin n) :: ps, rows => (rows.headD []).getD p 0 :: pivotEntries ps rows.tail
  | none :: ps, rows => pivotEntries ps rows.tail

theorem getD_eq_zero_of_pivotPrefixes [Zero R] {ps : List (WithTop (Fin n))}
    {rows : List (List R)} (h : ∀ x ∈ pivotPrefixes ps rows, x = 0) {i : ℕ} {j : Fin n}
    (hi : i < ps.length) (hj : (j : WithTop (Fin n)) < ps.getD i ⊤) :
    (rows.getD i []).getD j 0 = 0 := by
  induction ps generalizing rows i with
  | nil => simp at hi
  | cons p ps ih =>
    cases i with
    | zero =>
      rw [← List.headD_eq_getD, List.getD_eq_getElem?_getD]
      cases p with
      | coe q =>
        simp only [List.getD_cons_zero, WithTop.coe_lt_coe] at hj
        simp only [pivotPrefixes, List.mem_append] at h
        rw [← List.getElem?_take_of_lt hj]
        cases hx : ((rows.headD []).take q)[j]? with
        | none => rfl
        | some x => exact h x (Or.inl (List.mem_of_getElem? hx))
      | top =>
        simp only [pivotPrefixes, List.mem_append] at h
        cases hx : (rows.headD [])[j]? with
        | none => rfl
        | some x => exact h x (Or.inl (List.mem_of_getElem? hx))
    | succ i =>
      rw [List.getD_eq_getElem?_getD (l := rows), ← List.getElem?_tail,
        ← List.getD_eq_getElem?_getD]
      cases p with
      | coe q =>
        simp only [pivotPrefixes, List.mem_append] at h
        exact ih (fun x hx => h x (Or.inr hx)) (by simpa using hi) hj
      | top =>
        simp only [pivotPrefixes, List.mem_append] at h
        exact ih (fun x hx => h x (Or.inr hx)) (by simpa using hi) hj

theorem getD_ne_zero_of_pivotEntries [Zero R] {ps : List (WithTop (Fin n))}
    {rows : List (List R)} (h : ∀ x ∈ pivotEntries ps rows, x ≠ 0) {i : ℕ} {c : Fin n}
    (hc : ps.getD i ⊤ = c) : (rows.getD i []).getD c 0 ≠ 0 := by
  induction ps generalizing rows i with
  | nil => simp at hc
  | cons p ps ih =>
    cases i with
    | zero =>
      rw [List.getD_cons_zero] at hc
      subst hc
      rw [← List.headD_eq_getD]
      exact h _ (List.mem_cons_self ..)
    | succ i =>
      rw [List.getD_eq_getElem?_getD (l := rows), ← List.getElem?_tail,
        ← List.getD_eq_getElem?_getD]
      cases p with
      | coe q => exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) hc
      | top => exact ih h hc

theorem isPivotedBy_ofLists [Zero R] {m : ℕ} {rows : List (List R)}
    {pivot : Fin m → WithTop (Fin n)} {ps : List (WithTop (Fin n))} (hps : List.ofFn pivot = ps)
    (hchain : ps.IsChain PivotStep) {N : ℕ} (hzero : pivotPrefixes ps rows = List.replicate N 0)
    (hnz : ∀ x ∈ pivotEntries ps rows, x ≠ 0) : (ofLists m n rows).IsPivotedBy pivot := by
  have hmono := (isChain_ofFn_iff_monotone_and_strictMonoOn pivot).mp (hps ▸ hchain)
  refine Matrix.isPivotedBy_iff.mpr ⟨hmono.1, hmono.2, fun i => ?_⟩
  have hi : ps.getD i ⊤ = pivot i := by simp [← hps]
  refine ⟨fun j hj => ?_, fun c hc => ?_⟩
  · rw [ofLists_apply, ofList_apply]
    exact getD_eq_zero_of_pivotPrefixes (List.eq_replicate_iff.mp hzero).2 (by simp [← hps])
      (hi ▸ hj)
  · rw [ofLists_apply, ofList_apply]
    exact getD_ne_zero_of_pivotEntries hnz (hi.trans hc)

end PivotSweeps

end Mathlib.Tactic.Echelon

end

public meta section

open Lean Meta Qq Mathlib.Tactic.Matrix

namespace Mathlib.Tactic.Echelon

/-- Build the numeral of `i` in `Fin $n`. -/
def mkFinNumeral (n : ℕ) (i : ℕ) : MetaM Q(Fin $n) :=
  mkNumeral q(Fin $n) i

/-- Three views of one matrix literal: `entries` the row-major entries, `lit` the same entries
as a list of rows, and `matrix` that list read as a matrix by `ofLists`. -/
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

/-- The proof of `l.Forall p` from the proofs of `p x` at the entries `x` of `l`, in order. -/
def mkForallChain (proofs : List Expr) : MetaM Expr :=
  -- `Forall` ends with its last conjunct, so the chain is folded from the last proof
  match proofs.reverse with
  | [] => pure q(True.intro)
  | last :: rest => rest.foldlM (fun acc h => mkAppM ``And.intro #[h, acc]) last

/-- Prove `∀ i, L.diag i ≠ 0` from the recorded rows of `L`: the diagonal entries are nonzero
by `certifier?`, or by `decide` when there is none. -/
def certifyNonzeroDiag {u : Level} {m : ℕ} {α : Q(Type u)} (_cr : Q(CommRing $α))
    (L : MatrixViews u m m α) (certifier? : Option EntryCertifier) :
    MetaM Q(∀ i, ($(L.matrix)).diag i ≠ 0) := do
  have rows : Q(List (List $α)) := L.lit
  let hnz : Q(∀ x ∈ ListMatrix.diagonal 0 $m $rows, x ≠ 0) ← match certifier? with
    | none => mkDecideProofQ q(∀ x ∈ ListMatrix.diagonal 0 $m $rows, x ≠ 0)
    | some certifier => do
      let proofs ← L.entries.zipIdx.mapM fun (row, i) => do
        have entry : Q($α) := row[i]!
        certifier q($entry ≠ 0)
      have hForall : Q((ListMatrix.diagonal 0 $m $rows).Forall (· ≠ 0)) := ← mkForallChain proofs
      pure q(List.forall_iff_forall_mem.mp $hForall)
  -- `L.matrix` is the `ofLists` term on `rows`, so the hint is settled without reduction
  return mkExpectedPropHint q(diag_ofLists_ne_zero $rows $hnz) q(∀ i, ($(L.matrix)).diag i ≠ 0)

/-- Prove `L.IsLowerTriangular` from the recorded rows of `L`: the elimination emits literal
zeros above the diagonal, so the list of those entries reduces to the replicated zero. -/
def certifyLowerTriangular {u : Level} {m : ℕ} {α : Q(Type u)} (_cr : Q(CommRing $α))
    (L : MatrixViews u m m α) : MetaM Q(($(L.matrix)).IsLowerTriangular) := do
  have rows : Q(List (List $α)) := L.lit
  have n : Q(Nat) := mkNatLit (m * (m - 1) / 2)
  have hrep : Q(ListMatrix.aboveDiagonal 0 $rows = List.replicate $n (0 : $α)) :=
    mkExpectedPropHint q(Eq.refl (ListMatrix.aboveDiagonal 0 $rows))
      q(ListMatrix.aboveDiagonal 0 $rows = List.replicate $n (0 : $α))
  -- `BlockTriangular` spelled out (`toDual j < toDual i` is `i < j`)
  let prf : Q(∀ i j : Fin $m, OrderDual.toDual j < OrderDual.toDual i →
      ofLists $m $m $rows i j = 0) :=
    q(fun _ _ hij => ofLists_eq_zero_of_lt $rows (List.eq_replicate_iff.mp $hrep).2 hij)
  -- `L.matrix` is the `ofLists` term on `rows`, so the hint unfolds `IsLowerTriangular` only
  return mkExpectedPropHint prf q(($(L.matrix)).IsLowerTriangular)

/-- Prove `U.IsPivotedBy pivot` from the recorded rows of `U` and the pivot list: the entries
before the pivot columns are literal zeros, so their list reduces to the replicated zero; the
entries at the pivot columns are nonzero by `certifier?`, or by `decide` when there is none; and
the pivot-function conditions are decided on the pivot list in chain form. -/
def certifyPivotedBy {u : Level} {m n : ℕ} {α : Q(Type u)} (_cr : Q(CommRing $α))
    (U : MatrixViews u m n α) (pivot : Q(Fin $m → WithTop (Fin $n))) (pivots : Array Nat)
    (certifier? : Option EntryCertifier) : MetaM Q(($(U.matrix)).IsPivotedBy $pivot) := do
  have rows : Q(List (List $α)) := U.lit
  -- the pivot list, `⊤` on the rows the elimination left zero
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
  -- the entries before the pivot columns: the pivot column of a pivot row, the whole row otherwise
  let N := pivots.toList.sum + ((U.entries.drop pivots.size).map List.length).sum
  have nQ : Q(ℕ) := mkNatLit N
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
  -- `U.matrix` is the `ofLists` term on `rows`, so the hint is settled without reduction
  return mkExpectedPropHint q(isPivotedBy_ofLists $hps $hchain $hzero $hnz)
    q(($(U.matrix)).IsPivotedBy $pivot)

/-- Prove the row arrangement `A.submatrix σ id = Aσ` by reflection using `FinVec.etaExpand_eq`. -/
def certifyPermEq {u : Level} {m n : ℕ} {α : Q(Type u)} (A : Q(Matrix (Fin $m) (Fin $n) $α))
    (Aσ : Q(Matrix (Fin $m) (Fin $n) $α)) (σ : Q(Equiv.Perm (Fin $m))) :
    MetaM Q(($A).submatrix $σ id = $Aσ) := do
  mkExpectedTypeHint
    q(congrArg (fun f => Matrix.of f) (FinVec.etaExpand_eq (fun i => $A ($σ i))).symm)
    q(($A).submatrix $σ id = $Aσ)

/-- Prove the product `L * Aσ = U` from the literals' recorded entries: the product of the row
lists is expanded to the sums of products, which `certifier?` proves equal to the entries of `U`,
or the kernel evaluates when there is none. -/
def certifyProductEq {u : Level} {m n : ℕ} {α : Q(Type u)} (_cr : Q(CommRing $α))
    (L : MatrixViews u m m α) (Aσ U : MatrixViews u m n α) (certifier? : Option EntryCertifier) :
    MetaM Q($(L.matrix) * $(Aσ.matrix) = $(U.matrix)) := do
  let r := proveMul (← synthInstanceQ q(Zero $α)) (← synthInstanceQ q(Add $α))
    (← synthInstanceQ q(Mul $α)) m m n L.entries Aσ.entries
  have F : Q(List (List $α)) := r.expr
  have listU : Q(List (List $α)) := U.lit
  let hV : Q($F = $listU) ← match certifier? with
    | none =>
      -- the kernel evaluates the sums of products against the recorded entries
      pure (mkExpectedPropHint q(Eq.refl $F) q($F = $listU))
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
  -- `pf` is stated on the row lists `proveMul` built from the same entries as the views, so
  -- the hint is settled by a structural comparison of those lists with `L.lit` and `Aσ.lit`
  return mkExpectedPropHint pf q($(L.matrix) * $(Aσ.matrix) = $(U.matrix))

/-- Build the `Echelon.Decomposition` certificate of `A` from the decomposition data and
`entries`, the parsed entries of `A`, proving every condition by `decide` unless `certifier?`
supplies a certifier for the entry ones. -/
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
