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

end Mathlib.Tactic.Echelon

end

public meta section

open Lean Meta Qq Mathlib.Tactic.Matrix

namespace Mathlib.Tactic.Echelon

/-- Build the numeral of `i` in `Fin $n`. -/
def mkFinNumeral (n : ℕ) (i : ℕ) : MetaM Q(Fin $n) :=
  mkNumeral q(Fin $n) i

/-- Two views of one matrix literal: `matrix` the elaborated term, and `entries` the
row-major entries it was built from. -/
structure MatrixViews (u : Level) (m n : ℕ) (α : Q(Type u)) where
  /-- The matrix literal. -/
  matrix : Q(Matrix (Fin $m) (Fin $n) $α)
  /-- The row-major entries. -/
  entries : Array (Array Q($α))

/-- Build the `MatrixViews` of the row-major entries `rows`. -/
def mkMatrixViews {u : Level} (α : Q(Type u)) (m n : Nat) (rows : Array (Array Q($α))) :
    MatrixViews u m n α :=
  { matrix := Matrix.mkLiteralQ (m := m) (n := n) (.of fun i j => (rows[i]!)[j]!),
    entries := rows }

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

/-- Prove the quantified statement `p` over a literal `Fin` domain from proofs of its
instances, `certifier i` proving it at index `i`. The proof recurses on the index list
`List.finRange n`, so the motive is spelled once rather than once per index. -/
def certifyForallFin (p : Q(Prop)) (certifier : Nat → (q : Q(Prop)) → MetaM Q($q)) :
    MetaM Q($p) :=
  forallBoundedTelescope p (some 1) fun is body => do
    let #[i] := is
      | throwError "expected a quantified statement:{indentExpr p}"
    let motive ← mkLambdaFVars is body
    let fin ← inferType i
    let_expr Fin nE := fin | throwError "expected a quantifier over `Fin`:{indentExpr p}"
    let some n ← getNatValue? nE
      | throwError "expected a literal `Fin` domain:{indentExpr p}"
    -- the conjunction takes its statement from the proofs, so that the one defeq check
    -- against the quantified goal is left to the kernel rather than run here as well; its
    -- innermost conjunct is the last proof itself, as `List.Forall` ends without a `True`
    let rec go (j : Nat) : MetaM Expr := do
      let h ← certifier j (mkApp motive (← mkNumeral fin j)).headBeta
      if j + 1 < n then mkAppM ``And.intro #[h, ← go (j + 1)] else pure h
    let acc ← if n == 0 then pure q(True.intro) else go 0
    have nQ : Q(ℕ) := nE
    have motiveQ : Q(Fin $nQ → Prop) := motive
    have forAll : Q((List.finRange $nQ).Forall $motiveQ) := acc
    mkExpectedTypeHint
      q(fun i => List.forall_iff_forall_mem.mp $forAll i (List.mem_finRange i)) p

/-- Prove an implication `P → Q` where the caller already knows from the recorded data
whether `P` holds, which saves a decision on `P` again. -/
def certifyImplication (holds : Bool) (p : Q(Prop)) (certifier : (q : Q(Prop)) → MetaM Q($q)) :
    MetaM Q($p) := do
  let .forallE nm dom body bi := p
    | throwError "expected an implication:{indentExpr p}"
  if body.hasLooseBVars then -- shouldn't happen, but a safety check
    throwError "the conclusion depends on the hypothesis:{indentExpr p}"
  if holds then
    return .lam nm dom (← certifier body) bi
  else
    have hyp : Q(Prop) := dom
    mkAppOptM ``Not.elim #[none, some body, ← mkDecideProofQ q(¬ $hyp)]

/-- Prove a defeq `p` by `rfl`. -/
def certifyDefEq (p : Q(Prop)) : MetaM Q($p) := do
  match_expr p with
  | Eq _ lhs _ => mkEqRefl lhs
  | _ => throwError "expected an equation:{indentExpr p}"

/-- Prove `∀ i, L.diag i ≠ 0` from the recorded entries of `L`. -/
def certifyNonzeroDiag {u : Level} {m : ℕ} {α : Q(Type u)} (_cr : Q(CommRing $α))
    (L : MatrixViews u m m α) (certifier : EntryCertifier) :
    MetaM Q(∀ i, ($(L.matrix)).diag i ≠ 0) := do
  let zero : Q($α) ← mkNumeral α 0
  certifyForallFin q(∀ i, ($(L.matrix)).diag i ≠ 0) fun i _ =>
    certifier q($((L.entries[i]!)[i]!) ≠ $zero)

/-- Prove `L.IsLowerTriangular` from the recorded rows of `L`: the elimination emits literal
zeros above the diagonal, so the list of those entries reduces to the replicated zero. -/
def certifyLowerTriangular {u : Level} {m : ℕ} {α : Q(Type u)} (_cr : Q(CommRing $α))
    (L : MatrixViews u m m α) : MetaM Q(($(L.matrix)).IsLowerTriangular) := do
  have rows : Q(List (List $α)) :=
    mkListLitQ (α := q(List $α)) (L.entries.toList.map fun row => mkListLitQ row.toList)
  have n : Q(Nat) := mkNatLit (m * (m - 1) / 2)
  have hrep : Q(ListMatrix.aboveDiagonal 0 $rows = List.replicate $n (0 : $α)) :=
    mkExpectedPropHint q(Eq.refl (ListMatrix.aboveDiagonal 0 $rows))
      q(ListMatrix.aboveDiagonal 0 $rows = List.replicate $n (0 : $α))
  -- `BlockTriangular` spelled out (`toDual j < toDual i` is `i < j`)
  let prf : Q(∀ i j : Fin $m, OrderDual.toDual j < OrderDual.toDual i →
      ofLists $m $m $rows i j = 0) :=
    q(fun _ _ hij => ofLists_eq_zero_of_lt $rows (List.eq_replicate_iff.mp $hrep).2 hij)
  -- `ofLists` on the row list unfolds to the `!![…]` literal
  return mkExpectedPropHint prf q(($(L.matrix)).IsLowerTriangular)

/-- Prove the characterisation of `U.IsPivotedBy pivot` via `isPivotedBy_iff`.
The first two conditions are decidable. The entry conditions require equality check against 0
and need to invoke the entry certifier to construct the non-zero proofs. -/
def certifyPivotedBy {u : Level} {m n : ℕ} {α : Q(Type u)} (_cr : Q(CommRing $α))
    (U : MatrixViews u m n α) (pivot : Q(Fin $m → WithTop (Fin $n))) (pivots : Array Nat)
    (certifier : EntryCertifier) : MetaM Q(($(U.matrix)).IsPivotedBy $pivot) := do
  let zero : Q($α) ← mkNumeral α 0
  let entryConds ← certifyForallFin
      q(∀ i, (∀ j : Fin $n, (j : WithTop (Fin $n)) < $pivot i → $(U.matrix) i j = 0) ∧
        ∀ c : Fin $n, $pivot i = c → $(U.matrix) i c ≠ 0) fun i p => do
    let_expr And zeros nonzeros := p
      | throwError "unexpected shape of the pivot entry conditions:{indentExpr p}"
    -- typed, so that the quotation below can read the context through the type of `hz`
    have zeros : Q(Prop) := zeros
    have nonzeros : Q(Prop) := nonzeros
    -- `pivot i` is the recorded column, or `⊤` on a row the elimination left zero
    let col? := if h : i < pivots.size then some pivots[i] else none
    let hz ← certifyForallFin zeros fun j cell =>
      certifyImplication (col?.all (j < ·)) cell certifyDefEq
    let hn ← certifyForallFin nonzeros fun c cell =>
      certifyImplication (col? == some c) cell fun _ =>
        certifier q($((U.entries[i]!)[c]!) ≠ $zero)
    mkAppM ``And.intro #[hz, hn]
  -- both pivot-function conditions are decided at once in their adjacent-pairs chain
  -- form, which reduces linearly along the list
  let hChain ← mkDecideProofQ q((List.ofFn $pivot).IsChain PivotStep)
  let hMonoStrict : Q(Monotone $pivot ∧ StrictMonoOn $pivot {i | $pivot i ≠ ⊤}) :=
    q((isChain_ofFn_iff_monotone_and_strictMonoOn $pivot).mp $hChain)
  return q(Matrix.isPivotedBy_iff.mpr ⟨($hMonoStrict).1, ($hMonoStrict).2, $entryConds⟩)

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
  let rows (entries : Array (Array Q($α))) : List (List Q($α)) := entries.toList.map Array.toList
  let r := proveMul (← synthInstanceQ q(Zero $α)) (← synthInstanceQ q(Add $α))
    (← synthInstanceQ q(Mul $α)) m m n (rows L.entries) (rows Aσ.entries)
  have F : Q(List (List $α)) := r.expr
  have listU : Q(List (List $α)) := mkListLitQ (α := q(List $α)) ((rows U.entries).map mkListLitQ)
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
  -- `pf` is stated on `ofLists` forms, which unfold on row-list literals to exactly the
  -- `Matrix.of`/`vecCons` terms of the literals, so the kernel settles the hint by reduction
  return mkExpectedPropHint pf q($(L.matrix) * $(Aσ.matrix) = $(U.matrix))

/-- Build the `Echelon.Decomposition` certificate of `A` from the decomposition data and
`entries`, the parsed entries of `A`, proving every condition by `decide` unless `certifier?`
supplies a certifier for the entry ones. -/
def certifyDecomposition {u : Level} {m n : ℕ} {α : Q(Type u)} (_cr : Q(CommRing $α))
    (A : Q(Matrix (Fin $m) (Fin $n) $α)) (entries : Array (Array Q($α)))
    (data : BareissData Expr) (certifier? : Option EntryCertifier) :
    MetaM Q(Echelon.Decomposition $A) := do
  have L := mkMatrixViews α m m data.L
  have U := mkMatrixViews α m n data.U
  let aEntries := data.rowOrder.map (entries[·]!)
  have Aσ := mkMatrixViews α m n aEntries
  let σ ← mkPerm m data.swaps
  let pivot ← mkPivotLit m n data.pivot
  let dispatch (p : Q(Prop)) (certify : EntryCertifier → MetaM Q($p)) : MetaM Q($p) :=
    match certifier? with
    | none => mkDecideProofQ p
    | some certifier => certify certifier
  have Lm := L.matrix
  have Aσm := Aσ.matrix
  have Um := U.matrix
  let hperm ← certifyPermEq A Aσm σ
  have hprod : Q($Lm * $Aσm = $Um) := ← certifyProductEq _cr L Aσ U certifier?
  have hU : Q($Lm * ($A).submatrix $σ id = $Um) := q($hperm ▸ $hprod)
  let hpivot ← dispatch q(($Um).IsPivotedBy $pivot) fun certifier =>
    certifyPivotedBy _cr U pivot data.pivot certifier
  have hlower : Q(($Lm).IsLowerTriangular) := ← certifyLowerTriangular _cr L
  let hdiag ← dispatch q(∀ i, ($Lm).diag i ≠ 0) fun certifier =>
    certifyNonzeroDiag _cr L certifier
  return q(⟨$Lm, $σ, $pivot, $hU ▸ $hpivot, $hlower, $hdiag⟩)

end Mathlib.Tactic.Echelon
