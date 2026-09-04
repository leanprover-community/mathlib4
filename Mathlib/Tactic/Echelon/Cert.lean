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
public import Mathlib.Util.Qq

/-!
# Certificate construction for the Bareiss decomposition

`certifyDecomposition` builds the `Echelon.Decomposition` certificate from the decomposition
data, proving each certificate condition by `decide`, or from proofs of the
individual entries supplied by an entry certifier.

## Main definitions

- `certifyDecomposition`: build the `Echelon.Decomposition` certificate of a matrix literal.
- `mkMatrixViews`: elaborate a matrix literal together with its entry view.
- `mkPerm`, `mkPivotLit`: elaborate the row permutation and the pivot function.

## Implementation notes

The elimination records its echelon form `U`, making the product a certificate obligation
of its own, `L * A_σ = U`, decided separately from the pivot condition on `U`. On the
certifier path this is built one entry at a time. `norm_num` does close it today (via
@[simp] rewrites), but is several times slower and does not handle some edge cases
(e.g. 0x0).

Once a list-based matrix multiplication exists, the better route is to prove the product
condition of the list representation and bridge it to the matrix-based version, leaving only
the per-entry arithmetic evidence to the certifier.
-/

public meta section

open Lean Meta Qq

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

/-- Prove that a recorded `entry` is nonzero by having `certifier` refute its equation with
`zero`; `site` names the entry in errors. -/
def certifyNonzeroEntry {u : Level} {α : Q(Type u)} (certifier : EntryCertifier)
    (entry zero : Q($α)) (site : MessageData) : MetaM Q($entry ≠ $zero) := do
  let (b, prf) ← certifier q($entry = $zero)
  if b then throwError "{site} is zero"
  return prf

/-- Prove `∀ i, L.diag i ≠ 0` from the recorded entries of `L`. -/
def certifyNonzeroDiag {u : Level} {m : ℕ} {α : Q(Type u)} (_cr : Q(CommRing $α))
    (L : MatrixViews u m m α) (certifier : EntryCertifier) :
    MetaM Q(∀ i, ($(L.matrix)).diag i ≠ 0) := do
  let zero : Q($α) ← mkNumeral α 0
  certifyForallFin q(∀ i, ($(L.matrix)).diag i ≠ 0) fun i _ =>
    certifyNonzeroEntry certifier (L.entries[i]!)[i]! zero
      m!"the diagonal entry of the transform at {i}"

/-- Prove `L.IsLowerTriangular`: the elimination emits literal zeros above the diagonal,
so every entry condition closes by `rfl`. -/
def certifyLowerTriangular {u : Level} {m : ℕ} {α : Q(Type u)} (_cr : Q(CommRing $α))
    (L : Q(Matrix (Fin $m) (Fin $m) $α)) : MetaM Q(($L).IsLowerTriangular) := do
  -- `BlockTriangular` spelled out (`toDual j < toDual i` is `i < j`), as the `reducible`
  -- ambient inside `simp` cannot unfold it
  let prf ← certifyForallFin
      q(∀ i j : Fin $m, OrderDual.toDual j < OrderDual.toDual i → $L i j = 0) fun i p => do
    certifyForallFin p fun j cell => certifyImplication (i < j) cell certifyDefEq
  return q($prf)

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
    -- `pivot i` is the recorded column, or `⊤` on a row the elimination left zero
    let col? := if h : i < pivots.size then some pivots[i] else none
    let hz ← certifyForallFin zeros fun j cell =>
      certifyImplication (col?.all (j < ·)) cell certifyDefEq
    let hn ← certifyForallFin nonzeros fun c cell =>
      certifyImplication (col? == some c) cell fun _ =>
        certifyNonzeroEntry certifier (U.entries[i]!)[c]! zero
          m!"the pivot entry at ({i}, {c})"
    mkAppM ``And.intro #[hz, hn]
  let hMono ← mkDecideProofQ q(Monotone $pivot)
  let hStrict ← mkDecideProofQ q(StrictMonoOn $pivot {i | $pivot i ≠ ⊤})
  return q(Matrix.isPivotedBy_iff.mpr ⟨$hMono, $hStrict, $entryConds⟩)

/-- Prove the row arrangement `A.submatrix σ id = Aσ` by reflection using `FinVec.etaExpand_eq`. -/
def certifyPermEq {u : Level} {m n : ℕ} {α : Q(Type u)} (A : Q(Matrix (Fin $m) (Fin $n) $α))
    (Aσ : Q(Matrix (Fin $m) (Fin $n) $α)) (σ : Q(Equiv.Perm (Fin $m))) :
    MetaM Q(($A).submatrix $σ id = $Aσ) := do
  mkExpectedTypeHint
    q(congrArg (fun f => Matrix.of f) (FinVec.etaExpand_eq (fun i => $A ($σ i))).symm)
    q(($A).submatrix $σ id = $Aσ)

/-- Prove the product `L * Aσ = U` entrywise from the literals' recorded entries. At
concrete indices the product reduces to the fold of its terms, which `certifier` settles
against the entry of `U`. -/
def certifyProductEq {u : Level} {m n : ℕ} {α : Q(Type u)} (_cr : Q(CommRing $α))
    (L : MatrixViews u m m α) (Aσ U : MatrixViews u m n α) (certifier : EntryCertifier) :
    MetaM Q($(L.matrix) * $(Aσ.matrix) = $(U.matrix)) := do
  have zero : Q($α) := ← mkNumeral α 0
  -- synthesised once, so that every cell references one instance node rather than rebuilding
  -- the projection path from `_cr`
  have _hmul : Q(HMul $α $α $α) := ← synthInstanceQ q(HMul $α $α $α)
  have _hadd : Q(HAdd $α $α $α) := ← synthInstanceQ q(HAdd $α $α $α)
  let cell (i j : Nat) : MetaM Expr := do
    let terms : Array Q($α) := Array.ofFn (n := m) fun c =>
      q($((L.entries[i]!)[c]!) * $((Aσ.entries[c]!)[j]!))
    -- the fold must reproduce what `(L * Aσ) i j` expands to
    have sum : Q($α) := terms.foldr (fun t acc => q($t + $acc)) zero
    have entry : Q($α) := (U.entries[i]!)[j]!
    let (b, prf) ← certifier q($sum = $entry)
    unless b do
      throwError "the product of the transform does not match the echelon form at ({i}, {j})"
    return prf
  return q(Matrix.ext $(← certifyForallFin
      q(∀ i j, ($(L.matrix) * $(Aσ.matrix)) i j = $(U.matrix) i j) fun i p => do
    certifyForallFin p fun j _ => cell i j))

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
  let hperm ← dispatch q(($A).submatrix $σ id = $Aσm) fun _ => certifyPermEq A Aσm σ
  let hprod ← dispatch q($Lm * $Aσm = $Um) fun certifier =>
    certifyProductEq _cr L Aσ U certifier
  have hU : Q($Lm * ($A).submatrix $σ id = $Um) := q($hperm ▸ $hprod)
  let hpivot ← dispatch q(($Um).IsPivotedBy $pivot) fun certifier =>
    certifyPivotedBy _cr U pivot data.pivot certifier
  let hlower ← dispatch q(($Lm).IsLowerTriangular) fun _ => certifyLowerTriangular _cr Lm
  let hdiag ← dispatch q(∀ i, ($Lm).diag i ≠ 0) fun certifier =>
    certifyNonzeroDiag _cr L certifier
  return q(⟨$Lm, $σ, $pivot, $hU ▸ $hpivot, $hlower, $hdiag⟩)

end Mathlib.Tactic.Echelon
