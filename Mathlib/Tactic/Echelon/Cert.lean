/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.LinearAlgebra.Matrix.Echelon.Decomposition  -- shake: keep (Qq dependency)
public import Mathlib.Tactic.Echelon.Core
public import Mathlib.Util.Qq

/-!
# Certificate construction for the Bareiss decomposition

The certificate constructor from the decomposition data, and the default certifier
`mkCertificate`, which proves the certificate conditions by `decide +kernel`, or from
proofs of the individual entries supplied by a leaf normaliser.

## Main definitions

- `mkCertificate`: build the `Echelon.Decomposition` certificate of a matrix literal.
- `LeafProver`: settle a proposition about a single entry.
- `mkPerm`, `mkPivotLit`, `mkRowsLit`, `mkMatrixLit`: elaborate the row permutation, the
  pivot function, and a matrix literal unwrapped or wrapped in `Matrix.of`.

## Implementation notes

The elimination records its echelon form `U`, making the product a certificate obligation
of its own, `L * A_σ = U`, decided separately from the pivot condition on `U`. On the leaf
path this is built one entry at a time, but should eventually be replaced by a dedicated
matrix mult normalising tactic, which is why `A_σ` is a literal. `norm_num` does close it
but is several times slower.

A quantifier over `Fin n` is discharged by recursion on `List.finRange n`, where the motive
is spelled once, rather than by chaining `Fin.forall_fin_succ`, which respells it at every
index.

Each condition maker takes both an elaborated term and the recorded data it was built from,
`U` with `data.U` and `pivot` with `data.pivot`: the term is what the statement names, while
the data is indexed for the entries and compared to decide the index guards. They cannot be
bundled, as a dependent return type can splice only plain binders.
-/

public meta section

open Lean Meta Qq

namespace Mathlib.Tactic.Echelon

/-- Build the numeral of `i` in `Fin $n`. -/
def mkFinNumeral (n : ℕ) (i : ℕ) : MetaM Q(Fin $n) :=
  mkNumeral q(Fin $n) i

/-- Build the row-function literal `![![a, b], ![c, d]]` of the row-major entries `rows`,
the function that a matrix literal wraps in `Matrix.of`. -/
def mkRowsLit {u : Level} (α : Q(Type u)) (m n : Nat) (rows : Array (Array Q($α))) :
    Q(Fin $m → Fin $n → $α) :=
  PiFin.mkLiteralQ (α := q(Fin $n → $α)) (n := m) fun i =>
    PiFin.mkLiteralQ (α := α) (n := n) fun j => (rows[i]!)[j]!

/-- Build the matrix literal of the row-major entries `rows`. -/
def mkMatrixLit {u : Level} (α : Q(Type u)) (m n : Nat) (rows : Array (Array Q($α))) :
    Q(Matrix (Fin $m) (Fin $n) $α) :=
  have elems := mkRowsLit α m n rows
  q(Matrix.of $elems)

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

/-- Prove the certificate condition `p` by a kernel-checked `decide`, with `name` naming
the condition in errors. -/
def certifyCondition (name : String) (p : Q(Prop)) : MetaM Q($p) := do
  let d ← mkDecide p
  let .ok r := Kernel.whnf (← getEnv) (← getLCtx) d
    | throwError "cannot verify the rank certificate: {name} does not reduce in the kernel"
  unless r.isConstOf ``Bool.true do
    throwError "cannot verify the rank certificate: {name} failed"
  mkDecideProofQ p

/-- A leaf normaliser settles a proposition about a single entry, returning its truth value
together with a proof of the proposition or of its negation. -/
@[expose] def LeafProver := Q(Prop) → MetaM (Bool × Expr)

/-- Prove the quantified statement `p` over `Fin n` from proofs of its instances, `proofAt i`
proving it at index `i`, unfolding `p` when its quantifier is behind a definition. The proof
recurses on the index list `List.finRange n`, so the motive is spelled once rather than once
per index. -/
def mkForallFin (n : Nat) (p : Q(Prop)) (proofAt : Nat → (q : Q(Prop)) → MetaM Q($q)) :
    MetaM Q($p) :=
  forallBoundedTelescope p (some 1) (whnfType := true) fun is body => do
    let #[i] := is
      | throwError "expected a quantified statement:{indentExpr p}"
    let motive ← mkLambdaFVars is body
    have fin : Q(Type) := q(Fin $n)
    let mut acc : Expr := mkConst ``True.intro
    for k in 0...n do
      let j := n - 1 - k
      let h ← proofAt j (mkApp motive (← mkNumeral fin j)).headBeta
      -- the conjunction takes its statement from the proofs, so that the one defeq check
      -- against the quantified goal is left to the kernel rather than run here as well
      acc ← if k == 0 then pure h else mkAppM ``And.intro #[h, acc]
    have range : Q(List (Fin $n)) := q(List.finRange $n)
    let hAll ← mkAppM ``Iff.mp
      #[← mkAppOptM ``List.forall_iff_forall_mem #[none, some motive, some range],
        ← mkExpectedTypeHint acc (← mkAppM ``List.Forall #[motive, range])]
    mkExpectedTypeHint
      (← mkLambdaFVars is (mkApp2 hAll i (← mkAppM ``List.mem_finRange #[i]))) p

/-- Prove an implication `P → Q` where the caller already knows from the recorded data
whether `P` holds, so that neither side is discovered by reduction: when it holds, `proof`
supplies `Q` and the hypothesis is discarded, and otherwise `P` is refuted and the
implication is vacuous. -/
def mkImplication (holds : Bool) (p : Q(Prop)) (proof : (q : Q(Prop)) → MetaM Q($q)) :
    MetaM Q($p) := do
  let .forallE nm dom body bi := p
    | throwError "expected an implication:{indentExpr p}"
  if body.hasLooseBVars then -- shouldn't happen, but a safety check
    throwError "the conclusion depends on the hypothesis:{indentExpr p}"
  if holds then
    return .lam nm dom (← proof body) bi
  else
    have hyp : Q(Prop) := dom
    mkAppOptM ``Not.elim #[none, some body, ← certifyCondition "an index guard" q(¬ $hyp)]

/-- Prove a cell whose two sides reduce to the same recorded entry. -/
def proveRflCell (p : Q(Prop)) : MetaM Q($p) := do
  match_expr p with
  | Eq _ lhs rhs =>
    unless ← isDefEq lhs rhs do
      throwError "the two sides do not reduce to the same recorded entry:{indentExpr p}"
    mkEqRefl lhs
  | _ => throwError "expected an equation:{indentExpr p}"

/-- Prove that a recorded `entry` is nonzero, by having `leaf` refute its equation with
`zero`; `site` names the entry in errors. -/
def proveNonzeroEntry {u : Level} {α : Q(Type u)} (leaf : LeafProver) (entry zero : Q($α))
    (site : MessageData) : MetaM Q($entry ≠ $zero) := do
  let (b, prf) ← leaf q($entry = $zero)
  if b then throwError "{site} is zero"
  return prf

/-- Prove `∀ i, L.diag i ≠ 0` from the recorded entries of `L`. -/
def mkDiagCond {u : Level} {m : ℕ} {α : Q(Type u)} (_cr : Q(CommRing $α))
    (L : Q(Matrix (Fin $m) (Fin $m) $α)) (entries : Array (Array Q($α))) (leaf : LeafProver) :
    MetaM Q(∀ i, ($L).diag i ≠ 0) := do
  let zero : Q($α) ← mkNumeral α 0
  mkForallFin m q(∀ i, ($L).diag i ≠ 0) fun i _ =>
    proveNonzeroEntry leaf (entries[i]!)[i]! zero m!"the diagonal entry of the transform at {i}"

/-- Prove `L.IsLowerTriangular`: above the diagonal the elimination emitted zero, and at
the remaining index pairs the triangularity guard is refutable. -/
def mkLowerCond {u : Level} {m : ℕ} {α : Q(Type u)} (_cr : Q(CommRing $α))
    (L : Q(Matrix (Fin $m) (Fin $m) $α)) : MetaM Q(($L).IsLowerTriangular) := do
  -- the unfolded guard is `toDual j < toDual i`, which is `i < j` in the original order
  mkForallFin m q(($L).IsLowerTriangular) fun i gi => do
    mkForallFin m gi fun j cell => mkImplication (i < j) cell proveRflCell

/-- Prove the characterisation of `U.IsPivotedBy pivot`: the two conditions on the pivot
function mention no entry and are decided, while the entry conditions are built from the
recorded entries of `U`. -/
def mkPivotCond {u : Level} {m n : ℕ} {α : Q(Type u)} (_cr : Q(CommRing $α))
    (U : Q(Matrix (Fin $m) (Fin $n) $α)) (entries : Array (Array Q($α)))
    (pivot : Q(Fin $m → WithTop (Fin $n))) (pivots : Array Nat) (leaf : LeafProver) :
    MetaM Q(($U).IsPivotedBy $pivot) := do
  let zero : Q($α) ← mkNumeral α 0
  let iff ← mkAppOptM ``Matrix.isPivotedBy_iff
    #[none, none, none, none, some U, some pivot, none, none]
  match_expr (← whnfR (← inferType iff)).appArg! with
  | And mono rest =>
    match_expr rest with
    | And strict cells =>
      let entryConds ← mkForallFin m cells fun i gi => do
        match_expr gi with
        | And zeros nonzeros =>
          -- `pivot i` is the recorded column, or `⊤` on a row the elimination left zero
          let col? := if h : i < pivots.size then some pivots[i] else none
          let hz ← mkForallFin n zeros fun j cell =>
            mkImplication (col?.all (j < ·)) cell proveRflCell
          let hn ← mkForallFin n nonzeros fun c cell =>
            mkImplication (col? == some c) cell fun _ =>
              proveNonzeroEntry leaf (entries[i]!)[c]! zero m!"the pivot entry at ({i}, {c})"
          mkAppM ``And.intro #[hz, hn]
        | _ => throwError "unexpected shape of the pivot entry conditions:{indentExpr gi}"
      let hMono ← certifyCondition "monotonicity of the pivot function" mono
      let hStrict ← certifyCondition "strict monotonicity of the pivot function" strict
      mkAppM ``Iff.mpr
        #[iff, ← mkAppM ``And.intro #[hMono, ← mkAppM ``And.intro #[hStrict, entryConds]]]
    | _ => throwError "unexpected shape of `Matrix.isPivotedBy_iff`:{indentExpr rest}"
  | _ => throwError "unexpected shape of `Matrix.isPivotedBy_iff`"

/-- Prove the row arrangement `A.submatrix σ id = Aσ`, with `Aσ` the literal `mkMatrixLit`
built from `entries`, by proving the reindexing functions equal and lifting that with
`congrArg`. Directly constructing the goal with `.submatrix` causes some exponential explosion
in kernel unfolds. -/
def mkPermEq {u : Level} {m n : ℕ} {α : Q(Type u)} (A Aσ : Q(Matrix (Fin $m) (Fin $n) $α))
    (entries : Array (Array Q($α))) (σ : Q(Equiv.Perm (Fin $m))) :
    MetaM Q(($A).submatrix $σ id = $Aσ) := do
  have rows : Q(Fin $m → Fin $n → $α) := mkRowsLit α m n entries
  -- every cell is an equation between two spellings of one entry of `A`, so all of them
  -- close by `rfl` and none consults a leaf normaliser
  have reindexed : Q(Fin $m → Fin $n → $α) := q(fun i j => $A ($σ i) (id j))
  have rowStmt : Q(Prop) := ← withLocalDeclD `i q(Fin $m) fun i => do
    mkForallFVars #[i] (← mkEq (mkApp reindexed i).headBeta (mkApp rows i))
  let rowEq ← mkForallFin m rowStmt fun i _ => do
    let iN ← mkFinNumeral m i
    have colStmt : Q(Prop) := ← withLocalDeclD `j q(Fin $n) fun j => do
      mkForallFVars #[j] (← mkEq (mkApp2 reindexed iN j).headBeta (mkApp2 rows iN j))
    mkAppM ``funext #[← mkForallFin n colStmt fun _ cell => proveRflCell cell]
  have wrap : Q((Fin $m → Fin $n → $α) → Matrix (Fin $m) (Fin $n) $α) :=
    q(fun g => Matrix.of g)
  mkExpectedTypeHint (← mkAppM ``congrArg #[wrap, ← mkAppM ``funext #[rowEq]])
    q(($A).submatrix $σ id = $Aσ)

/-- Prove the product `L * Aσ = U` entrywise from the recorded entries `lEntries`,
`aEntries` and `uEntries`. At concrete indices the product reduces to the fold of its
terms, which `leaf` settles against the entry of `U`. -/
def mkProductEq {u : Level} {m n : ℕ} {α : Q(Type u)} (_cr : Q(CommRing $α))
    (L : Q(Matrix (Fin $m) (Fin $m) $α)) (lEntries : Array (Array Q($α)))
    (Aσ : Q(Matrix (Fin $m) (Fin $n) $α)) (aEntries : Array (Array Q($α)))
    (U : Q(Matrix (Fin $m) (Fin $n) $α)) (uEntries : Array (Array Q($α)))
    (leaf : LeafProver) : MetaM Q($L * $Aσ = $U) := do
  have zero : Q($α) := ← mkNumeral α 0
  -- synthesised once, so that every cell references one instance node rather than rebuilding
  -- the projection path from `_cr`
  have _hmul : Q(HMul $α $α $α) := ← synthInstanceQ q(HMul $α $α $α)
  have _hadd : Q(HAdd $α $α $α) := ← synthInstanceQ q(HAdd $α $α $α)
  let cell (i j : Nat) : MetaM Expr := do
    let terms : Array Q($α) := Array.ofFn (n := m) fun c =>
      q($((lEntries[i]!)[c]!) * $((aEntries[c]!)[j]!))
    -- the fold must reproduce what `(L * Aσ) i j` expands to
    have sum : Q($α) := terms.foldr (fun t acc => q($t + $acc)) zero
    have entry : Q($α) := (uEntries[i]!)[j]!
    let (b, prf) ← leaf q($sum = $entry)
    unless b do
      throwError "the product of the transform does not match the echelon form at ({i}, {j})"
    return prf
  return q(Matrix.ext $(← mkForallFin m q(∀ i j, ($L * $Aσ) i j = $U i j) fun i gi => do
    mkForallFin n gi fun j _ => cell i j))

/-- Build the `Echelon.Decomposition` certificate of `A` from the decomposition data and
`entries`, the parsed entries of `A`, deciding every condition in the kernel unless `leaf?`
supplies a normaliser for the entry ones. -/
def mkCertificate {u : Level} {m n : ℕ} {α : Q(Type u)} (_cr : Q(CommRing $α))
    (A : Q(Matrix (Fin $m) (Fin $n) $α)) (entries : Array (Array Q($α)))
    (data : BareissData Expr) (leaf? : Option LeafProver) :
    MetaM Q(Echelon.Decomposition $A) := withDefault do
  -- `withDefault`: the ambient transparency inside `simp` is `reducible`, which does not
  -- reduce a matrix literal at a concrete index, so no entry would be recognised as zero
  have L := mkMatrixLit α m m data.L
  have U := mkMatrixLit α m n data.U
  let aEntries := data.rowOrder.map (entries[·]!)
  have Aσ := mkMatrixLit α m n aEntries
  let σ ← mkPerm m data.swaps
  let pivot ← mkPivotLit m n data.pivot
  match leaf? with
  | none =>
    have hperm : Q(($A).submatrix $σ id = $Aσ) :=
      ← certifyCondition "the row arrangement" q(($A).submatrix $σ id = $Aσ)
    have hprod : Q($L * $Aσ = $U) :=
      ← certifyCondition "the product of the transform" q($L * $Aσ = $U)
    have hU : Q($L * ($A).submatrix $σ id = $U) := q($hperm ▸ $hprod)
    let hpivot ← certifyCondition "the echelon-pivot condition" q(($U).IsPivotedBy $pivot)
    let hlower ← certifyCondition "lower triangularity of the transform"
      q(($L).IsLowerTriangular)
    let hdiag ← certifyCondition "the nonzero diagonal of the transform"
      q(∀ i, ($L).diag i ≠ 0)
    return q(⟨$L, $σ, $pivot, $hU ▸ $hpivot, $hlower, $hdiag⟩)
  | some leaf =>
    have hperm : Q(($A).submatrix $σ id = $Aσ) := ← mkPermEq A Aσ aEntries σ
    have hprod : Q($L * $Aσ = $U) :=
      ← mkProductEq _cr L data.L Aσ aEntries U data.U leaf
    have hU : Q($L * ($A).submatrix $σ id = $U) := q($hperm ▸ $hprod)
    have hpivot : Q(($U).IsPivotedBy $pivot) := ← mkPivotCond _cr U data.U pivot data.pivot leaf
    have hlower : Q(($L).IsLowerTriangular) := ← mkLowerCond _cr L
    have hdiag : Q(∀ i, ($L).diag i ≠ 0) := ← mkDiagCond _cr L data.L leaf
    return q(⟨$L, $σ, $pivot, $hU ▸ $hpivot, $hlower, $hdiag⟩)

end Mathlib.Tactic.Echelon
