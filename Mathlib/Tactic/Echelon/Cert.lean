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
`mkCertificate`, which currently proves the certificate conditions by `decide +kernel`.

This will eventually be generalised to a general certificate
constructor that is parametric on a leaf normaliser.

## Main definitions

- `mkCertificate`: build the `Echelon.Decomposition` certificate of a matrix literal.
- `checkKernelDecide`: check that equality in a ring reduces in the kernel.
- `mkPerm`, `mkPivotLit`, `mkMatrixLit`: elaborate the row permutation, the pivot
  function, and a matrix literal.

## Implementation notes

The elimination records its echelon form `U`, making the product a certificate obligation
of its own, `L * A_σ = U`, decided separately from the pivot condition on `U`.
-/

public meta section

open Lean Meta Qq

namespace Mathlib.Tactic.Echelon

/-- Build the numeral of `i` in `Fin $n`. -/
def mkFinNumeral (n : ℕ) (i : ℕ) : MetaM Q(Fin $n) :=
  mkNumeral q(Fin $n) i

/-- Build the matrix literal of the row-major entries `rows`. -/
def mkMatrixLit {u : Level} (α : Q(Type u)) (m n : Nat) (rows : Array (Array Expr)) :
    Q(Matrix (Fin $m) (Fin $n) $α) :=
  Matrix.mkLiteralQ (α := α) (m := m) (n := n) (.of fun i j => (rows[i]!)[j]!)

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

/-- Check that equality with zero in `α` reduces to a verdict in the kernel, as the
certificate conditions will be decided by kernel reduction. This needs to be changed when
the cert-checking tactic is updated. -/
def checkKernelDecide {u : Level} (α : Q(Type u)) : MetaM Unit := do
  have _cr : Q(CommRing $α) := ← synthInstanceQ q(CommRing $α)
  -- `Decidable` of the single equality rather than `DecidableEq`: a ring where equality
  -- is only decidable against zero should pass
  let some inst ← synthInstance? q(Decidable (((1 : ℤ) : $α) = 0))
    | throwError "equality with zero in the element type is not decidable{indentExpr α}"
  -- check if the equality reduced to a concrete false
  unless (Kernel.whnf (← getEnv) (← getLCtx) inst).toOption.any
      (·.isAppOf ``Decidable.isFalse) do
    throwError "equality in the element type does not reduce in the kernel{indentExpr α}"

/-- Prove the certificate condition `c` by a kernel-checked `decide`, with `name` naming
the condition in errors. -/
def certifyCondition (name : String) (c : Q(Prop)) : MetaM Q($c) := do
  let d ← mkDecide c
  let .ok r := Kernel.whnf (← getEnv) (← getLCtx) d
    | throwError "cannot verify the rank certificate: {name} does not reduce in the kernel"
  unless r.isConstOf ``Bool.true do
    throwError "cannot verify the rank certificate: {name} failed"
  mkDecideProofQ c

/-- A leaf normaliser settles a proposition about a single entry, returning its truth value
together with a proof of the proposition or of its negation. -/
@[expose] def LeafProver := Expr → MetaM (Bool × Expr)

/-- `norm_num`'s core as a leaf normaliser. -/
def normNumLeaf : LeafProver := fun p => do
  let ⟨b, prf⟩ ← Mathlib.Meta.NormNum.deriveBool p
  return (b, prf)

/-- The entries of the matrix a condition speaks about, addressed by the index path that
the condition's quantifiers have introduced so far. -/
abbrev EntryLookup := Array Nat → MetaM Expr

/-- Prove `¬ p` when `decide p` reduces to `false` in the kernel. The index guards of a
condition are decidable in any ring, as they mention no entries. -/
def refuteGuard? (p : Expr) : MetaM (Option Expr) := do
  let .some inst ← trySynthInstance (← mkAppM ``Decidable #[p]) | return none
  let d ← mkAppOptM ``Decidable.decide #[p, inst]
  let .ok r := Kernel.whnf (← getEnv) (← getLCtx) d | return none
  unless r.isConstOf ``Bool.false do return none
  let ff := mkConst ``Bool.false
  let h ← mkExpectedTypeHint (← mkEqRefl ff) (← mkEq d ff)
  return some (← mkAppOptM ``of_decide_eq_false #[p, inst, h])

/-- Prove `∀ i : Fin n, motive i` from proofs of its instances, `head i` proving the
statement at index `i`. The proof recurses on the index list `List.finRange n`, so the
motive is spelled once rather than once per index. -/
def mkListForall (n : Nat) (motive : Expr) (head : Nat → Expr → MetaM Expr) : MetaM Expr := do
  let fin ← mkAppM ``Fin #[mkNatLit n]
  let mut acc : Expr := mkConst ``True.intro
  for k in [0:n] do
    let i := n - 1 - k
    let h ← head i (← whnfR (mkApp motive (← mkNumeral fin i)))
    -- the conjunction takes its statement from the proofs, so that the one defeq check
    -- against the quantified goal is left to the kernel rather than run here as well
    acc ← if k == 0 then pure h else mkAppM ``And.intro #[h, acc]
  let range ← mkAppM ``List.finRange #[mkNatLit n]
  let hAll ← mkAppM ``Iff.mp
    #[← mkAppOptM ``List.forall_iff_forall_mem #[none, some motive, some range],
      ← mkExpectedTypeHint acc (← mkAppM ``List.Forall #[motive, range])]
  withLocalDeclD `i fin fun i => do
    let body := mkApp2 hAll i (← mkAppM ``List.mem_finRange #[i])
    mkExpectedTypeHint (← mkLambdaFVars #[i] body)
      (← mkForallFVars #[i] (← whnfR (mkApp motive i)))

/-- Prove one cell of a certificate condition, on the shape of its statement: a conjunction
splits, a quantifier over `Fin k` is taken apart index by index, a guard that no index
satisfies is refuted, an entry that the elimination emitted as zero is closed by `rfl`, and
a nonzero entry is left to `leaf`. A statement of none of these shapes, such as the pivot
function's monotonicity, mentions no entry and is decided in the kernel. -/
partial def proveCell (leaf : LeafProver) (ents : EntryLookup) (path : Array Nat)
    (goal : Expr) : MetaM Expr := do
  let g ← whnfR goal
  if let some (a, b) := g.and? then
    return ← mkAppM ``And.intro #[← proveCell leaf ents path a, ← proveCell leaf ents path b]
  -- `e ≠ 0`, in either spelling: the entry is nonzero
  let negated? : Option Expr :=
    match g.ne? with
    | some (_, _, rhs) => some rhs
    | none => (g.not?.bind (·.eq?)).map (·.2.2)
  if let some rhs := negated? then
    let (b, prf) ← leaf (← mkEq (← ents path) rhs)
    if b then throwError "the entry at {path} was expected to be nonzero"
    return prf
  match g with
  | .forallE nm dom body bi =>
    if dom.isAppOfArity ``Fin 1 then
      if let some k ← getNatValue? (← whnfR dom.appArg!) then
        return ← mkListForall k (.lam nm dom body bi) fun i gi =>
          proveCell leaf ents (path.push i) gi
    if let some ref ← refuteGuard? dom then
      withLocalDecl nm bi dom fun h => do
        let tgt := body.instantiate1 h
        mkLambdaFVars #[h] (← mkAppOptM ``absurd #[some dom, some tgt, some h, some ref])
    else
      withLocalDecl nm bi dom fun h => do
        mkLambdaFVars #[h] (← proveCell leaf ents path (body.instantiate1 h))
  | _ =>
    if let some (_, lhs, rhs) := g.eq? then
      if ← isDefEq lhs rhs then
        return ← mkEqRefl lhs
    -- no entry of ours occurs: decide it, and only then unfold and try again
    try
      certifyCondition "a condition on the pivot function" g
    catch e =>
      let some g' ← unfoldDefinition? g
        | throwError "cannot verify the rank certificate:{indentExpr g}\
            \nis neither decidable nor reducible:{indentD e.toMessageData}"
      proveCell leaf ents path g'

/-- Prove the row arrangement `A.submatrix σ id = Aσ` entrywise: at concrete indices both
sides reduce to the same entry of `A`, so every cell is closed by `rfl`. -/
def mkPermEq {u : Level} {m n : ℕ} {α : Q(Type u)} (A Aσ : Q(Matrix (Fin $m) (Fin $n) $α))
    (σ : Q(Equiv.Perm (Fin $m))) (leaf : LeafProver) :
    MetaM Q(($A).submatrix $σ id = $Aσ) := do
  let noEntries : EntryLookup := fun p =>
    throwError "the row arrangement is not entrywise definitional at {p}"
  mkAppM ``Matrix.ext
    #[← proveCell leaf noEntries #[] q(∀ i j, ($A).submatrix $σ id i j = $Aσ i j)]

/-- Prove the product `L * Aσ = U` entrywise from the recorded entries `lEntries`,
`aEntries` and `uEntries`. At concrete indices the product reduces to the fold of its
terms, which `leaf` settles against the entry of `U`. -/
def mkProductEq {u : Level} {m n : ℕ} {α : Q(Type u)} (_cr : Q(CommRing $α))
    (L : Q(Matrix (Fin $m) (Fin $m) $α)) (Aσ U : Q(Matrix (Fin $m) (Fin $n) $α))
    (lEntries aEntries uEntries : Array (Array Expr)) (leaf : LeafProver) :
    MetaM Q($L * $Aσ = $U) := do
  let motiveOf (e : Expr) : MetaM Expr := do
    match ← whnfR e with
    | .forallE nm dom body bi => return .lam nm dom body bi
    | _ => throwError "expected a quantified statement:{indentExpr e}"
  let cell (i j : Nat) : MetaM Expr := do
    let mut sum ← mkNumeral α 0
    for k in [0:m] do
      let c := m - 1 - k
      let term ← mkAppM ``HMul.hMul #[(lEntries[i]!)[c]!, (aEntries[c]!)[j]!]
      sum ← mkAppM ``HAdd.hAdd #[term, sum]
    let (b, prf) ← leaf (← mkEq sum (uEntries[i]!)[j]!)
    unless b do
      throwError "the product of the transform does not match the echelon form at ({i}, {j})"
    return prf
  let rows ← motiveOf q(∀ i j, ($L * $Aσ) i j = $U i j)
  mkAppM ``Matrix.ext #[← mkListForall m rows fun i gi => do
    mkListForall n (← motiveOf gi) fun j _ => cell i j]

/-- Build the `Echelon.Decomposition` certificate of `A` from the decomposition data and
`entries`, the parsed entries of `A`.

Without a leaf normaliser every condition is decided in the kernel. With one, the entry
conditions are constructed from proofs of the individual entries, for the rings whose
equality does not reduce in the kernel. -/
def mkCertificate {u : Level} {m n : ℕ} {α : Q(Type u)} (_cr : Q(CommRing $α))
    (A : Q(Matrix (Fin $m) (Fin $n) $α)) (entries : Array (Array Expr))
    (data : BareissData Expr) (leaf? : Option LeafProver := none) :
    MetaM Q(Echelon.Decomposition $A) := withDefault do
  -- `withDefault`: the ambient transparency inside `simp` is `reducible`, which does not
  -- reduce a matrix literal at a concrete index, so no entry would be recognised as zero
  have L := mkMatrixLit α m m data.L
  have U := mkMatrixLit α m n data.U
  -- the row of `A_σ = A.submatrix σ id` at position `i` is the row of `A` at `σ i`
  let aEntries := data.rowOrder.map (entries[·]!)
  have Aσ := mkMatrixLit α m n aEntries
  let σ ← mkPerm m data.swaps
  let pivot ← mkPivotLit m n data.pivot
  match leaf? with
  | none =>
    have hperm : Q(($A).submatrix $σ id = $Aσ) :=
      ← certifyCondition "the row arrangement" q(($A).submatrix $σ id = $Aσ)
    -- TODO: switch to a dedicated matrix multiplication tactic once implemented
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
    have hperm : Q(($A).submatrix $σ id = $Aσ) := ← mkPermEq A Aσ σ leaf
    have hprod : Q($L * $Aσ = $U) :=
      ← mkProductEq _cr L Aσ U data.L aEntries data.U leaf
    have hU : Q($L * ($A).submatrix $σ id = $U) := q($hperm ▸ $hprod)
    let uEnts : EntryLookup := fun p => return (data.U[p[0]!]!)[p[1]!]!
    let lEnts : EntryLookup := fun p => return (data.L[p[0]!]!)[p[1]!]!
    let diagEnts : EntryLookup := fun p => return (data.L[p[0]!]!)[p[0]!]!
    -- the pivot condition through its characterisation: the two conditions on the pivot
    -- function are decided, and the entry conditions constructed
    let pivotIff ← mkAppOptM ``Matrix.isPivotedBy_iff
      #[none, none, none, none, some U, some pivot, none, none]
    let pivotRhs := (← whnfR (← inferType pivotIff)).appArg!
    have hpivot : Q(($U).IsPivotedBy $pivot) :=
      ← mkAppM ``Iff.mpr #[pivotIff, ← proveCell leaf uEnts #[] pivotRhs]
    have hlower : Q(($L).IsLowerTriangular) :=
      ← proveCell leaf lEnts #[] q(($L).IsLowerTriangular)
    have hdiag : Q(∀ i, ($L).diag i ≠ 0) :=
      ← proveCell leaf diagEnts #[] q(∀ i, ($L).diag i ≠ 0)
    return q(⟨$L, $σ, $pivot, $hU ▸ $hpivot, $hlower, $hdiag⟩)

end Mathlib.Tactic.Echelon
