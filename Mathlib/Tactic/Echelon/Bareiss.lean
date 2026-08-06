/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.LinearAlgebra.Matrix.Echelon.Defs
public import Mathlib.Tactic.Echelon.Core

public meta import Mathlib.LinearAlgebra.Matrix.Notation
public meta import Mathlib.Util.Qq

public import Mathlib.Tactic.Echelon.Rat
public import Mathlib.Tactic.Echelon.Zsqrtd

/-!
# The Bareiss decomposition method

Given a matrix literal `M` over a commutative domain, the entry point
`mkBareissDecomposition` selects a computation model for the element type, runs the
elimination, and elaborates a certificate `⟨L, σ, pivot, …⟩ : Bareiss.Decomposition M`,
with the certificate conditions checked by the kernel via `decide`.

## Main definitions

- `mkBareissDecomposition`: produce and elaborate the decomposition of a matrix literal.
- `checkBareissCommittal`: the pre-commitment applicability check of the Bareiss method.
- `producerFor?`: select the computation model for a ring.
-/

public meta section

open Lean Meta Elab Qq

namespace Mathlib.Tactic.Echelon

/-- Build the matrix literal `!![…]` with the given rows of entries. -/
def mkMatrixLit {u : Level} (R : Q(Type u)) (rows : Array (Array Expr)) : Expr :=
  Matrix.mkLiteralQ (α := R) (m := rows.size) (n := (rows.getD 0 #[]).size)
    (.of fun i j => show Q($R) from (rows[i.1]!)[j.1]!)

/-- Build the pivot literal `![↑c₀, …, ⊤, …] : Fin m → WithTop (Fin n)`, sending the
first rows to their pivot columns and the remaining rows to `⊤`. -/
def mkPivotLit (m n : Nat) (pivots : Array Nat) : MetaM Expr := do
  let entries : Array Q(WithTop (Fin $n)) ← (Array.range m).mapM fun i => do
    if hi : i < pivots.size then
      let c ← mkNumeral q(Fin $n) pivots[i]
      have c : Q(Fin $n) := c
      return q(WithTop.some $c)
    else
      return q((⊤ : WithTop (Fin $n)))
  return PiFin.mkLiteralQ (α := q(WithTop (Fin $n))) (n := m) fun i => entries[i.1]!

/-- Build the permutation `σ = swap a₀ b₀ * swap a₁ b₁ * ⋯` from the recorded swaps. -/
def mkPerm (m : Nat) (swaps : Array (Nat × Nat)) : MetaM Expr := do
  have mE : Q(ℕ) := mkNatLit m
  let mut acc : Q(Equiv.Perm (Fin $mE)) := q(Equiv.refl (Fin $mE))
  for (a, b) in swaps do
    let aE ← mkNumeral q(Fin $mE) a
    let bE ← mkNumeral q(Fin $mE) b
    have aE : Q(Fin $mE) := aE
    have bE : Q(Fin $mE) := bE
    acc := q($acc * Equiv.swap $aE $bE)
  return acc

/-- The pre-commitment applicability check of the Bareiss method, which requires a
commutative domain with kernel-decidable equality. -/
def checkBareissCommittal (R : Expr) : MetaM (Except MessageData Unit) := do
  if (← synthInstance? (← mkAppM ``CommRing #[R])).isNone then
    return .error m!"expected the element type to be a commutative ring"
  if (← synthInstance? (← mkAppOptM ``IsDomain #[some R, none])).isNone then
    return .error m!"expected the element type to be a domain"
  -- the certificate conditions are decided by kernel reduction: probe one zero test
  let u ← getDecLevel R
  have R : Q(Type u) := R
  try
    discard <| isZeroInR R 1
  catch e =>
    return .error e.toMessageData
  return .ok ()

/-- A wrapper for the `decide` decision of a certificate condition with a named error. The
error is unreachable from user input — the commitment gate ensures the conditions are
kernel-decidable — and guards against a defective production. -/
scoped elab "bareiss_certify " s:str : tactic => do
  try
    Tactic.evalTactic (← `(tactic| decide +kernel))
  catch e =>
    throwError "cannot verify the rank certificate: {s.getString} failed:\n{e.toMessageData}"

/-- Elaborate the `Bareiss.Decomposition` certificate of `M` from its rendered
components, with the kernel checking the certificate conditions. -/
def elabCertificate (M L σ pivotE : Expr) : TermElabM Expr := do
  let stx ← `((⟨$(← Term.exprToSyntax L), $(← Term.exprToSyntax σ),
                $(← Term.exprToSyntax pivotE),
                -- TODO: switch to an efficient decision of matrix mult once implemented
                by bareiss_certify "the echelon-pivot condition",
                by bareiss_certify "lower triangularity of the transform",
                by bareiss_certify "the nonzero diagonal of the transform"⟩ :
              Bareiss.Decomposition $(← Term.exprToSyntax M)))
  -- without the recovery barrier a failing obligation would be logged and patched with
  -- `sorryAx` instead of thrown
  let e ← Term.withoutErrToSorry do
    let e ← Term.elabTermEnsuringType stx none
    Term.synthesizeSyntheticMVarsNoPostponing
    pure e
  instantiateMVars e

/-- Select the computation model for the ring expression `R`. -/
def producerFor? (R : Expr) : MetaM (Option Producer) := do
  -- ring-specific models match on the head of `R` here, before the fallback
  if let some p ← zsqrtdExt R then return some p
  ratExt R

/-- Produce and elaborate the `Bareiss.Decomposition` certificate of the matrix literal
`M`. -/
def mkBareissDecomposition (M : Expr) (m n : Nat) (R : Expr)
    (entries : Array (Array Expr)) : TermElabM Expr := do
  let some produce ← producerFor? R
    | throwError "no computation model applies to the element type{indentExpr R}"
  let d ← produce entries
  let u ← getDecLevel R
  have R : Q(Type u) := R
  elabCertificate M (mkMatrixLit R d.L) (← mkPerm m d.swaps) (← mkPivotLit m n d.pivot)

end Mathlib.Tactic.Echelon
