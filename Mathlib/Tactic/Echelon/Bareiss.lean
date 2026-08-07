/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.LinearAlgebra.Matrix.Echelon.Decomposition
public import Mathlib.Tactic.Echelon.Core
public import Mathlib.Tactic.Echelon.Rat
public import Mathlib.Tactic.Echelon.Zsqrtd

public meta import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The Bareiss decomposition method

Given a matrix literal `A` over a commutative domain, the entry point
`mkBareissDecomposition` selects a computation model for the element type, runs the
elimination, and elaborates a certificate `⟨L, σ, pivot, …⟩ : Echelon.Decomposition A`,
with the certificate conditions checked by the kernel via `decide`.

## Main definitions

- `mkBareissDecomposition`: produce and elaborate the decomposition of a matrix literal.
- `checkBareissApplicable`: the applicability check of the Bareiss method.
- `producerFor`: select the computation model for a ring.
-/

public meta section

open Lean Meta Elab Qq

namespace Mathlib.Tactic.Echelon

/-- Build the numeral of `i` in `Fin $n`. -/
def mkFinNumeral (n : ℕ) (i : ℕ) : MetaM Q(Fin $n) :=
  mkNumeral q(Fin $n) i

/-- Build the pivot literal `![↑c₀, …, ⊤, …] : Fin m → WithTop (Fin n)`, sending the
first rows to their pivot columns and the remaining rows to `⊤`. -/
def mkPivotLit (m n : Nat) (pivots : Array Nat) : MetaM Expr := do
  let entries : Array Q(WithTop (Fin $n)) ← (Array.range m).mapM fun i => do
    if hi : i < pivots.size then
      return q(WithTop.some $(← mkFinNumeral n pivots[i]))
    else
      return q((⊤ : WithTop (Fin $n)))
  return PiFin.mkLiteralQ (α := q(WithTop (Fin $n))) (n := m) fun i => entries[i.1]!

/-- Build the permutation `σ = swap a₀ b₀ * swap a₁ b₁ * ⋯` from the recorded swaps. -/
def mkPerm (m : Nat) (swaps : Array (Nat × Nat)) : MetaM Expr := do
  let mut acc : Q(Equiv.Perm (Fin $m)) := q(Equiv.refl (Fin $m))
  for (a, b) in swaps do
    acc := q($acc * Equiv.swap $(← mkFinNumeral m a) $(← mkFinNumeral m b))
  return acc

/-- The applicability check of the Bareiss method, which requires a commutative domain
with kernel-decidable equality. -/
def checkBareissApplicable (R : Expr) : MetaM (Except MessageData Unit) := do
  let u ← getDecLevel R
  have R : Q(Type u) := R
  let .some _cr ← trySynthInstanceQ q(CommRing $R)
    | return .error m!"expected the element type to be a commutative ring"
  let .some _ ← trySynthInstanceQ q(IsDomain $R)
    | return .error m!"expected the element type to be a domain"
  -- the certificate conditions are decided by kernel reduction: probe one zero test
  try
    discard <| isZeroInRing R 1
  catch e =>
    return .error e.toMessageData
  return .ok ()

/-- A wrapper for the `decide` decision of a certificate condition with a named error. -/
scoped elab "bareiss_certify " s:str : tactic => do
  try
    Tactic.evalTactic (← `(tactic| decide +kernel))
  catch e =>
    throwError "cannot verify the rank certificate: {s.getString} failed:\n{e.toMessageData}"

/-- Elaborate the `Echelon.Decomposition` certificate of `A` from its rendered
components, with the kernel checking the certificate conditions. -/
def elabCertificate (A L σ pivotE : Expr) : TermElabM Expr := do
  let stx ← `((⟨$(← Term.exprToSyntax L), $(← Term.exprToSyntax σ),
                $(← Term.exprToSyntax pivotE),
                -- TODO: switch to a better decision of matrix mult once implemented
                by bareiss_certify "the echelon-pivot condition",
                by bareiss_certify "lower triangularity of the transform",
                by bareiss_certify "the nonzero diagonal of the transform"⟩ :
              Echelon.Decomposition $(← Term.exprToSyntax A)))
  -- without the recovery barrier a failing obligation would be logged and patched with
  -- `sorryAx` instead of thrown
  let e ← Term.withoutErrToSorry do
    let e ← Term.elabTermEnsuringType stx none
    Term.synthesizeSyntheticMVarsNoPostponing
    pure e
  instantiateMVars e

-- TODO: implement this in compiler using some method like a `norm_num` extension
/-- Select the computation model for the ring expression `R`. -/
def producerFor (R : Expr) : MetaM Producer := do
  -- ring-specific models match on the head of `R` here, before the fallback
  if let some p ← zsqrtdExt R then return p
  ratExt R

/-- Produce and elaborate the `Echelon.Decomposition` certificate of the matrix literal
`A`. -/
def mkBareissDecomposition (A : Expr) (m n : Nat) (R : Expr)
    (entries : Array (Array Expr)) : TermElabM Expr := do
  let d ← (← producerFor R) entries
  let u ← getDecLevel R
  have R : Q(Type u) := R
  let L := Matrix.mkLiteralQ (α := R) (m := m) (n := m)
    (.of fun i j => show Q($R) from (d.L[i.1]!)[j.1]!)
  elabCertificate A L (← mkPerm m d.swaps) (← mkPivotLit m n d.pivot)

end Mathlib.Tactic.Echelon
