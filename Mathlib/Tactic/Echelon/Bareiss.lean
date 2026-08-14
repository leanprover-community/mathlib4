/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.LinearAlgebra.Matrix.Echelon.Decomposition
public import Mathlib.Tactic.Echelon.Rat

/-!
# The Bareiss decomposition driver

Given a matrix literal `A` over a commutative domain, the entry point
`mkBareissDecomposition` selects a computation model for the element type, runs the
elimination, and elaborates a certificate `⟨L, σ, pivot, …⟩ : Echelon.Decomposition A`,
with the certificate conditions checked by the kernel via `decide`. The elimination
itself is the model-parameterized `bareissDecomp` in `Mathlib.Tactic.Echelon.Core`.

## Main definitions

- `mkBareissDecomposition`: produce and elaborate the decomposition of a matrix literal.
- `BareissResult`: the elaborated certificate together with the computed decomposition data.
- `checkBareissApplicable`: the applicability check of the Bareiss method.
- `producerFor`: select the computation model for a ring.
-/

public meta section

open Lean Meta Elab Qq

initialize registerTraceClass `Tactic.evalRank

namespace Mathlib.Tactic.Echelon

/-- Build the numeral of `i` in `Fin $n`. -/
def mkFinNumeral (n : ℕ) (i : ℕ) : MetaM Q(Fin $n) :=
  mkNumeral q(Fin $n) i

/-- Build the pivot literal `![↑c₀, …, ⊤, …] : Fin m → WithTop (Fin n)`, sending the
first rows to their pivot columns and the remaining rows to `⊤`. -/
def mkPivotLit (m n : Nat) (pivots : Array Nat) : MetaM Expr := do
  let entries : Array Q(WithTop (Fin $n)) ← Array.ofFnM (n := m) fun i => do
    if hi : i < pivots.size then
      return q(WithTop.some $(← mkFinNumeral n pivots[i]))
    else
      return q(⊤ : WithTop (Fin $n))
  return PiFin.mkLiteralQ (α := q(WithTop (Fin $n))) (n := m) fun i => entries[i]!

/-- Build the permutation `σ = swap a₀ b₀ * swap a₁ b₁ * ⋯` from the recorded swaps. -/
def mkPerm (m : Nat) (swaps : Array (Nat × Nat)) : MetaM Expr := do
  let mut acc : Q(Equiv.Perm (Fin $m)) := q(Equiv.refl (Fin $m))
  for (a, b) in swaps do
    acc := q((Equiv.swap $(← mkFinNumeral m a) $(← mkFinNumeral m b)).trans $acc)
  return acc

/-- Check that equality with zero in `R` reduces to a verdict in the kernel, as the
certificate conditions will be decided by kernel reduction. This needs to be changed when
the cert-checking tactic is updated. -/
def checkKernelDecide {u : Level} (R : Q(Type u)) : MetaM Unit := do
  have _cr : Q(CommRing $R) := ← synthInstanceQ q(CommRing $R)
  -- `Decidable` of the single equality rather than `DecidableEq`: a ring where equality
  -- is only decidable against zero should pass
  let some inst ← synthInstance? q(Decidable (((1 : ℤ) : $R) = 0))
    | throwError "equality with zero in the element type is not decidable{indentExpr R}"
  -- check if the equality reduced to a concrete false
  unless (Kernel.whnf (← getEnv) (← getLCtx) inst).toOption.any
      (·.isAppOf ``Decidable.isFalse) do
    throwError "equality in the element type does not reduce in the kernel{indentExpr R}"

/-- The applicability check of the Bareiss method, which requires a commutative domain
with kernel-decidable equality. -/
def checkBareissApplicable (R : Expr) : MetaM (Except MessageData Unit) := do
  let u ← getDecLevel R
  have R : Q(Type u) := R
  let .some _cr ← trySynthInstanceQ q(CommRing $R)
    | return .error m!"expected the element type to be a commutative ring"
  let .some _ ← trySynthInstanceQ q(IsDomain $R)
    | return .error m!"expected the element type to be a domain"
  try
    checkKernelDecide R
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

/-- Select the computation model for the ring expression `R`: the first registered
`bareiss_ext` extension that handles `R`, or the default rational model. -/
def producerFor (R : Expr) : MetaM Producer := do
  let R ← whnf R
  for ext in bareissExt.getState (← getEnv) do
    if let some p ← ext.producer? R then
      trace[Tactic.evalRank] "selected the model `{ext.name}` for{indentExpr R}"
      return p
  ratProducer R

/-- The result of producing a decomposition by Bareiss. -/
structure BareissResult where
  /-- The elaborated `Echelon.Decomposition` certificate term. -/
  cert : Expr
  /-- The decomposition data underlying the certificate. -/
  data : BareissData Expr

/-- Produce and elaborate the `Echelon.Decomposition` certificate of the matrix literal
`A`. -/
def mkBareissDecomposition (A : Expr) (m n : Nat) (R : Expr)
    (entries : Array (Array Expr)) : TermElabM BareissResult := do
  let d ← (← producerFor R) entries
  let u ← getDecLevel R
  have R : Q(Type u) := R
  let L := Matrix.mkLiteralQ (α := R) (m := m) (n := m) (.of fun i j => (d.L[i]!)[j]!)
  return { cert := ← elabCertificate A L (← mkPerm m d.swaps) (← mkPivotLit m n d.pivot)
           data := d }

end Mathlib.Tactic.Echelon
