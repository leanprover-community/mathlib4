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

open Lean Meta Qq

initialize registerTraceClass `Tactic.evalRank

namespace Mathlib.Tactic.Echelon

/-- Build the numeral of `i` in `Fin $n`. -/
def mkFinNumeral (n : ℕ) (i : ℕ) : MetaM Q(Fin $n) :=
  mkNumeral q(Fin $n) i

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

/-- The applicability check of the Bareiss method, which requires a commutative domain
with kernel-decidable equality. -/
def checkBareissApplicable (R : Expr) : MetaM (Except MessageData Unit) := do
  let u ← getDecLevel R
  have α : Q(Type u) := R
  let .some _cr ← trySynthInstanceQ q(CommRing $α)
    | return .error m!"expected the element type to be a commutative ring"
  let .some _ ← trySynthInstanceQ q(IsDomain $α)
    | return .error m!"expected the element type to be a domain"
  try
    checkKernelDecide α
  catch e =>
    return .error e.toMessageData
  return .ok ()

/-- Prove the certificate condition `c` by a kernel-checked `decide`, with `name` naming
the condition in errors. -/
def certifyCondition (name : String) (c : Q(Prop)) : MetaM Q($c) := do
  let d ← mkDecide c
  let .ok r := Kernel.whnf (← getEnv) (← getLCtx) d
    | throwError "cannot verify the rank certificate: {name} does not reduce in the kernel"
  unless r.isConstOf ``Bool.true do
    throwError "cannot verify the rank certificate: {name} failed"
  mkDecideProofQ c

/-- Build the `Echelon.Decomposition` certificate of `A` from its constructed components,
with the certificate conditions proven by kernel-checked `decide`. -/
def mkCertificate {u : Level} {m n : ℕ} {α : Q(Type u)} (_cr : Q(CommRing $α))
    (A : Q(Matrix (Fin $m) (Fin $n) $α)) (L : Q(Matrix (Fin $m) (Fin $m) $α))
    (σ : Q(Equiv.Perm (Fin $m))) (pivot : Q(Fin $m → WithTop (Fin $n))) :
    MetaM Q(Echelon.Decomposition $A) := do
  let pf₁ ← certifyCondition "the echelon-pivot condition"
    -- TODO: switch to a better decision of matrix mult once implemented
    q(($L * ($A).submatrix $σ id).IsPivotedBy $pivot)
  let pf₂ ← certifyCondition "lower triangularity of the transform"
    q(($L).IsLowerTriangular)
  let pf₃ ← certifyCondition "the nonzero diagonal of the transform"
    q(∀ i, ($L).diag i ≠ 0)
  return q(⟨$L, $σ, $pivot, $pf₁, $pf₂, $pf₃⟩)

/-- Select the computation model for the ring expression `R`: the first registered
`bareiss_ext` extension that handles `R`, or the default rational model. -/
def producerFor (R : Expr) : MetaM Producer := do
  for (name, ext) in bareissExt.getState (← getEnv) do
    if let some p ← ext.producer? R then
      trace[Tactic.evalRank] "selected the model `{name}` for{indentExpr R}"
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
def mkBareissDecomposition {u : Level} (A : Expr) (m n : Nat) (α : Q(Type u))
    (entries : Array (Array Expr)) : MetaM BareissResult := do
  let d ← (← producerFor α) entries
  have _cr : Q(CommRing $α) := ← synthInstanceQ q(CommRing $α)
  have A : Q(Matrix (Fin $m) (Fin $n) $α) := A
  let L := Matrix.mkLiteralQ (α := α) (m := m) (n := m) (.of fun i j => (d.L[i]!)[j]!)
  return { cert := ← mkCertificate _cr A L (← mkPerm m d.swaps) (← mkPivotLit m n d.pivot)
           data := d }

end Mathlib.Tactic.Echelon
