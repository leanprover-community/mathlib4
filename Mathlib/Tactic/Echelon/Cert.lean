/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.LinearAlgebra.Matrix.Echelon.Decomposition -- shake: keep (Qq dependency)
public import Mathlib.Tactic.Echelon.Core
public import Mathlib.Util.Qq

/-!
# Certificate construction for the Bareiss decomposition

The elaboration of the certificate components from the decomposition data, and the
default certifier `mkCertificate`, which proves the certificate conditions by
kernel-checked `decide`.

## Main definitions

- `CertInput`, `Certifier`: the input of a certifier, and the certifier interface.
- `mkCertificate`: build the `Echelon.Decomposition` certificate of a matrix literal.
- `checkKernelDecide`: check that equality in a ring reduces in the kernel.
- `mkPerm`, `mkPivotLit`: elaborate the row permutation and the pivot function.

## Implementation notes

The elimination records its echelon form `U`, making the product a certificate obligation
of its own, `L * A_σ = U`, decided separately from the pivot condition on `U`. Deciding
the pivot condition on the product itself evaluates the multiplication inside the decision
procedure, leaving no separate goal for a dedicated matrix multiplication tactic to
discharge.
-/

public meta section

open Lean Meta Qq

namespace Mathlib.Tactic.Echelon

/-- The input of a certifier. The matrix literal `A` with its element type and parsed
entries, and the decomposition data computed by the producer. Certifiers elaborate the
required components from `data`. -/
structure CertInput where
  /-- The universe of the element type. -/
  u : Level
  /-- The element type, `Q(Type u)`. -/
  α : Expr
  /-- The number of rows. -/
  m : Nat
  /-- The number of columns. -/
  n : Nat
  /-- The matrix literal, `Q(Matrix (Fin m) (Fin n) α)`. -/
  A : Expr
  /-- The parsed entries of `A`. -/
  entries : Array (Array Expr)
  /-- The decomposition data computed by the producer. -/
  data : BareissData Expr

/-- A certifier: prove the certificate conditions, elaborating the
`Echelon.Decomposition A` term of the input. -/
@[expose] def Certifier := CertInput → MetaM Expr

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

/-- Prove the certificate condition `c` by a kernel-checked `decide`, with `name` naming
the condition in errors. -/
def certifyCondition (name : String) (c : Q(Prop)) : MetaM Q($c) := do
  let d ← mkDecide c
  let .ok r := Kernel.whnf (← getEnv) (← getLCtx) d
    | throwError "cannot verify the rank certificate: {name} does not reduce in the kernel"
  unless r.isConstOf ``Bool.true do
    throwError "cannot verify the rank certificate: {name} failed"
  mkDecideProofQ c

/-- Build the `Echelon.Decomposition` certificate of the input's matrix literal, with the
certificate conditions proven by kernel-checked `decide`. -/
def mkCertificate : Certifier := fun input => do
  let { u, m, n, entries, data, .. } := input
  have α : Q(Type u) := input.α
  have A : Q(Matrix (Fin $m) (Fin $n) $α) := input.A
  have _cr : Q(CommRing $α) := ← synthInstanceQ q(CommRing $α)
  let lit (r c : Nat) (rows : Array (Array Expr)) : Q(Matrix (Fin $r) (Fin $c) $α) :=
    Matrix.mkLiteralQ (α := α) (m := r) (n := c) (.of fun i j => (rows[i]!)[j]!)
  have L : Q(Matrix (Fin $m) (Fin $m) $α) := lit m m data.L
  have U : Q(Matrix (Fin $m) (Fin $n) $α) := lit m n data.U
  -- the row of `A_σ = A.submatrix σ id` at position `i` is the row of `A` at `σ i`
  have Aσ : Q(Matrix (Fin $m) (Fin $n) $α) := lit m n (data.rowOrder.map (entries[·]!))
  let σ ← mkPerm m data.swaps
  let pivot ← mkPivotLit m n data.pivot
  let hperm ← certifyCondition "the row arrangement" q(($A).submatrix $σ id = $Aσ)
  -- TODO: switch to a dedicated matrix multiplication tactic once implemented
  let hprod ← certifyCondition "the product of the transform" q($L * $Aσ = $U)
  have hU : Q($L * ($A).submatrix $σ id = $U) := q($hperm ▸ $hprod)
  let hpivot ← certifyCondition "the echelon-pivot condition" q(($U).IsPivotedBy $pivot)
  let hlower ← certifyCondition "lower triangularity of the transform" q(($L).IsLowerTriangular)
  let hdiag ← certifyCondition "the nonzero diagonal of the transform" q(∀ i, ($L).diag i ≠ 0)
  let cert : Q(Echelon.Decomposition $A) :=
    q(⟨$L, $σ, $pivot, $hU ▸ $hpivot, $hlower, $hdiag⟩)
  return cert

end Mathlib.Tactic.Echelon
