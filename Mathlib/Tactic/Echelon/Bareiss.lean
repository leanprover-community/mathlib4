/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Tactic.Echelon.Cert
public import Mathlib.Tactic.Echelon.Rat

/-!
# The Bareiss decomposition driver

Given a matrix literal `A` over a commutative domain, the entry point
`mkBareissDecomposition` selects a computation model for the element type, runs the
elimination, and elaborates a certificate `⟨L, σ, pivot, …⟩ : Echelon.Decomposition A`,
whose conditions are discharged in the kernel, or by the model's leaf certifier when it
supplies one. The elimination itself is the model-parameterized `bareissDecomp` in
`Mathlib.Tactic.Echelon.Core`, and the certificate construction `certifyDecomposition` in
`Mathlib.Tactic.Echelon.Cert`.

## Main definitions

- `mkBareissDecomposition`: produce and elaborate the decomposition of a matrix literal.
- `BareissResult`: the elaborated certificate together with the computed decomposition data.
- `checkBareissApplicable`: the applicability check of the Bareiss method.
- `checkKernelDecide`: check that equality in a ring reduces in the kernel.
- `normNumCertifier`: `norm_num`'s core as a leaf certifier.
- `modelFor`: select the computation model for a ring.
-/

public meta section

open Lean Meta Qq

initialize registerTraceClass `Tactic.evalRank

namespace Mathlib.Tactic.Echelon

/-- Check that equality with zero in `α` reduces to a verdict in the kernel, which decides
whether the certificate conditions can be discharged by `decide` or need a leaf
certifier.
Note that ℝ has a decidableEq instance via classical but isn't usable, so a mere instance
synthesis check is insufficient. -/
def checkKernelDecide {u : Level} (α : Q(Type u)) : MetaM Unit := do
  have _cr : Q(CommRing $α) := ← synthInstanceQ q(CommRing $α)
  -- `Decidable` of the single equality rather than `DecidableEq`: a ring where equality
  -- is only decidable against zero should pass
  let some inst ← synthInstance? q(Decidable (((1 : ℤ) : $α) = 0))
    | throwError "equality with zero in the element type is not decidable{indentExpr α}"
  unless (Kernel.whnf (← getEnv) (← getLCtx) inst).toOption.any
      (·.isAppOf ``Decidable.isFalse) do
    throwError "equality in the element type does not reduce in the kernel{indentExpr α}"

/-- `norm_num`'s core as a leaf certifier. -/
def normNumCertifier : LeafCertifier := fun p => do
  let ⟨b, prf⟩ ← Mathlib.Meta.NormNum.deriveBool p
  return (b, prf)

/-- The applicability check of the Bareiss method, which requires a commutative domain. -/
def checkBareissApplicable (R : Expr) : MetaM (Except MessageData Unit) := do
  let u ← getDecLevel R
  have α : Q(Type u) := R
  let .some _cr ← trySynthInstanceQ q(CommRing $α)
    | return .error m!"expected the element type to be a commutative ring"
  let .some _ ← trySynthInstanceQ q(IsDomain $α)
    | return .error m!"expected the element type to be a domain"
  return .ok ()

/-- Select the computation model for the element type `α`: the first registered
`bareiss_ext` extension that handles it, or the rational fallback. The fallback serves
many rings, so it also probes for its leaf certifier: none where equality reduces in
the kernel, where every certificate condition is decided outright, and `norm_num`
otherwise. -/
def modelFor {u : Level} (α : Q(Type u)) : MetaM Model := do
  for (name, ext) in bareissExt.getState (← getEnv) do
    if let some m ← ext.model? α then
      trace[Tactic.evalRank] "selected the model `{name}` for{indentExpr α}"
      return m
  -- fallback model (rational literals)
  let leaf? ← try
      checkKernelDecide α
      pure none
    catch _ =>
      trace[Tactic.evalRank] "equality in the element type cannot be decided in the \
        kernel; using `norm_num` leaves{indentExpr α}"
      pure (some normNumCertifier)
  return { producer := ← ratProducer α, leafCertifier? := leaf? }

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
  let model ← modelFor α
  let d ← model.producer entries
  have _cr : Q(CommRing $α) := ← synthInstanceQ q(CommRing $α)
  have A : Q(Matrix (Fin $m) (Fin $n) $α) := A
  return { cert := ← certifyDecomposition _cr A entries d model.leafCertifier?, data := d }

end Mathlib.Tactic.Echelon
