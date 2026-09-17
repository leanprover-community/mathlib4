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
elimination, and elaborates the certificate of the decomposition with the terms and proofs it
is assembled from.
The elimination itself is the model-parameterized `bareissDecomp` in
`Mathlib.Tactic.Echelon.Core`, and the certificate construction `certifyDecomposition` in
`Mathlib.Tactic.Echelon.Cert`.

## Main definitions

- `mkBareissDecomposition`: produce and elaborate the decomposition of a matrix literal.
- `BareissResult`: the decomposition data and its certificate with the terms and proofs it is
  assembled from.
- `checkBareissApplicable`: the applicability check of the Bareiss method.
- `checkDecideEq`: check whether `decide` settles equality in a ring.
- `normNumCertifier`: `norm_num`'s core as an entry certifier.
- `modelFor`: select the computation model for a ring.
-/

public meta section

open Lean Meta Qq

initialize registerTraceClass `Tactic.evalRank

namespace Mathlib.Tactic.Echelon

/-- Check whether the equality with zero in `α` directly reduces to a verdict by `decide`.
Note that ℝ has a `DecidableEq` instance via classical that isn't usable, so a mere instance
synthesis check is insufficient. -/
def checkDecideEq {u : Level} (α : Q(Type u)) : MetaM Bool := do
  have _cr : Q(CommRing $α) := ← synthInstanceQ q(CommRing $α)
  -- `Decidable` of the single equality rather than `DecidableEq`: a ring where equality
  -- is only decidable against zero should pass
  let some _inst ← synthInstanceQ? q(Decidable (((1 : ℤ) : $α) = 0)) | return false
  let d := q(decide (((1 : ℤ) : $α) = 0))
  return (Kernel.whnf (← getEnv) (← getLCtx) d).toOption.any (·.isConstOf ``Bool.false)

/-- `norm_num`'s core as an entry certifier. -/
def normNumCertifier : EntryCertifier := fun p => do
  let ⟨b, prf⟩ ← Mathlib.Meta.NormNum.deriveBool p
  unless b do throwError "norm_num refutes{indentExpr p}"
  return prf

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
many rings, so it also probes for its entry certifier: none where `decide` settles
equality, and `norm_num` otherwise. -/
def modelFor {u : Level} (α : Q(Type u)) : MetaM Model := do
  for (name, ext) in bareissExt.getState (← getEnv) do
    if let some m ← ext.model? α then
      trace[Tactic.evalRank] "selected the model `{name}` for{indentExpr α}"
      return m
  -- fallback model (rational literals)
  let certifier? ← do
    if ← checkDecideEq α then pure none
    else
      trace[Tactic.evalRank] "`decide` cannot settle equality in the element type; \
        using the `norm_num` entry certifier{indentExpr α}"
      pure (some normNumCertifier)
  return { producer := ← ratProducer (u := u) α, entryCertifier? := certifier? }

/-- The result of producing a decomposition by Bareiss: the decomposition data and its
`DecompositionCert`. -/
structure BareissResult {u : Level} {m n : ℕ} {α : Q(Type u)} (_cr : Q(CommRing $α))
    (A : Q(Matrix (Fin $m) (Fin $n) $α)) where
  /-- The decomposition data, as computed by the producer. -/
  data : BareissData Expr
  /-- The certificate, as constructed by the certifier. -/
  cert : DecompositionCert _cr A

/-- Produce the decomposition of the matrix literal `A` and elaborate its certificate with the
terms and proofs it is assembled from. -/
def mkBareissDecomposition {u : Level} {m n : ℕ} {α : Q(Type u)} (_cr : Q(CommRing $α))
    (A : Q(Matrix (Fin $m) (Fin $n) $α)) (entries : Array (Array Expr)) :
    MetaM (BareissResult _cr A) := do
  let model ← modelFor α
  let d ← model.producer entries
  return { data := d, cert := ← certifyDecomposition _cr A entries d model.entryCertifier? }

end Mathlib.Tactic.Echelon
