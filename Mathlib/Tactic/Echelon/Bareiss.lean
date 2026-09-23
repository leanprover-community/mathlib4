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
-/

public meta section

open Lean Meta Qq

initialize registerTraceClass `Tactic.evalRank

namespace Mathlib.Tactic.Echelon

/-- Check whether the equality with zero in `α` directly reduces to a verdict by `decide`.
Note that ℝ has a `DecidableEq` instance via classical that isn't usable, so a mere instance
synthesis check is insufficient. -/
def checkDecideEq {u : Level} (α : Q(Type u)) (_cr : Q(CommRing $α)) : MetaM Bool := do
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
def checkBareissApplicable {u : Level} (α : Q(Type u)) :
    MetaM (Except MessageData Q(CommRing $α)) := do
  let .some _cr ← trySynthInstanceQ q(CommRing $α)
    | return .error m!"expected the element type to be a commutative ring"
  let .some _ ← trySynthInstanceQ q(IsDomain $α)
    | return .error m!"expected the element type to be a domain"
  return .ok _cr

/-- Select the first registered computation model for the element type `α`, or the default
rational model. The rational model serves many rings, so its entry certifier is probed here
(`none` where `decide` settles equality, `norm_num` otherwise). -/
def modelFor {u : Level} (α : Q(Type u)) (_cr : Q(CommRing $α)) :
    MetaM ((c : Carrier) × Model c.type) := do
  for (name, ext) in bareissExt.getState (← getEnv) do
    if let some model ← ext.model? α then
      trace[Tactic.evalRank] "selected the model `{name}` for{indentExpr α}"
      return model
  trace[Tactic.evalRank] "no registered model handles the element type; using the rational \
    model for{indentExpr α}"
  let certifier? ← do
    if ← checkDecideEq α _cr then pure none
    else
      trace[Tactic.evalRank] "`decide` cannot settle equality in the element type; \
        using the `norm_num` entry certifier{indentExpr α}"
      pure (some normNumCertifier)
  let ⟨carrier, model⟩ ← ratModel α _cr
  return ⟨carrier, { model with entryCertifier? := certifier? }⟩

/-- The result of producer evaluation and certificate construction, together with the carrier
model. -/
structure BareissResult {u : Level} {m n : ℕ} {α : Q(Type u)} (_cr : Q(CommRing $α))
    (A : Q(Matrix (Fin $m) (Fin $n) $α)) where
  /-- The certificate, as constructed by the certifier. -/
  cert : DecompositionCert _cr A
  /-- The carrier of the computation model. -/
  carrier : Carrier
  /-- The computation model that produced the decomposition. -/
  model : Model carrier.type
  /-- The decomposition data underlying the certificate, on the model's carrier. -/
  data : BareissData carrier.type

/-- Produce the decomposition of the matrix literal `A` and elaborate its certificate with the
terms and proofs it is assembled from. -/
def mkBareissDecomposition {u : Level} {m n : ℕ} {α : Q(Type u)} (_cr : Q(CommRing $α))
    (A : Q(Matrix (Fin $m) (Fin $n) $α)) (entries : Array (Array Expr)) :
    MetaM (BareissResult _cr A) := do
  let ⟨carrier, model⟩ ← modelFor α _cr
  let fractions ← entries.mapM fun row => row.mapM model.evalEntry
  let (values, scales) := scaleRows model.ops model.commonMultiple fractions
  let data := restoreScaling model.ops scales (← bareissDecomp model.ops values)
  let d ← data.mapM model.mkEntry
  let cert ← certifyDecomposition _cr A entries d model.entryCertifier?
  return { cert, carrier, model, data }

end Mathlib.Tactic.Echelon
