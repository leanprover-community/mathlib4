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
with the certificate conditions checked by the kernel via `decide`. The elimination
itself is the model-parameterized `bareissDecomp` in `Mathlib.Tactic.Echelon.Core`, and
the certificate construction `mkCertificate` in `Mathlib.Tactic.Echelon.Cert`.
-/

public meta section

open Lean Meta Qq

initialize registerTraceClass `Tactic.evalRank

namespace Mathlib.Tactic.Echelon

/-- The applicability check of the Bareiss method, which requires a commutative domain
with kernel-decidable equality. -/
def checkBareissApplicable {u : Level} (α : Q(Type u)) :
    MetaM (Except MessageData Q(CommRing $α)) := do
  let .some rα ← trySynthInstanceQ q(CommRing $α)
    | return .error m!"expected the element type to be a commutative ring"
  let .some _ ← trySynthInstanceQ q(IsDomain $α)
    | return .error m!"expected the element type to be a domain"
  try
    checkKernelDecide α rα
  catch e =>
    return .error e.toMessageData
  return .ok rα

/-- Select the first registered computation model for the element type `α`, or the default
rational model. -/
def modelFor {u : Level} (α : Q(Type u)) (rα : Q(CommRing $α)) :
    MetaM ((c : Carrier) × Model c.type) := do
  for (name, ext) in bareissExt.getState (← getEnv) do
    if let some model ← ext.model? α then
      trace[Tactic.evalRank] "selected the model `{name}` for{indentExpr α}"
      return model
  trace[Tactic.evalRank] "no registered model handles the element type; using the rational \
    model for{indentExpr α}"
  ratModel α rα

/-- The result of producer evaluation and certificate construction, together with the carrier
model. -/
structure BareissResult where
  /-- The elaborated `Echelon.Decomposition` certificate term. -/
  cert : Expr
  /-- The carrier of the computation model. -/
  carrier : Carrier
  /-- The computation model that produced the decomposition. -/
  model : Model carrier.type
  /-- The decomposition data underlying the certificate, on the model's carrier. -/
  data : BareissData carrier.type

/-- Produce and elaborate the `Echelon.Decomposition` certificate of the matrix literal
`A`. -/
def mkBareissDecomposition {u : Level} {m n : Nat} {α : Q(Type u)} (rα : Q(CommRing $α))
    (A : Q(Matrix (Fin $m) (Fin $n) $α)) (entries : Array (Array Expr)) :
    MetaM BareissResult := do
  let ⟨carrier, model⟩ ← modelFor α rα
  let fractions ← entries.mapM fun row => row.mapM model.evalEntry
  let (values, scales) := scaleRows model.ops model.commonMultiple fractions
  let data := restoreScaling model.ops scales (← bareissDecomp model.ops values)
  let d ← data.mapM model.mkEntry
  return { cert := ← mkCertificate rα A entries d, carrier, model, data }

end Mathlib.Tactic.Echelon
