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
elimination, and elaborates the certificate of the decomposition.
The elimination itself is the model-parameterized `bareissDecomp` in
`Mathlib.Tactic.Echelon.Core`, and the certificate construction `certifyDecomposition` in
`Mathlib.Tactic.Echelon.Cert`.
-/

public meta section

open Lean Meta Qq

namespace Mathlib.Tactic.Echelon

/-- The applicability check of the Bareiss method, which requires a commutative domain. -/
def inferBareissRing {u : Level} (α : Q(Type u)) :
    MetaM (Except MessageData Q(CommRing $α)) := do
  let .some rα ← trySynthInstanceQ q(CommRing $α)
    | return .error m!"expected the element type to be a commutative ring"
  let .some _ ← trySynthInstanceQ q(IsDomain $α)
    | return .error m!"expected the element type to be a domain"
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
  return ⟨.int, ← ratModel α rα⟩

/-- The result of producer evaluation and certificate construction, together with the computation
model. -/
structure BareissResult {u : Level} {m n : Nat} {α : Q(Type u)} (rα : Q(CommRing $α))
    (A : Q(Matrix (Fin $m) (Fin $n) $α)) where
  /-- The decomposition certificate with its reusable intermediate certificates. -/
  cert : DecompositionCert rα A
  /-- The carrier of the computation model. -/
  carrier : Carrier
  /-- The computation model that produced the decomposition. -/
  model : Model carrier.type
  /-- The decomposition data underlying the certificate, on the model's carrier. -/
  data : BareissData carrier.type

/-- Produce the decomposition of the matrix literal `A` and elaborate its certificates. -/
def mkBareissDecomposition {u : Level} {m n : Nat} {α : Q(Type u)} (rα : Q(CommRing $α))
    (A : Q(Matrix (Fin $m) (Fin $n) $α)) (entries : Array (Array Q($α))) :
    MetaM (BareissResult rα A) := do
  let ⟨carrier, model⟩ ← modelFor α rα
  let fractions ← entries.mapM fun row => row.mapM model.evalEntry
  let (values, scales) := scaleRows model.ops model.commonMultiple fractions
  let data := restoreScaling model.ops scales (← bareissDecomp model.ops values)
  let exprData ← data.mapM model.mkEntry
  let cert ← certifyDecomposition rα A entries exprData model.entryCertifier?
  return { cert, carrier, model, data }

end Mathlib.Tactic.Echelon
