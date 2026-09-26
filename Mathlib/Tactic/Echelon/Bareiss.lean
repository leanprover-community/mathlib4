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

initialize registerTraceClass `Tactic.evalRank

namespace Mathlib.Tactic.Echelon

/-- Check whether `decide` reduces the nonzero-ness of a numeral of `α` to a verdict, the shape
of the entry conditions the certificate closes by `decide`. ℝ has a classical `DecidableEq`
instance, so instance synthesis alone does not settle this. -/
def checkDecideEq {u : Level} (α : Q(Type u)) (rα : Q(CommRing $α)) : MetaM Bool := do
  let two : Q($α) ← mkIntNumeral α 2
  -- `Decidable` of the single disequality rather than `DecidableEq`: a ring where equality
  -- is only decidable against zero should pass
  let some _inst ← synthInstanceQ? q(Decidable ($two ≠ 0)) | return false
  let dec := q(decide ($two ≠ 0))
  return (Kernel.whnf (← getEnv) (← getLCtx) dec).toOption.any fun r =>
    r.isConstOf ``Bool.true || r.isConstOf ``Bool.false

/-- `norm_num`'s core as an entry certifier. -/
def normNumCertifier : EntryCertifier := fun p => do
  let ⟨b, prf⟩ ← Mathlib.Meta.NormNum.deriveBool p
  unless b do throwError "norm_num refutes{indentExpr p}"
  return prf

/-- The applicability check of the Bareiss method, which requires a commutative domain. -/
def checkBareissApplicable {u : Level} (α : Q(Type u)) :
    MetaM (Except MessageData Q(CommRing $α)) := do
  let .some rα ← trySynthInstanceQ q(CommRing $α)
    | return .error m!"expected the element type to be a commutative ring"
  let .some _ ← trySynthInstanceQ q(IsDomain $α)
    | return .error m!"expected the element type to be a domain"
  return .ok rα

/-- Select the first registered computation model for the element type `α`, or the default
rational model. The rational model serves many rings, so its entry certifier is probed here
(`none` where `decide` settles equality, `norm_num` otherwise). -/
def modelFor {u : Level} (α : Q(Type u)) (rα : Q(CommRing $α)) :
    MetaM ((c : Carrier) × Model c.type) := do
  for (name, ext) in bareissExt.getState (← getEnv) do
    if let some model ← ext.model? α then
      trace[Tactic.evalRank] "selected the model `{name}` for{indentExpr α}"
      return model
  trace[Tactic.evalRank] "no registered model handles the element type; using the rational \
    model for{indentExpr α}"
  let certifier? ← do
    if ← checkDecideEq α rα then pure none
    else
      trace[Tactic.evalRank] "`decide` cannot settle equality in the element type; \
        using the `norm_num` entry certifier{indentExpr α}"
      pure (some normNumCertifier)
  let ⟨carrier, model⟩ ← ratModel α rα
  return ⟨carrier, { model with entryCertifier? := certifier? }⟩

/-- The result of producer evaluation and certificate construction, together with the carrier
model. -/
structure BareissResult {u : Level} {m n : Nat} {α : Q(Type u)} (rα : Q(CommRing $α))
    (A : Q(Matrix (Fin $m) (Fin $n) $α)) where
  /-- The certificate of the decomposition. -/
  cert : DecompositionCert rα A
  /-- The carrier of the computation model. -/
  carrier : Carrier
  /-- The computation model that produced the decomposition. -/
  model : Model carrier.type
  /-- The decomposition data underlying the certificate, on the model's carrier. -/
  data : BareissData carrier.type

/-- Produce the decomposition of the matrix literal `A` and elaborate its certificate with the
terms and proofs it is assembled from. -/
def mkBareissDecomposition {u : Level} {m n : Nat} {α : Q(Type u)} (rα : Q(CommRing $α))
    (A : Q(Matrix (Fin $m) (Fin $n) $α)) (entries : Array (Array Expr)) :
    MetaM (BareissResult rα A) := do
  let ⟨carrier, model⟩ ← modelFor α rα
  let fractions ← entries.mapM fun row => row.mapM model.evalEntry
  let (values, scales) := scaleRows model.ops model.commonMultiple fractions
  let data := restoreScaling model.ops scales (← bareissDecomp model.ops values)
  let exprData ← data.mapM model.mkEntry
  let cert ← certifyDecomposition rα A entries exprData model.entryCertifier?
  return { cert, carrier, model, data }

end Mathlib.Tactic.Echelon
