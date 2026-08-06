/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public meta import Lean.Elab.Term

namespace Mathlib.Tactic.PrivateProof

/-- Wraps a term in a public aux lemma so that it may contain private declarations. -/
syntax (name := privateElab) "private " term : term

open Lean Meta Elab Term in
elab_rules : term <= ty
| `(private%$tk $t) => do
  -- Do not check `backward.proofsInPublic`; if the user is using `private%`, it's intentional.
  if !(← getEnv).isExporting then
    logWarningAt tk "`private` is unnecessary, since private declarations are already usable."
    Term.elabTerm t ty (implicitLambda := false)
  else if ← ResolveName.backward.privateInPublic.getM then
    logWarningAt tk "`private` is unnecessary, since `backward.privateInPublic` is `true`."
    Term.elabTerm t ty (implicitLambda := false)
  else if !(← isProp ty) then
    logError m!"`private` can only wrap proofs; the expected type is {ty} : {← inferType ty}"
    Term.elabTerm t ty (implicitLambda := false)
  else
    -- `by exact` should be sufficient for extraction into an aux lemma, but just to insist on it.
    Term.elabTerm (← `(term| by as_aux_lemma => exact $t)) ty (implicitLambda := false)
