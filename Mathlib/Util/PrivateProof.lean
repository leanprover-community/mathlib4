/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public meta import Lean.Elab.Term
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public import Mathlib.Tactic.Linter.Header  -- shake: keep

/-!
# `private` wrapper for proof terms

A simple elaborator that wraps term-mode proofs in auxiliary lemmas if possible. This allows the
user to reference private declarations in term-mode proofs.

`private_decl%` exists in core, but (1) does not have the syntax we want (2) does not warn if
unnecessary (3) also produces definitions, and thus is more "dangerous".

## Implementation notes

This postpones until the expected type is available (`<= ty`). `withSynthesize` and
`elabTermEnsuringType` mirror `by exact`'s behavior. We avoid elaborating an actual `by exact`
since this would let through a public term under `backward.proofsInPublic`, which we want to ignore.

We use `withSynthesize (postpone := .partial)` because `postpone := .yes` allows nested `by`'s
within the wrapped term to escape, and thus they may still error when useing private definitions
(if used to construct data within the wrapped proof), and `postpone := .no` can cause timing
friction that `by exact` avoids.

`private%` was considered, but this interferes with the parsing of antiquotations like
`$[private%$tk]` (for e.g. `private` modifiers on declarations).
-/

namespace Mathlib.Tactic.PrivateProof

/-- Warn when the `private ...` proof term elaborator is unnecessary (either because private
definitions are already available, or `backward.privateInPublic` is `true`). -/
public meta register_option linter.privateProof.warnIfUnnecessary : Bool := {
  defValue := true
  descr := "warn when the `private` proof term elaborator is unnecessary"
}

/-- Wraps a proof term in a public auxiliary lemma so that it may contain private declarations
without erroring. This is acceptable due to proof irrelevance.

Note that `by ...` already wraps terms in auxiliary lemmas if possible; `private` may be preferred
on bare terms over `by exact` to communicate intent.

If the term is not known to be a proof, `private` fails.

Note that `field := private ...` for structure instances is distinct, and allows wrapping data in
auxiliary definitions as well. See also `private_decl%` for similar behavior that also includes
non-proof declarations. -/
syntax (name := privateElab) "private " term : term

open Lean Meta Elab Term in
elab_rules : term <= ty
| `(private%$tk $t) => withRef t do
  if ← linter.privateProof.warnIfUnnecessary.getM then
    if !(← getEnv).isExporting then
      logWarningAt tk "`private` is unnecessary, since private declarations are already usable."
    else if ← ResolveName.backward.privateInPublic.getM then
      logWarningAt tk "`private` is unnecessary, since `backward.privateInPublic` is `true`."
  -- If definitely not a prop, log an error and proceed. We log errors at the (ambient) term
  -- instead of the `private` token, since the term is "at fault".
  if ← notM (isProp ty) <&&> return !(← instantiateMVars <|← inferType ty).hasMVar then
    logError m!"`private` can only wrap proofs, but \
      the expected type is not a `Prop`.\
      {indentD ty} : {← inferType ty}\n\n\
      Use `private_decl%` to wrap a non-proof term in an auxiliary definition."
    Term.elabTerm t ty (implicitLambda := false)
  else
    let e ← instantiateMVars <|← withoutExporting do withSynthesize (postpone := .partial) do
      Term.elabTermEnsuringType t ty (implicitLambda := false)
    if !(← isProp ty) then
      let knownToBe? := if (← instantiateMVars ty).hasMVar then " known to be" else ""
      logError m!"`private` can only wrap proofs, but \
        the expected type of `{e}` is not{knownToBe?} a `Prop`.\
        {indentD ty} : {← inferType ty}\n\n\
        Use `private_decl%` to wrap a non-proof term in an auxiliary definition."
      return e
    else if e.isFVar then
      if ← linter.privateProof.warnIfUnnecessary.getM then
        logWarningAt tk m!"`private` is unnecessary, since the resulting expression is just a free \
          variable:{indentD e} : {ty}"
      return e
    else
      mkAuxTheorem ty e (zetaDelta := true) (cache := !e.hasSorry)
