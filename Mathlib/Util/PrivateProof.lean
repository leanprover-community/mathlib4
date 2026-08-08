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

This postpones until the expected type is available (`<= ty`), then elaborates the term itself
outside the exporting context and abstracts the result into a public auxiliary theorem. We do not
route through `by as_aux_lemma => exact ...`: `by` already abstracts proofs into auxiliary theorems
itself, but only when `backward.proofsInPublic` is `false`, and only that route understands how to
leave the exporting context. Depending on it would make `private` a no-op under that option, and
`as_aux_lemma` on top of it would emit a redundant second auxiliary theorem.

`private%` was considered, but this interferes with the parsing of antiquotations like
`$[private%$tk]` (for e.g. `private` modifiers on declarations).
-/

namespace Mathlib.Tactic.PrivateProof

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
  -- Do not check `backward.proofsInPublic`; if the user is using `private`, it's intentional.
  -- Use `implicitLambda := false` since term elaboration will have already taken care of this, and
  -- e.g. `@(private ..)` should elaborate without implicit lambda insertions.
  if !(← getEnv).isExporting then
    logWarningAt tk "`private` is unnecessary, since private declarations are already usable."
    Term.elabTerm t ty (implicitLambda := false)
  else if ← ResolveName.backward.privateInPublic.getM then
    logWarningAt tk "`private` is unnecessary, since `backward.privateInPublic` is `true`."
    Term.elabTerm t ty (implicitLambda := false)
  else if !(← isProp ty) then
    let hasMVar := (← instantiateMVars <|← inferType ty).hasMVar
    if hasMVar then
      -- Try elaborating then wrapping
      let (ty, e) ← withoutExporting do
        let e ← Term.elabTermAndSynthesize t ty
        pure (← inferType e, e)
      -- Check once more
      if !(← isProp ty) then
        let knownToBe? := if ty.hasMVar then " known to be" else ""
        logError m!"`private` can only wrap proofs; \
          the expected type of `{e}` is not{knownToBe?} a `Prop`.\
          {indentD ty} : {← inferType ty}"
        return e
      else mkAuxTheorem ty e (zetaDelta := true)
    else
      logError m!"`private` can only wrap proofs; the expected type is not a `Prop`.\
        {indentD ty} : {← inferType ty}"
      Term.elabTerm t ty (implicitLambda := false)
  else
    -- Elaborate outside the exporting context so private declarations resolve, then abstract the
    -- result into an auxiliary theorem ourselves. Note that `mkAuxTheorem` runs while exporting, so
    -- the auxiliary theorem is public.
    --
    -- We deliberately do not delegate to `by as_aux_lemma => exact ...`: `by` only leaves the
    -- exporting context when `backward.proofsInPublic` is `false` (see `Lean.Elab.Term.runTactic`),
    -- which we do not want to depend on, and it already abstracts its result into an auxiliary
    -- theorem, so `as_aux_lemma` would add a redundant second one.
    -- Use `elabTermEnsuringType`, not `elabTerm`: a type mismatch must be reported here rather
    -- than escaping into the auxiliary theorem, where only the kernel would catch it.
    let e ← withoutExporting do
      instantiateMVars (← Term.withSynthesize <|
        Term.elabTermEnsuringType t ty (implicitLambda := false))
    -- Nothing to hide behind an auxiliary theorem if the proof is just a local hypothesis.
    if e.isFVar then return e
    mkAuxTheorem ty e (zetaDelta := true) (cache := !e.hasSorry)
