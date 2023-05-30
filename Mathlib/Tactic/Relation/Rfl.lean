/-
Copyright (c) 2022 Newell Jensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Newell Jensen
-/
import Lean
import Mathlib.Lean.Meta
import Mathlib.Lean.Expr.Basic

/-!
# `rfl` tactic extension for reflexive relations

This extends the `rfl` tactic so that it works on any reflexive relation,
provided the reflexivity lemma has been marked as `@[refl]`.
-/

namespace Mathlib.Tactic

open Lean Meta

/-- Environment extensions for `refl` lemmas -/
initialize reflExt :
    SimpleScopedEnvExtension (Name × Array (DiscrTree.Key true)) (DiscrTree Name true) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun dt (n, ks) ↦ dt.insertCore ks n
    initial := {}
  }

initialize registerBuiltinAttribute {
  name := `refl
  descr := "reflexivity relation"
  add := fun decl _ kind ↦ MetaM.run' <| withReducible do
    let declTy := (← getConstInfo decl).type
    let (_, _, targetTy) ← forallMetaTelescope declTy
    let fail := throwError
      "@[refl] attribute only applies to lemmas proving x ∼ x, got {declTy} with target {targetTy}"
    let xx ← targetTy.getNumExplicitArgs 2
    unless ← withNewMCtxDepth <| isDefEq xx[0]! xx[1]! do fail
    let key ← DiscrTree.mkPath (← whnfR targetTy)
    reflExt.add (decl, key) kind
}

open Elab Tactic

/-- `MetaM` version of the `rfl` tactic.

This tactic applies to a goal whose target has the form `x ~ x`, where `~` is a reflexive
relation, that is, a relation which has a reflexive lemma tagged with the attribute [refl].
-/
def _root_.Lean.MVarId.rfl (goal : MVarId) : MetaM Unit := do
  let t ← whnfR <|← instantiateMVars <|← goal.getType
  let s ← saveState
  let mut ex? := none
  for lem in ← (reflExt.getState (← getEnv)).getMatch t do
    try
      let gs ← goal.apply (← mkConstWithFreshMVarLevels lem)
      if gs.isEmpty then return () else
        logError <| MessageData.tagged `Tactic.unsolvedGoals <| m!"unsolved goals\n
          {goalsToMessageData gs}"
    catch e =>
      ex? := ex? <|> (some (← saveState, e)) -- stash the first failure of `apply`
    s.restore
  if let some (sErr, e) := ex? then
    sErr.restore
    throw e
  else
    throwError "rfl failed, no lemma with @[refl] applies"

/--
This tactic applies to a goal whose target has the form `x ~ x`, where `~` is a reflexive
relation, that is, a relation which has a reflexive lemma tagged with the attribute [refl].
-/
elab_rules : tactic
| `(tactic| rfl) => withMainContext do liftMetaFinishingTactic (·.rfl)
