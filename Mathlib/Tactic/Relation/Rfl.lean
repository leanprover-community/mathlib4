/-
Copyright (c) 2022 Newell Jensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Newell Jensen
-/
import Lean

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
  add := fun decl _ kind ↦ MetaM.run' do
    let declTy := (← getConstInfo decl).type
    let (_, _, targetTy) ← withReducible <| forallMetaTelescopeReducing declTy
    let fail := throwError
      "@[refl] attribute only applies to lemmas proving x ∼ x, got {declTy}"
    let .app (.app rel lhs) rhs := targetTy | fail
    unless ← withNewMCtxDepth <| isDefEq lhs rhs do fail
    let key ← DiscrTree.mkPath rel
    reflExt.add (decl, key) kind
}

/-- `MetaM` version of the `rfl` tactic.

This tactic applies to a goal whose target has the form `x ~ x`, where `~` is a reflexive
relation, that is, a relation which has a reflexive lemma tagged with the attribute [refl].
-/
def _root_.Lean.MVarId.rfl (goal : MVarId) : MetaM (List MVarId) := do
  let .app (.app rel _) _ ← whnfR <|← instantiateMVars <|← goal.getType
    | throwError "reflexivity lemmas only apply to binary relations, not
      {indentExpr (← goal.getType)}"
  let s ← saveState
  for lem in ← (reflExt.getState (← getEnv)).getMatch rel do
    try
      return ← goal.apply (← mkConstWithFreshMVarLevels lem)
    catch e =>
      s.restore
      throw e
  throwError "rfl failed, no lemma with @[refl] applies"

open Elab.Tactic in
/--
This tactic applies to a goal whose target has the form `x ~ x`, where `~` is a reflexive
relation, that is, a relation which has a reflexive lemma tagged with the attribute [refl].
-/
elab_rules : tactic
| `(tactic| rfl) => withMainContext do liftMetaTactic (·.rfl)
