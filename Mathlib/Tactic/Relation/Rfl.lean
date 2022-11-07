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
initialize reflExt : SimpleScopedEnvExtension (Name × Array DiscrTree.Key) (DiscrTree Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun dt (n, ks) => dt.insertCore ks n
    initial := {}
  }

initialize registerBuiltinAttribute {
  name := `refl
  descr := "reflexivity relation"
  add := fun decl _ kind => MetaM.run' do
    let declTy := (← getConstInfo decl).type
    let (_, _, targetTy) ← withReducible <| forallMetaTelescopeReducing declTy
    let fail := throwError
      "@[refl] attribute only applies to lemmas proving x ∼ x, got {declTy}"
    let .app (.app rel lhs) rhs := targetTy | fail
    unless ← withNewMCtxDepth <| isDefEq lhs rhs do fail
    let key ← DiscrTree.mkPath rel
    reflExt.add (decl, key) kind
}

open Elab.Tactic in
/--
This tactic applies to a goal whose target has the form `x ~ x`, where `~` is a reflexive
relation, that is, a relation which has a reflexive lemma tagged with the attribute [refl].
-/
elab_rules : tactic
| `(tactic| rfl) => withMainContext do
  let tgt ← getMainTarget
  let .app (.app rel _) _ := tgt
    | throwError "reflexivity lemmas only apply to binary relations, not {indentExpr tgt}"
  let s ← saveState
  for lem in ← (reflExt.getState (← getEnv)).getMatch rel do
    try
      liftMetaTactic (·.apply (← mkConstWithFreshMVarLevels lem))
      return
    catch e =>
      s.restore
      throw e
  throwError "rfl failed, no lemma with @[refl] applies"
