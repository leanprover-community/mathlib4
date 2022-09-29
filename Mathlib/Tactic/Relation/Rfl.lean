/-
Copyright (c) 2022 Newell Jensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Newell Jensen
-/

import Lean

namespace Mathlib.Tactic.Relation.Rfl

open Lean Meta

/-- Environment extensions for `refl` lemmas -/
initialize reflExtension : SimpleScopedEnvExtension (Name × Array DiscrTree.Key) (DiscrTree Name) ←
  registerSimpleScopedEnvExtension {
    name := `refl
    addEntry := fun dt (n, ks) => dt.insertCore ks n
    initial := {}
  }

/-- add reflexivity attribute if valid -/
def reflAttr : AttributeImpl where
  name := `refl
  descr := "reflexivity relation"
  add decl _ kind := do
    MetaM.run' do
      let declTy := (← getConstInfo decl).type
      let (_, _, targetTy) ← withReducible <| forallMetaTelescopeReducing declTy
      let fail := throwError
        "@[refl] attribute only applies to lemmas proving x ∼ x, got {declTy}"
      let .app (.app rel lhs) rhs := targetTy | fail
      unless ← isDefEq lhs rhs do fail
      let key ← withReducible <| DiscrTree.mkPath rel
      reflExtension.add (decl, key) kind

initialize registerBuiltinAttribute reflAttr


/-- look up reflexivity lemmas -/
def reflLemmas (env : Environment) : DiscrTree Name :=
  reflExtension.getState env

open Lean.Elab.Tactic in

/-- This tactic applies to a goal whose target has the form `x ~ x`, where `~` is a reflexive
relation, that is, a relation which has a reflexive lemma tagged with the attribute [refl].
-/
elab_rules : tactic
| `(tactic| rfl) =>
  withMainContext do
  let tgt ← getMainTarget
  let .app (.app rel _) _ := tgt
    | throwError "reflexivity lemmas only apply to binary relations, not {indentExpr tgt}"
  let s ← saveState
  for lem in ← (reflLemmas (← getEnv)).getMatch rel do
    try
      liftMetaTactic (·.apply (← mkConstWithFreshMVarLevels lem))
      return
    catch e =>
      s.restore
      throw e
  throwError "rfl failed, no lemma with @[refl] applies"
