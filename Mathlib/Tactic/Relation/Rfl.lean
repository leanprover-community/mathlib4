/-
Copyright (c) 2022 Newell Jensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Newell Jensen
-/

import Lean
import Mathlib.Tactic.Relation.Basic

namespace Mathlib.Tactic.Relation.Rfl

open Lean Meta

/-- Environment extensions for `refl` lemmas -/
initialize reflExtension : SimpleScopedEnvExtension (Name × Array DiscrTree.Key)
(DiscrTree Name) ← registerSimpleScopedEnvExtension {
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
      let (xs, _, targetTy) ← withReducible <| forallMetaTelescopeReducing declTy
      if xs.size < 1 then
        throwError "@[refl] attribute only applies to lemmas proving x ∼ x, got {declTy} with
        too few arguments"
      else
        match ← relationAppM? targetTy with
        | some (rel, lhs, rhs) =>
          unless (← isDefEq lhs rhs) do
            throwError "@[refl] attribute only applies to lemmas proving x ∼ x, got {declTy}
            with {lhs} ~ {rhs} instead"
          let key ← withReducible <| DiscrTree.mkPath rel
          reflExtension.add (decl, key) kind
        | none =>
          throwError "@[refl] attribute only applies to lemmas proving x ∼ x, got {declTy}"

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
  match ← relationAppM? tgt with
  | some (rel, _, _) =>
    let s ← saveState
    for lem in ← (reflLemmas (← getEnv)).getMatch rel do
      try
        liftMetaTactic (MVarId.apply · (← mkConstWithFreshMVarLevels lem))
        return
      catch _ =>
        s.restore
  | none =>
    throwError "reflexivity lemmas only apply to binary relations, not{indentExpr tgt}"
