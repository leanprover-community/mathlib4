/-
Copyright (c) 2022 Siddhartha Gadgil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Mario Carneiro
-/
import Mathlib.Lean.Meta
import Lean.Elab.Tactic.Location

/-!
# `trans` tactic

This implements the `trans` tactic, which can apply transitivity theorems with an optional middle
variable argument.
-/

namespace Mathlib.Tactic
open Lean Meta Elab

/-- Environment extension storing transitivity lemmas -/
initialize transExt : SimpleScopedEnvExtension (Name × Array DiscrTree.Key) (DiscrTree Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun dt (n, ks) => dt.insertCore ks n
    initial := {}
  }

initialize registerBuiltinAttribute {
  name := `trans
  descr := "transitive relation"
  add := fun decl _ kind => MetaM.run' do
    let declTy := (← getConstInfo decl).type
    let (xs, _, targetTy) ← withReducible <| forallMetaTelescopeReducing declTy
    let fail := throwError
      "@[trans] attribute only applies to lemmas proving x ∼ y → y ∼ z → x ∼ z, got {declTy}"
    let .app (.app rel x₂) z₂ := targetTy | fail
    let some yzHyp := xs.back? | fail
    let some xyHyp := xs.pop.back? | fail
    let .app (.app rel₂ y₂) z₁ ← inferType yzHyp | fail
    let .app (.app rel₁ x₁) y₁ ← inferType xyHyp | fail
    let .true ← withNewMCtxDepth <|
      isDefEq x₁ x₂ <&&> isDefEq y₁ y₂ <&&> isDefEq z₁ z₂ <&&>
      isDefEq rel rel₁ <&&> isDefEq rel rel₂ | fail
    let key ← withReducible <| DiscrTree.mkPath rel
    transExt.add (decl, key) kind
}

/-- Compose two proofs by transitivity, simplified to the homogeneous case. -/
def _root_.Trans.simple {a b c : α} [Trans r r r] : r a b → r b c → r a c := trans

open Lean.Elab.Tactic
/--
`trans` applies to a goal whose target has the form `t ~ u` where `~` is a transitive relation,
that is, a relation which has a transitivity lemma tagged with the attribute [trans].

* `trans s` replaces the goal with the two subgoals `t ~ s` and `s ~ u`.
* If `s` is omitted, then a metavariable is used instead.
-/
elab "trans" t?:(ppSpace (colGt term))? : tactic => withMainContext do
  let tgt ← getMainTarget
  let .app (.app rel x) z := tgt
    | throwError "transitivity lemmas only apply to binary relations, not {indentExpr tgt}"
  let ty ← inferType x
  let t? ← t?.mapM (elabTermWithHoles · ty (← getMainTag))
  let s ← saveState
  for lem in (← (transExt.getState (← getEnv)).getUnify rel).push ``Trans.simple do
    try
      liftMetaTactic fun g => do
        let lemTy ← inferType (← mkConstWithLevelParams lem)
        let arity ← withReducible <| forallTelescopeReducing lemTy fun es _ => pure es.size
        let y ← (t?.map (pure ·.1)).getD (mkFreshExprMVar ty)
        let g₁ ← mkFreshExprMVar (some <| .app (.app rel x) y) .synthetic
        let g₂ ← mkFreshExprMVar (some <| .app (.app rel y) z) .synthetic
        g.assign (← mkAppOptM lem (mkArray (arity - 2) none ++ #[some g₁, some g₂]))
        pure <| [g₁.mvarId!, g₂.mvarId!] ++ if let some (_, gs') := t? then gs' else [y.mvarId!]
      return
    catch _ => s.restore
  throwError "no applicable transitivity lemma found for {indentExpr tgt}"
