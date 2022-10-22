/-
Copyright (c) 2022 Siddhartha Gadgil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Mario Carneiro
-/
import Mathlib.Lean.Meta
import Lean.Elab.Tactic.Location

/-!
# `symm` tactic

This implements the `symm` tactic, which can apply symmetry theorems to either the goal or a
hypothesis.
-/

namespace Mathlib.Tactic
open Lean Meta

/-- Environment extensions for symm lemmas -/
initialize symmExt : SimpleScopedEnvExtension (Name × Array DiscrTree.Key) (DiscrTree Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun dt (n, ks) => dt.insertCore ks n
    initial := {}
  }

initialize registerBuiltinAttribute {
  name := `symm
  descr := "symmetric relation"
  add := fun decl _ kind => MetaM.run' do
    let declTy := (← getConstInfo decl).type
    let (xs, _, targetTy) ← withReducible <| forallMetaTelescopeReducing declTy
    let fail := throwError
      "@[symm] attribute only applies to lemmas proving x ∼ y → y ∼ x, got {declTy}"
    let some finalHyp := xs.back? | fail
    let .app (.app rel lhs) rhs := targetTy | fail
    let flip := .app (.app rel rhs) lhs
    let .true ← withNewMCtxDepth <| isDefEqGuarded flip (← inferType finalHyp) | fail
    let key ← withReducible <| DiscrTree.mkPath rel
    symmExt.add (decl, key) kind
}

open Lean.Elab.Tactic in
/--
* `symm` applies to a goal whose target has the form `t ~ u` where `~` is a symmetric relation,
  that is, a relation which has a symmetry lemma tagged with the attribute [symm].
  It replaces the target with `u ~ t`.
* `symm at h` will rewrite a hypothesis `h : t ~ u` to `h : u ~ t`.
-/
elab "symm" loc:((Parser.Tactic.location)?) : tactic =>
  let onRel (tgt : Expr) (k : MVarId → Expr → MetaM MVarId) : TacticM Unit := do
    let .app (.app rel _) _ := tgt
      | throwError "symmetry lemmas only apply to binary relations, not{indentExpr tgt}"
    let s ← saveState
    for lem in ← (symmExt.getState (← getEnv)).getMatch rel do
      try
        liftMetaTactic1 fun g => do
          let g' ← k g (← mkConstWithFreshMVarLevels lem)
          g'.setTag (← g.getTag)
          pure g'
        return
      catch _ => s.restore
    throwError "no applicable symmetry lemma found for{indentExpr tgt}"
  let atHyp h := do
    onRel (← h.getType) fun g e => do
      let (xs, _, targetTy) ← withReducible <| forallMetaTelescopeReducing (← inferType e)
      let .true ← isDefEq xs.back (.fvar h) | failure
      pure (← g.replace h (← instantiateMVars targetTy) (mkAppN e xs)).mvarId
  let atTarget := withMainContext do
    onRel (← getMainTarget) fun g e => do
      let (xs, _, targetTy) ← withReducible <| forallMetaTelescopeReducing (← inferType e)
      let .true ← isDefEq (← g.getType) targetTy | failure
      g.assign (mkAppN e xs)
      pure xs.back.mvarId!
  withLocation (expandOptLocation loc) atHyp atTarget fun _ => throwError "symm made no progress"
