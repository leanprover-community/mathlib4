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

open Lean Meta

namespace Mathlib.Tactic

/-- Environment extensions for symm lemmas -/
initialize symmExt :
    SimpleScopedEnvExtension (Name × Array (DiscrTree.Key true)) (DiscrTree Name true) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun dt (n, ks) ↦ dt.insertCore ks n
    initial := {}
  }

initialize registerBuiltinAttribute {
  name := `symm
  descr := "symmetric relation"
  add := fun decl _ kind ↦ MetaM.run' do
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

end Mathlib.Tactic

namespace Lean.MVarId
open Mathlib.Tactic

/--
Internal implementation of `Lean.MVarId.symm` and of the user-facing tactic.

`tgt` should be of the form `a ~ b`, and is used to index the symm lemmas.

`k lem args body goal` should transform `goal` into a new goal,
given a candidate `symm` lemma `lem`, which will have type `∀ args, body`.
Depending on whether we are working on a hypothesis or a goal,
`k` will internally use either `replace` or `assign`.
-/
def symmAux (tgt : Expr) (k : Expr → Array Expr → Expr → MVarId → MetaM MVarId) (g : MVarId) :
    MetaM MVarId := do
  let .app (.app rel _) _ := tgt
    | throwError "symmetry lemmas only apply to binary relations, not{indentExpr tgt}"
  for lem in ← (symmExt.getState (← getEnv)).getMatch rel do
    try
      let lem ← mkConstWithFreshMVarLevels lem
      let (args, _, body) ← withReducible <| forallMetaTelescopeReducing (← inferType lem)
      let g' ← k lem args body g
      g'.setTag (← g.getTag)
      return g'
    catch _ => pure ()
  throwError "no applicable symmetry lemma found for{indentExpr tgt}"

/-- Apply a symmetry lemma (i.e. marked with `@[symm]`) to a metavariable. -/
def symm (g : MVarId) : MetaM MVarId := do
  g.symmAux (← g.getType) fun lem args body g => do
    let .true ← isDefEq (← g.getType) body | failure
    g.assign (mkAppN lem args)
    return args.back.mvarId!

end Lean.MVarId

namespace Mathlib.Tactic

open Lean.Elab.Tactic in
/--
* `symm` applies to a goal whose target has the form `t ~ u` where `~` is a symmetric relation,
  that is, a relation which has a symmetry lemma tagged with the attribute [symm].
  It replaces the target with `u ~ t`.
* `symm at h` will rewrite a hypothesis `h : t ~ u` to `h : u ~ t`.
-/
elab "symm" loc:((Parser.Tactic.location)?) : tactic =>
  let atHyp h := liftMetaTactic1 fun g => do
    g.symmAux (← h.getType) fun lem args body g => do
      let .true ← isDefEq args.back (.fvar h) | failure
      pure (← g.replace h (← instantiateMVars body) (mkAppN lem args)).mvarId
  let atTarget := liftMetaTactic1 fun g => g.symm
  withLocation (expandOptLocation loc) atHyp atTarget fun _ ↦ throwError "symm made no progress"
