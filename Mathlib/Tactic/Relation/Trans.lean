/-
Copyright (c) 2022 Siddhartha Gadgil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Mario Carneiro, Scott Morrison
-/
import Mathlib.Lean.Meta
import Mathlib.Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Location
import Std.Tactic.Exact

/-!
# `trans` tactic

This implements the `trans` tactic, which can apply transitivity theorems with an optional middle
variable argument.
-/

set_option autoImplicit true

namespace Mathlib.Tactic
open Lean Meta Elab

initialize registerTraceClass `Tactic.trans

/-- Given an expression of the form `r x y` with implicit arguments,
returns `(r, x, y)`. Otherwise returns `none`.
Does not ensure that `r x y` elaborates.

Assumption: `e` is in the form
`r (... implicit arguments ...) x (... implicit arguments ...) y (... implicit arguments ...)`
where `r` contains all those implicit arguments that both `x` and `y` depend on. -/
def _root_.Lean.Expr.rel? (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let f := e.getAppFn
  let args := e.getAppArgs
  let info ← getFunInfoNArgs f args.size
  -- Indices to the explicit arguments:
  let eidxs := (List.range args.size).filter fun i => info.paramInfo[i]!.isExplicit
  unless eidxs.length ≥ 2 do
    return none
  -- xi and yi are the indices to the arguments being related
  let xi := eidxs[eidxs.length - 2]!
  let yi := eidxs[eidxs.length - 1]!
  -- minArgs is the minimum number of arguments to f for the relation itself
  let minArgs := if eidxs.length = 2 then 0 else eidxs[eidxs.length - 3]!
  -- Now we need to figure out how many implicit arguments to include before xi
  let mut relArgs := minArgs
  for i in [minArgs : xi] do
    let xdep := info.paramInfo[xi]!.backDeps.contains i
    let ydep := info.paramInfo[yi]!.backDeps.contains i
    if xdep != ydep then
      -- This is an implicit argument that's only for parameterizing x or y
      -- but not both, so don't immediately include it.
      pure ()
    else
      -- This is an implicit argument parameterizing the relation,
      -- so include it and all previous implicit arguments.
      relArgs := i
  let rel := mkAppN f (args.extract 0 relArgs)
  return some (rel, args[xi]!, args[yi]!)

/-- Given an expression of the form `r x y` with implicit arguments,
returns `(r, x, y)`. Otherwise returns `none`.
Ensures that `r x y` elaborates using `Lean.Meta.mkAppM'`. -/
def _root_.Lean.Expr.rel?' (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let some (rel, x, y) ← e.rel? | return none
  try
    discard <| mkAppM' rel #[x, y]
    return some (rel, x, y)
  catch _ =>
    return none

/-- Environment extension storing transitivity lemmas -/
initialize transExt :
    SimpleScopedEnvExtension (Name × Array (DiscrTree.Key true)) (DiscrTree Name true) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun dt (n, ks) ↦ dt.insertCore ks n
    initial := {}
  }

initialize registerBuiltinAttribute {
  name := `trans
  descr := "transitive relation"
  add := fun decl _ kind ↦ MetaM.run' do
    let declTy := (← getConstInfo decl).type
    let (xs, _, targetTy) ← withReducible <| forallMetaTelescopeReducing declTy
    let fail := throwError
      "@[trans] attribute only applies to lemmas proving
      x ∼ y → y ∼ z → x ∼ z, got {indentExpr declTy} with target {indentExpr targetTy}"
    let some (rel, x, z) ← targetTy.rel?' | fail
    let some yzHyp := xs.back? | fail
    let some xyHyp := xs.pop.back? | fail
    let some (_, y, z') ← (← inferType yzHyp).rel?' | fail
    let some (_, x', y') ← (← inferType xyHyp).rel?' | fail
    unless ← isDefEq x x' do fail
    unless ← isDefEq y y' do fail
    unless ← isDefEq z z' do fail
    let key ← withReducible <| DiscrTree.mkPath rel
    transExt.add (decl, key) kind
}

/-- Composition using the `Trans` class in the homogeneous case. -/
def _root_.Trans.simple {a b c : α} [Trans r r r] : r a b → r b c → r a c := trans

/-- Composition using the `Trans` class in the general case. -/
def _root_.Trans.het {a : α} {b : β} {c : γ}
  {r : α → β → Sort u} {s : β → γ → Sort v} {t : outParam (α → γ → Sort w)}
  [Trans r s t] : r a b → s b c → t a c := trans

open Lean.Elab.Tactic

/--
Implementation of `Lean.MVarId.trans` and the user-facing `trans` tactic.
-/
def _root_.Lean.MVarId.transCore (g : MVarId) (lem : Name) (rel x z : Expr) (y? ty? : Option Expr) :
    MetaM (List MVarId) := do
  g.checkNotAssigned `trans
  let arity ← withReducible <| forallTelescopeReducing (← inferType (← mkConstWithLevelParams lem))
    fun es _ => pure es.size
  let y ← y?.getDM (mkFreshExprMVar ty?)
  let tag1 := appendTag (← g.getTag) `trans1
  let tag2 := appendTag (← g.getTag) `trans2
  let g₁ ← mkFreshExprSyntheticOpaqueMVar (← mkAppM' rel #[x, y]) (tag := tag1)
  let g₂ ← mkFreshExprSyntheticOpaqueMVar (← mkAppM' rel #[y, z]) (tag := tag2)
  g.assignIfDefeq <| ← mkAppOptM lem (mkArray (arity - 2) none ++ #[some g₁, some g₂])
  pure <| [g₁.mvarId!, g₂.mvarId!] ++ (if y?.isNone then [y.mvarId!] else [])

/--
Apply a transitivity lemma to the goal, optionally specifying the value `y` of the intermediate
term, or specifying its type `ty`. (If specifying both the type is not used.)
-/
def _root_.Lean.MVarId.trans (g : MVarId) (y ty : Option Expr := none) : MetaM (List MVarId) := do
  let tgt ← g.getType
  match ← tgt.rel? with
  | none => throwError "transitivity lemmas only apply to binary relations, not {indentExpr tgt}"
  | some (rel, x, z) =>
    (``Trans.simple :: ``HEq.trans :: (← (transExt.getState (← getEnv)).getUnify rel).toList)
      |>.firstM fun lem => do g.transCore lem rel x z y ty

/--
`trans` applies to a goal whose target has the form `t ~ u` where `~` is a transitive relation,
that is, a relation which has a transitivity lemma tagged with the attribute `@[trans]`.

* `trans s` replaces the goal with the two subgoals `t ~ s` and `s ~ u`.
* If `s` is omitted, then a metavariable is used instead.
-/
elab "trans" t?:(ppSpace colGt term)? : tactic => withMainContext do
  let tgt ← getMainTarget''
  match ← tgt.rel? with
  | none => throwError "transitivity lemmas only apply to binary relations, not {indentExpr tgt}"
  | some (rel, x, z) =>
    let t (ty? : Option Expr) := do
      if let some t := t? then
        let (e, gs) ← elabTermWithHoles t ty? (← getMainTag)
        return (some e, gs)
      else
        return (none, [])
    let lemmas ← (transExt.getState (← getEnv)).getUnify rel
    let ty ← inferType x
    -- First try assuming the types are homogeneous.
    (do
      let (t', gs) ← t ty
      liftMetaTactic fun g ↦ (lemmas.push ``Trans.simple).toList.firstM fun lem => do
        (· ++ gs) <$> g.transCore lem rel x z t' ty) <|>
    -- If that fails, try again but with a metavariable for the type of the middle term.
    (do
      let (t', gs) ← t none
      liftMetaTactic fun g ↦ (lemmas.push ``HEq.trans).toList.firstM fun lem => do
        (· ++ gs) <$> g.transCore lem rel x z t' none) <|>
    throwError m!"no applicable transitivity lemma found for {indentExpr tgt}"
