/-
Copyright (c) 2022 Siddhartha Gadgil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Mario Carneiro, Scott Morrison
-/
import Mathlib.Lean.Meta
import Mathlib.Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Location

/-!
# `trans` tactic

This implements the `trans` tactic, which can apply transitivity theorems with an optional middle
variable argument.
-/

set_option autoImplicit true

namespace Mathlib.Tactic
open Lean Meta Elab

initialize registerTraceClass `Tactic.trans

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
    let .app (.app rel _) _ := targetTy | fail
    let some yzHyp := xs.back? | fail
    let some xyHyp := xs.pop.back? | fail
    let .app (.app _ _) _ ← inferType yzHyp | fail
    let .app (.app _ _) _ ← inferType xyHyp | fail
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

/-- solving `tgt ← mkAppM' rel #[x, z]` given `tgt = f z` -/
def getExplicitRelArg? (tgt f z : Expr) : MetaM (Option <| Expr × Expr) := do
  match f with
  | Expr.app rel x => do
    let check: Bool ← do
      try
        let folded ← mkAppM' rel #[x, z]
        isDefEq folded tgt
      catch _ =>
        pure false
    if check then
      return some (rel, x)
    else
      getExplicitRelArg? tgt rel z
  | _ => return none

/-- refining `tgt ← mkAppM' rel #[x, z]` dropping more arguments if possible -/
def getExplicitRelArgCore (tgt rel x z : Expr) : MetaM (Expr × Expr) := do
  match rel with
  | Expr.app rel' _ => do
    let check: Bool ← do
      try
        let folded ← mkAppM' rel' #[x, z]
        isDefEq folded tgt
      catch _ =>
        pure false
    if !check then
      return (rel, x)
    else
      getExplicitRelArgCore tgt rel' x z
  | _ => return (rel ,x)

/--
If `e` of the form `x ~ z`? If so return the triple `(~, x, z)`.
-/
def _root_.Lean.Expr.rel? (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  match e with
  | Expr.app f z =>
    match (← getExplicitRelArg? e f z) with
    | some (rel, x) =>
      let (rel, x) ← getExplicitRelArgCore e rel x z
      pure (rel, x, z)
    | none => pure none
  | _ => pure none

/--
Implementation of `Lean.MVarId.trans` and the user-facing `trans` tactic.
-/
def _root_.Lean.MVarId.transCore (g : MVarId) (lem : Name) (rel x z : Expr) (y ty : Option Expr) :
    MetaM (List MVarId) := do
  let arity ← withReducible <| forallTelescopeReducing (← inferType (← mkConstWithLevelParams lem))
    fun es _ => pure es.size
  let y ← y.getDM (mkFreshExprMVar ty)
  let g₁ ← mkFreshExprMVar (some <| ← mkAppM' rel #[x, y]) .synthetic
  let g₂ ← mkFreshExprMVar (some <| ← mkAppM' rel #[y, z]) .synthetic
  g.assign (← mkAppOptM lem (mkArray (arity - 2) none ++ #[some g₁, some g₂]))
  pure <| [g₁.mvarId!, g₂.mvarId!] ++ (← getMVars y).toList

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
    let t (ty : Option Expr) :=
      do pure <| (← t?.mapM (elabTermWithHoles · ty (← getMainTag))).map (·.1)
    let lemmas := (← (transExt.getState (← getEnv)).getUnify rel)
    let ty ← inferType x
    -- First try assuming the types are homogeneous.
    (do
      let t' ← t ty
      liftMetaTactic fun g ↦ (lemmas.push ``Trans.simple).toList.firstM fun lem => do
        g.transCore lem rel x z t' ty) <|>
    -- If that fails, try again but with a metavariable for the type of the middle term.
    (do
      let t' ← t none
      liftMetaTactic fun g ↦ (lemmas.push ``HEq.trans).toList.firstM fun lem => do
        g.transCore lem rel x z t' none) <|>
    throwError m!"no applicable transitivity lemma found for {indentExpr tgt}"
