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
      "@[trans] attribute only applies to lemmas proving x ∼ y → y ∼ z → x ∼ z, got {indentExpr declTy} with target {indentExpr targetTy}"
    let .app (.app rel _) _ := targetTy | fail
    let some yzHyp := xs.back? | fail
    let some xyHyp := xs.pop.back? | fail
    let .app (.app _ _) _ ← inferType yzHyp | fail
    let .app (.app _ _) _ ← inferType xyHyp | fail
    let key ← withReducible <| DiscrTree.mkPath rel
    transExt.add (decl, key) kind
}

/-- Compose two proofs by transitivity, simplified to the homogeneous case. -/
def _root_.Trans.simple {a b c : α} [Trans r r r] : r a b → r b c → r a c := trans

def _root_.Trans.het {a : α}{b : β}{c : γ}
  {r : α → β → Sort u} {s : β → γ → Sort v} {t : outParam (α → γ → Sort w)}
  [Trans r s t]: r a b → s b c → t a c := trans

def _root_.Trans.het' {a : α}(b : β){c : γ}
  {r : α → β → Sort u} {s : β → γ → Sort v} {t : outParam (α → γ → Sort w)}
  [Trans r s t]: r a b → s b c → t a c := trans

open Lean.Elab.Tactic


def getExplicitFuncArg? (e: Expr) : MetaM (Option <| Expr × Expr) := do
  match e with
  | Expr.app f a => do
    if ← isDefEq (← mkAppM' f #[a]) e then
      return some (f, a)
    else
      getExplicitFuncArg? f
  | _ => return none


def getExplicitRelArg? (tgt f z: Expr) : MetaM (Option <| Expr × Expr) := do
  match f  with
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

def showExplicitRelArg (tgt f z: Expr) : MetaM Unit := do
  logInfo m!"tgt: {tgt}"
  logInfo m!"f: {f}"
  logInfo m!"z: {z}"
  match f  with
  | Expr.app rel x => do
    logInfo m!"rel: {rel}"
    logInfo m!"x: {x}"
    if ← isDefEq (← mkAppM' rel #[x, z]) tgt then
      logInfo "matched"
      return ()
    else
      showExplicitRelArg tgt rel z
  | _ => return ()

/--
`trans` applies to a goal whose target has the form `t ~ u` where `~` is a transitive relation,
that is, a relation which has a transitivity lemma tagged with the attribute [trans].

* `trans s` replaces the goal with the two subgoals `t ~ s` and `s ~ u`.
* If `s` is omitted, then a metavariable is used instead.
-/
elab "trans" t?:(ppSpace (colGt term))? : tactic => withMainContext do
  let tgt ← getMainTarget
  let (rel, x, z) ←
    match tgt with
    | Expr.app f z =>
      match (← getExplicitRelArg? tgt f z) with
      | some (rel, x) =>
        pure (rel, x, z)
      | none => throwError "transitivity lemmas only apply to binary relations, not {indentExpr tgt}"
    | _ => throwError "transitivity lemmas only apply to binary relations, not {indentExpr tgt}"
  -- let .app (.app rel x) z := tgt
  --   | throwError "transitivity lemmas only apply to binary relations, not {indentExpr tgt}"
  trace[Tactic.trans]"goal decomposed"
  trace[Tactic.trans]"rel: {indentExpr rel}"
  trace[Tactic.trans]"x:{indentExpr x}"
  trace[Tactic.trans]"z:  {indentExpr z}"
  -- first trying the homogeneous case
  try
    let ty ← inferType x
    let t'? ← t?.mapM (elabTermWithHoles · ty (← getMainTag))
    let s ← saveState
    trace[Tactic.trans]"trying homogeneous case"
    for lem in (← (transExt.getState (← getEnv)).getUnify rel).push ``Trans.simple do
      trace[Tactic.trans]"trying lemma {lem}"
      try
        liftMetaTactic fun g ↦ do
          let lemTy ← inferType (← mkConstWithLevelParams lem)
          let arity ← withReducible <| forallTelescopeReducing lemTy fun es _ ↦ pure es.size
          let y ← (t'?.map (pure ·.1)).getD (mkFreshExprMVar ty)
          let g₁ ← mkFreshExprMVar (some <| ← mkAppM' rel #[x, y]) .synthetic
          let g₂ ← mkFreshExprMVar (some <| ← mkAppM' rel #[y, z]) .synthetic
          g.assign (← mkAppOptM lem (mkArray (arity - 2) none ++ #[some g₁, some g₂]))
          pure <| [g₁.mvarId!, g₂.mvarId!] ++ if let some (_, gs') := t'? then gs' else [y.mvarId!]
        return
      catch _ => s.restore
    pure ()
  catch _ =>
  trace[Tactic.trans]"trying heterogeneous case"
  let t'? ← t?.mapM (elabTermWithHoles · none (← getMainTag))
  let s ← saveState
  for lem in (← (transExt.getState (← getEnv)).getUnify rel).push
      ``Trans.het do
    try
      liftMetaTactic fun g ↦ do
        trace[Tactic.trans]"trying lemma {lem}"
        let lemTy ← inferType (← mkConstWithLevelParams lem)
        let arity ← withReducible <| forallTelescopeReducing lemTy fun es _ ↦ pure es.size
        let y ← (t'?.map (pure ·.1)).getD (mkFreshExprMVar none)
        let g₁ ← mkFreshExprMVar (some <| ← mkAppM' rel #[x, y]) .synthetic
        let g₂ ← mkFreshExprMVar (some <| ← mkAppM' rel #[y, z]) .synthetic
        g.assign (← mkAppOptM lem (mkArray (arity - 2) none ++ #[some g₁, some g₂]))
        pure <| [g₁.mvarId!, g₂.mvarId!] ++ if let some (_, gs') := t'? then gs' else [y.mvarId!]
      return
    catch _ => s.restore

  throwError m!"no applicable transitivity lemma found for {indentExpr tgt}
"
