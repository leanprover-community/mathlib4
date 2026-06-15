/-
Copyright (c) 2026 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/
module

public meta import Mathlib.Tactic.Set
public meta import Lean.Elab.BuiltinTerm

/-!
# The `setm` tactic

This module defines the `setm` tactic.
-/

meta section

open Lean Elab Tactic Meta Term Syntax

namespace Mathlib.Tactic.SetM

partial def wrapSyntheticHoles : Syntax → StateT (NameMap MVarId) TacticM Syntax :=
  fun stx => do
    if stx.isOfKind ``Lean.Parser.Term.syntheticHole && stx[1].isIdent then
      let mvar ←
        if let .some old := (← get).get? stx[1].getId then
          pure old
        else
          let name ← mkFreshUserName stx[1].getId
          let mvar := (← mkFreshExprMVar .none (userName := name)).mvarId!
          modify (.insert · stx[1].getId mvar)
          pure mvar
      let ident : Ident := mkIdent (← mvar.getTag)
      return ← withRef stx <| `(? $ident)
    match stx with
    | .node info kind args => return .node info kind (← args.mapM wrapSyntheticHoles)
    | _ => return stx

syntax (name := setMStx) "setm " term (Parser.Tactic.location)? : tactic

-- This code was copied from the `change` tactic in core. I am not sure if in our context,
-- all of it is necessary (could there be other synthetic opaque MVars that were not holes?).
def elabSetM (e : Expr) (p : Syntax) : TacticM Expr := do
  let p ← runTermElab do
    let p ← Term.elabTermEnsuringType p (← inferType e)
    unless ← isDefEq p e do
      Term.synthesizeSyntheticMVars (postpone := .partial)
      discard <| isDefEq p e
    pure p
  withAssignableSyntheticOpaque do
    unless ← isDefEq p e do
      throwError MessageData.ofLazyM (es := #[p, e]) do
        let (p, tgt) ← addPPExplicitToExposeDiff p e
        return m!"setm: pattern{indentExpr p}\nis not defeq to goal{indentExpr tgt}"
    return ← instantiateMVars p

@[tactic setMStx]
public def evalSetM : Tactic
  | `(tactic| setm $pat:term $[$loc:location]?) => withReducibleAndInstances do
    let (pat, mvars) ← StateT.run (wrapSyntheticHoles pat) .empty
    let locations := expandOptLocation (Lean.mkOptionalNode loc)
    -- First, unify the pattern with the target of each location.
    withLocation locations
      (atLocal := unify pat ∘ .some)
      (atTarget := unify pat .none)
      (failed := fun _ ↦ throwError "'setm' tactic failed")
    -- The, for each metavariable...
    for (n, m) in mvars do
      -- ... instantiate it and introduce a let into the context...
      let val ← instantiateMVars (.mvar m)
      let ty ← m.getType'
      let fvar ← liftMetaTacticAux fun goal ↦ do
        let (fvar, goal) ← (← goal.define n ty val).intro1P
        return (fvar, [goal])
      -- ... and rewrite the introduced decl in each one of the locations.
      withLocation locations
        (atLocal := rewrite fvar val ∘ .some)
        (atTarget := rewrite fvar val .none)
        (failed := fun _ ↦ throwError "'setm' tactic failed")
  | _ => throwUnsupportedSyntax
  where
    unify (pat : Syntax) (lvar : Option FVarId) : TacticM Unit := do
      let e ← if let .some l := lvar
        then l.getType
        else getMainTarget
      let tgt ← elabSetM e pat
      liftMetaTactic fun goal => do
        return [← changeDecl goal tgt lvar]
    rewrite (fvar : FVarId) (val : Expr) (lvar : Option FVarId) : TacticM Unit := do
      liftMetaTactic fun goal ↦ do
        let tgt ← instantiateMVars (← lvar.elim goal.getType (·.getType))
        let absTgt ← kabstract tgt val
        let goal ← if absTgt.hasLooseBVars
          then changeDecl goal (absTgt.instantiate1 (.fvar fvar)) lvar
          else pure goal
        return [goal]
    changeDecl (goal : MVarId) (tgt : Expr) (l? : Option FVarId := .none) : MetaM MVarId :=
      match l? with
      | .some fvar => do
        let lctx := (← goal.getDecl).lctx.modifyLocalDecl fvar
          fun d ↦ d.setType tgt
        goal.modifyLCtx (fun _ ↦ lctx)
        return goal
      | .none => goal.replaceTargetDefEq tgt

end Mathlib.Tactic.SetM
