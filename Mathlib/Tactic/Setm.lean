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

public meta section

open Lean Elab Tactic Meta Term Syntax

namespace Mathlib.Tactic.SetM

/-- This parser is declared inside a hidden namespace and should never be used. Its
purpose is to register the ``Hidden.setmSyntheticHole` syntaax node kind in
the environment. -/
scoped syntax:max (name := Hidden.setmSyntheticHole)
  "?" (ident <|> "_") : term

open Hidden in
/-- We give a distinguished name to the named holes appearing in the `setm` match pattern,
to avoid unifying them with other metavariables in the context which have the same name. The
distinguished name is reused across all holes with the same name in the pattern. -/
meta partial def wrapSyntheticHoles : Syntax → StateT (NameMap Name) TacticM Syntax :=
  fun stx => do
    if stx.isOfKind ``Lean.Parser.Term.syntheticHole && stx[1].isIdent then
      let name ←
        if let .some old := (← get).get? stx[1].getId then
          pure old
        else
          let unique ← mkFreshUserName stx[1].getId
          modify (.insert · stx[1].getId unique)
          pure unique
      return stx.setKind ``setmSyntheticHole |>.setArg 1 (mkIdent name)
    match stx with
    | .node info kind args => return .node info kind (← args.mapM wrapSyntheticHoles)
    | _ => return stx

open Hidden in
/-- Elaborate the named `setm` holes, creating metavariables for them. -/
@[term_elab Hidden.setmSyntheticHole]
def elabSetmSyntheticHole : Term.TermElab := fun stx expectedType? => do
  unless stx.isOfKind ``setmSyntheticHole do
    throwUnsupportedSyntax
  if let .ident _ _ n _ := stx[1] then
    -- Reuse metavariables in the context who have the same name.
    -- nb: at this point, they already have the distinguished names, so this is safe.
    for (id, decl) in (← getMCtx).decls do
      if decl.userName == n then return .mvar id
    let mvar ← mkFreshExprMVar expectedType? (userName := n)
    registerMVarErrorHoleInfo mvar.mvarId! stx
    return mvar
  else elabHole stx expectedType?

syntax (name := setMStx) "setm " term (Parser.Tactic.location)? : tactic

-- This code was copied from the `change` tactic in core. I am not sure if in our context,
-- all of it is necessary (could there be other synthetic opaque MVars that were not holes?).
meta def elabSetM (e : Expr) (p : Syntax) : TacticM Expr := do
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
meta def evalSetM : Tactic
  | `(tactic| setm $pat:term $[$loc:location]?) => withReducibleAndInstances do
    let (pat, names) ← StateT.run (wrapSyntheticHoles pat) .empty
    let locations := expandOptLocation (Lean.mkOptionalNode loc)
    -- First, unify the pattern with the target of each location.
    withLocation locations
      (atLocal := unify pat ∘ .some)
      (atTarget := unify pat .none)
      (failed := fun _ ↦ throwError "'setm' tactic failed")
    -- Now, make a mapping of hole names to the metavariables that appeared in the pattern.
    let mctx ← getMCtx
    let mvars : NameMap MVarId := mctx.decls.foldl (init := {}) fun acc id decl =>
      if let Option.some n := Id.run <| do
        for (n, un) in names do
          if un == decl.userName then return .some n
        return .none
      then acc.insert n id
      else acc
    -- Finally, for each metavariable...
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
