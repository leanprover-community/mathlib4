/-
Copyright (c) 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Tactic.SolveByElim
import Mathlib.Tactic.Positivity

namespace Mathlib.Tactic.Rel
open Lean Meta

structure RelCongrLemma where
  declName : Name
  mainSubgoals : Array Nat
  varyingArgs : Array Bool
  deriving Inhabited, Repr

/-- Environment extensions for rel_congr lemmas -/
initialize relCongrExt : SimpleScopedEnvExtension ((Name × Name) × RelCongrLemma)
    (HashMap (Name × Name) (Array RelCongrLemma)) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m (n, lem) => m.insert n ((m.findD n #[]).push lem)
    initial := {}
  }

initialize registerBuiltinAttribute {
  name := `rel_congr
  descr := "relation congruence"
  add := fun decl _ kind ↦ MetaM.run' do
    let declTy := (← getConstInfo decl).type
    withReducible <| forallTelescopeReducing declTy fun xs targetTy => do
    let fail := throwError
      "@[rel_congr] attribute only applies to lemmas proving {
      ""}x₁ ~₁ x₁' → ... xₙ ~ₙ xₙ' → f x₁ ... xₙ ∼ f x₁' ... xₙ', got {declTy}"
    let .app (.app rel lhs) rhs ← whnf targetTy | fail
    let some relName := rel.getAppFn.constName? | fail
    let (some head, lhsArgs) := lhs.withApp fun e a => (e.constName?, a) | fail
    let (some head', rhsArgs) := rhs.withApp fun e a => (e.constName?, a) | fail
    unless head == head' && lhsArgs.size == rhsArgs.size do fail
    let mut varyingArgs := #[]
    let mut pairs := #[]
    for e1 in lhsArgs, e2 in rhsArgs do
      let isEq ← isDefEq e1 e2
      varyingArgs := varyingArgs.push !isEq
      if !isEq then
        unless e1.isFVar && e2.isFVar do fail
        pairs := pairs.push (e1, e2)
    let mut mainSubgoals := #[]
    let mut i := 0
    for hyp in xs do
      mainSubgoals ← forallTelescopeReducing (← inferType hyp) fun _args hypTy => do
        let mut mainSubgoals := mainSubgoals
        if let .app (.app _ lhs₁) rhs₁ ← whnf hypTy then
          let lhs₁ := lhs₁.getAppFn
          let rhs₁ := rhs₁.getAppFn
          if ← pairs.anyM fun (e1, e2) =>
            isDefEq lhs₁ e1 <&&> isDefEq rhs₁ e2 <||>
            isDefEq lhs₁ e2 <&&> isDefEq rhs₁ e1
          then
            mainSubgoals := mainSubgoals.push i
        pure mainSubgoals
      i := i + 1
    relCongrExt.add ((relName, head), { declName := decl, mainSubgoals, varyingArgs }) kind
}

syntax "rel_congr_discharger" : tactic

macro_rules | `(tactic| rel_congr_discharger) => `(tactic| positivity)
macro_rules | `(tactic| rel_congr_discharger) => `(tactic| positivity)

syntax "rel" " [" term,* "] " : tactic
-- syntax (name := ExtraSyntax) "extra" : tactic

-- open Lean Mathlib Tactic

-- def RelConfig : SolveByElim.Config :=
-- { transparency := .instances
--   -- On applying a lemma or hypothesis successfully, don't backtrack
--   failAtMaxDepth := false
--   maxDepth := 50 }

-- -- def Lean.MVarId.RelCongr (attr : Name) --(add : List Term)
-- --     (disch : MVarId → MetaM (Option (List MVarId)) := fun _ => pure none)
-- --     (proc : List MVarId → List MVarId → MetaM (Option (List MVarId)) := fun _ _ => pure none)
-- --     (g : MVarId) :
-- --     MetaM (List MVarId) := do
-- --   let cfg : SolveByElim.Config := { RelConfig with discharge := disch, proc := proc }
-- --   SolveByElim.solveByElim.processSyntax cfg false false [] [] #[mkIdent attr] [g]

initialize registerTraceClass `Meta.rel

partial def _root_.Lean.MVarId.relCongr
    (g : MVarId) (template : Option Expr)
    (discharger : MVarId → MetaM Unit)
    (assumption : MVarId → MetaM Unit := fun g => g.assumption) :
    MetaM (Array MVarId) := do
  withTraceNode `Meta.rel (fun _ => return m!"rel_congr: ⊢ {← g.getType}") do
  match template with
  | none =>
    try assumption g; return #[]
    catch _ => pure ()
  | some (.mvar mvarId) =>
    if let .syntheticOpaque ← mvarId.getKind then
      try assumption g; return #[]
      catch _ => return #[g]
  | some _ => pure ()
  let .app (.app rel lhs) rhs ← withReducible g.getType'
    | throwError "rel_congr failed, not a relation"
  let some relName := rel.getAppFn.constName?
    | throwError "rel_congr failed, relation head {rel} is not a constant"
  let (some lhsHead, lhsArgs) := lhs.withApp fun e a => (e.constName?, a)
    | if template.isNone then return #[g]
      throwError "rel_congr failed, {lhs} is not a constant"
  let (some rhsHead, rhsArgs) := rhs.withApp fun e a => (e.constName?, a)
    | if template.isNone then return #[g]
      throwError "rel_congr failed, {rhs} is not a constant"
  let tplArgs ← if let some tpl := template then
    let (some tplHead, tplArgs) := tpl.withApp fun e a => (e.constName?, a)
      | throwError "rel_congr failed, {tpl} is not a constant"
    unless tplHead == lhsHead && tplArgs.size == rhsArgs.size do
      throwError "expected {tplHead}, got {lhsHead}\n{lhs}"
    unless tplHead == rhsHead && tplArgs.size == rhsArgs.size do
      throwError "expected {tplHead}, got {rhsHead}\n{rhs}"
    tplArgs.mapM fun tpl => do
      let mctx ← getMCtx
      let hasMVar := tpl.findMVar? fun mvarId =>
        if let some mdecl := mctx.findDecl? mvarId then
          mdecl.kind matches .syntheticOpaque
        else
          false
      pure (some tpl, hasMVar.isSome)
  else
    unless lhsHead == rhsHead && lhsArgs.size == rhsArgs.size do
      return #[g]
    (lhsArgs.zip rhsArgs).mapM fun (lhsArg, rhsArg) =>
      return (none, !(← isDefEq lhsArg rhsArg))
  let varyingArgs := tplArgs.map (·.2)
  if varyingArgs.all not then
    throwError "try refl"
  let s ← saveState
  let mut ex? := none
  for lem in (relCongrExt.getState (← getEnv)).findD (relName, lhsHead) #[] do
    if lem.varyingArgs == varyingArgs then
      let gs ← try
        Except.ok <$> g.apply (← mkConstWithFreshMVarLevels lem.declName)
      catch e => pure (Except.error e)
      match gs with
      | .error e =>
        ex? := ex? <|> (some (← saveState, e)) -- stash the first failure of `apply`
        s.restore
      | .ok gs =>
        let some e ← getExprMVarAssignment? g | panic! "unassigned?"
        let args := e.getAppArgs
        let mut subgoals := #[]
        for i in lem.mainSubgoals do
          let .mvar mvarId := args[i]! | panic! "what kind of lemma is this?"
          let (_vs, mvarId) ← mvarId.intros
          let tpl ← tplArgs[i]!.1.mapM fun e => do
            let (_vs, _, e) ← lambdaMetaTelescope e
            pure e
          subgoals := subgoals ++ (← mvarId.relCongr tpl discharger assumption)
        let mut out := #[]
        for g in gs do
          if !(← g.isAssigned) then
            try discharger g
            catch _ => out := out.push g
        return out ++ subgoals
  if template.isNone then
    return #[g]
  let some (sErr, e) := ex? | throwError "rel_congr failed, no lemma with @[rel_congr] applies"
  sErr.restore
  throw e

open Elab Tactic

def myExact (g : MVarId) (e : Expr) : MetaM Unit := do
  let .true ← isDefEq (← g.getType) (← inferType e) | failure
  g.checkNotAssigned `myExact
  g.assign e

def relAssumption (hs : Array Expr) (g : MVarId) : MetaM Unit :=
  withReducible do
    let s ← saveState
    withTraceNode `Meta.rel (fun _ => return m!"rel_assumption: ⊢ {← g.getType}") do
    for h in hs do
      try
        try myExact g h catch _ =>
          try myExact g (← mkAppM ``le_of_lt #[h]) catch _ =>
            let m ← mkFreshExprMVar none
            myExact g (← mkAppOptM ``Eq.subst #[h, m])
            g.rfl
        return
      catch _ => s.restore
    throwError "rel_assumption failed"

elab "rel_congr" template:(colGt term)? : tactic => do
  let g ← getMainGoal
  g.withContext do
  let .app (.app _rel lhs) _rhs ← withReducible g.getType'
    | throwError "rel_congr failed, not a relation"
  let template ← template.mapM fun e => do
    Term.elabTerm e (← inferType lhs)
  let disch g := Term.TermElabM.run' do
    let [] ← Tactic.run g <| evalTactic (Unhygienic.run `(tactic| rel_congr_discharger))
      | failure
  let assum g := do
    let mut hs := #[]
    for h in ← getLCtx do
      if !h.isImplementationDetail then
        hs := hs.push (.fvar h.fvarId)
    relAssumption hs g
  replaceMainGoal (← g.relCongr template disch assum).toList


-- def Lean.MVarId.rel (attr : Array Name) (add : List Term) (m : MessageData)
--     (disch : MVarId → MetaM (Option (List MVarId)) := fun _ => pure none)
--     (proc : List MVarId → List MVarId → MetaM (Option (List MVarId)) := fun _ _ => pure none)
--     (g : MVarId) :
--     MetaM (List MVarId) := do
--   let cfg : SolveByElim.Config := { RelConfig with discharge := disch, proc := proc }
--   let [] ← SolveByElim.solveByElim.processSyntax cfg true false add [] (attr.map mkIdent) [g]
--     | throwError m
--   return []
