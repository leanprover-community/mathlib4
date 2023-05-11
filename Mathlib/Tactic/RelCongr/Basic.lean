/-
Copyright (c) 2023 Mario Carneiro, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Heather Macbeth
-/
import Mathlib.Init.Algebra.Order
import Mathlib.Tactic.Relation.Rfl
import Mathlib.Tactic.Relation.Symm

/-!
# The `rel_congr` ("relational congruence") tactic

-/

namespace Mathlib.Tactic.Rel
open Lean Meta

/-- Structure recording the data for a "relational congruence" (`rel_congr`) lemma. -/
structure RelCongrLemma where
  declName : Name
  mainSubgoals : Array (Nat × Nat)
  varyingArgs : Array Bool
  deriving Inhabited, Repr

/-- Environment extension for "relational congruence" (`rel_congr`) lemmas. -/
initialize relCongrExt : SimpleScopedEnvExtension ((Name × Name) × RelCongrLemma)
    (HashMap (Name × Name) (Array RelCongrLemma)) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m (n, lem) => m.insert n ((m.findD n #[]).push lem)
    initial := {}
  }

/-- Attribute marking "relational congruence" (`rel_congr`) lemmas.  Such lemmas must have a
conclusion of a form such as `f x₁ y z₁ ∼ f x₂ y z₂`; that is, a relation between the application of
a function to two argument lists, in which the "varying argument" pairs (here `x₁`/`x₂` and
`z₁`/`z₂`) are all free variables.

The antecedents of such a lemma are classified as generating "main goals" if they are of the form
`x₁ ≈ x₂` for some "varying argument" pair `x₁`/`x₂` (and a possibly different relation `≈` to `∼`),
or more generally of the form `∀ i h h' j h'', f₁ i j ≈ f₂ i j` (say) for some "varying argument"
pair `f₁`/`f₂`. (Other antecedents are considered to generate "side goals".) The index of the
"varying argument" pair corresponding to each "main" antecedent is recorded. -/
initialize registerBuiltinAttribute {
  name := `rel_congr
  descr := "relational congruence"
  add := fun decl _ kind ↦ MetaM.run' do
    let declTy := (← getConstInfo decl).type
    withReducible <| forallTelescopeReducing declTy fun xs targetTy => do
    let fail := throwError
      "@[rel_congr] attribute only applies to lemmas proving {
      ""}x₁ ~₁ x₁' → ... xₙ ~ₙ xₙ' → f x₁ ... xₙ ∼ f x₁' ... xₙ', got {declTy}"
    -- verify that conclusion of the lemma is of the form `rel (head x₁ ... xₙ) (head y₁ ... yₙ)`
    let .app (.app rel lhs) rhs ← whnf targetTy | fail
    let some relName := rel.getAppFn.constName? | fail
    let (some head, lhsArgs) := lhs.withApp fun e a => (e.constName?, a) | fail
    let (some head', rhsArgs) := rhs.withApp fun e a => (e.constName?, a) | fail
    unless head == head' && lhsArgs.size == rhsArgs.size do fail
    let mut varyingArgs := #[]
    let mut pairs := #[]
    -- iterate through each pair of corresponding (LHS/RHS) inputs to the head function `head` in
    -- the conclusion of the lemma
    for e1 in lhsArgs, e2 in rhsArgs do
      -- we call such a pair a "varying argument" pair if the LHS/RHS inputs are not defeq
      let isEq ← isDefEq e1 e2
      if !isEq then
        -- verify that the "varying argument" pairs are free variables
        unless e1.isFVar && e2.isFVar do fail
        -- add such a pair to the `pairs` array
        pairs := pairs.push (varyingArgs.size, e1, e2)
      -- record in the `varyingArgs` array a boolean (true for varying, false if LHS/RHS are defeq)
      varyingArgs := varyingArgs.push !isEq
    let mut mainSubgoals := #[]
    let mut i := 0
    -- iterate over antecedents `hyp` to the lemma
    for hyp in xs do
      mainSubgoals ← forallTelescopeReducing (← inferType hyp) fun _args hypTy => do
        let mut mainSubgoals := mainSubgoals
        -- pull out the conclusion `hypTy` of the antecedent, and check whether it is of the form
        -- `lhs₁ _ ... _ ≈ rhs₁ _ ... _` (for a possibly different relation `≈` than the relation
        -- `rel` above)
        if let .app (.app _ lhs₁) rhs₁ ← whnf hypTy then
          let lhs₁ := lhs₁.getAppFn
          let rhs₁ := rhs₁.getAppFn
          -- check whether `(lhs₁, rhs₁)` is in some order one of the "varying argument" pairs from
          -- the conclusion to the lemma
          if let some j ← pairs.findM? fun (_, e1, e2) =>
            isDefEq lhs₁ e1 <&&> isDefEq rhs₁ e2 <||>
            isDefEq lhs₁ e2 <&&> isDefEq rhs₁ e1
          then
            -- if yes, record the index of this antecedent as a "main subgoal", together with the
            -- index of the "varying argument" pair it corresponds to
            mainSubgoals := mainSubgoals.push (i, j.1)
        pure mainSubgoals
      i := i + 1
    -- store all the information from this parse of the lemma's structure in a `RelCongrLemma`
    relCongrExt.add ((relName, head), { declName := decl, mainSubgoals, varyingArgs }) kind
}

syntax "rel_congr_discharger" : tactic

syntax "rel" " [" term,* "] " : tactic

initialize registerTraceClass `Meta.rel

partial def _root_.Lean.MVarId.relCongr
    (g : MVarId) (template : Option Expr)
    (discharger : MVarId → MetaM Unit)
    (assumption : MVarId → MetaM Unit := fun g => g.assumption) :
    MetaM (Array MVarId) := do
  withTraceNode `Meta.rel (fun _ => return m!"rel_congr: ⊢ {← g.getType}") do
  match template with
  -- A. If there is no template, try to resolve the goal by the provided `assumption` tactic, and
  -- continue on if this fails.
  | none =>
    try assumption g; return #[]
    catch _ => pure ()
  -- B. If there is a template, (i) if the template is `?_` then try to resolve the goal by the
  -- provided `assumption` tactic; if this fails, stop and report the existing goal.
  | some (.mvar mvarId) =>
    if let .syntheticOpaque ← mvarId.getKind then
      try assumption g; return #[]
      catch _ => return #[g]
  -- B. If there is a template, (ii) if the template is *not* `?_` then continue on.
  | some _ => pure ()
  -- Check that the goal is of the form `rel (lhsHead _ ... _) (rhsHead _ ... _)`
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
  -- B. If there is a template, check that it is of the form `tplHead _ ... _` and that
  -- `tplHead = lhsHead = rhsHead`
  let tplArgs ← if let some tpl := template then
    let (some tplHead, tplArgs) := tpl.withApp fun e a => (e.constName?, a)
      | throwError "rel_congr failed, {tpl} is not a constant"
    unless tplHead == lhsHead && tplArgs.size == rhsArgs.size do
      throwError "expected {tplHead}, got {lhsHead}\n{lhs}"
    unless tplHead == rhsHead && tplArgs.size == rhsArgs.size do
      throwError "expected {tplHead}, got {rhsHead}\n{rhs}"
    -- and also build a array of `Expr` corresponding to the arguments `_ ... _` to `tplHead` in the
    -- template (these will be used in recursive calls later), and a array of booleans according to
    -- which of these contain `?_`
    tplArgs.mapM fun tpl => do
      let mctx ← getMCtx
      let hasMVar := tpl.findMVar? fun mvarId =>
        if let some mdecl := mctx.findDecl? mvarId then
          mdecl.kind matches .syntheticOpaque
        else
          false
      pure (some tpl, hasMVar.isSome)
  -- A. If there is no template, check that `lhs = rhs`
  else
    unless lhsHead == rhsHead && lhsArgs.size == rhsArgs.size do
      -- (if not, stop and report the existing goal)
      return #[g]
    -- and also build a array of booleans according to which arguments `_ ... _` to the head function
    -- differ between the LHS and RHS
    (lhsArgs.zip rhsArgs).mapM fun (lhsArg, rhsArg) =>
      return (none, !(← isDefEq lhsArg rhsArg))
  -- Name the array of booleans `varyingArgs`: this records which arguments to the head function are
  -- supposed to vary, according to the template (if there is one) to vary, and in the absence of
  -- a template to record which arguments to the head function differ between the two sides of the
  -- goal.
  let varyingArgs := tplArgs.map (·.2)
  if varyingArgs.all not then
    throwError "try refl"
  let s ← saveState
  let mut ex? := none
  -- Look up the `@[rel_congr]` lemmas whose conclusion has the same relation and head function as
  -- the goal.
  for lem in (relCongrExt.getState (← getEnv)).findD (relName, lhsHead) #[] do
    -- Filter further according to whether the boolean-array of varying/nonvarying arguments of such
    -- a lemma matches `varyingArgs`
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
        for (i, j) in lem.mainSubgoals do
          let some (.mvar mvarId) := args[i]? | panic! "what kind of lemma is this?"
          let (_vs, mvarId) ← mvarId.intros
          let tpl ← tplArgs[j]!.1.mapM fun e => do
            let (_vs, _, e) ← lambdaMetaTelescope e
            pure e
          subgoals := subgoals ++ (← mvarId.relCongr tpl discharger assumption)
        let mut out := #[]
        for g in gs do
          if !(← g.isAssigned) && !subgoals.contains g then
            try discharger g
            catch _ => out := out.push g
        return out ++ subgoals
  -- A. If there is no template, and there was no `@[rel_congr]` lemma which matched the goal,
  -- report this goal back.
  if template.isNone then
    return #[g]
  -- B. If there is a template, and there was no `@[rel_congr]` lemma which matched the template,
  -- fail.
  let some (sErr, e) := ex?
    | throwError "rel_congr failed, no @[rel_congr] lemma applies for the template portion {template} and the relation {rel}"
  -- B. If there is a template, and there was a `@[rel_congr]` lemma which matched the template, but
  -- it was not possible to apply that lemma, then report the error message from applying that
  -- lemma.
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
          try g.symm >>= fun g ↦ myExact g h catch _ =>
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
