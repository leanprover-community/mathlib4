/-
Copyright (c) 2023 Sebastian Zimmer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Zimmer, Mario Carneiro, Heather Macbeth
-/
import Mathlib.Tactic.Core
import Std.Tactic.LabelAttr
import Mathlib.Tactic.GCongr.Core
import Mathlib.Data.Prod.Basic

/-!
# GRW Tactic

This module defines the core of the `grw` tactic.

-/

open Lean Meta Std.Tactic.LabelAttr Elab Tactic

namespace Mathlib.Tactic.GRW

initialize registerTraceClass `GRW


/-- Structure recording the data for a "generalized rewriting" (`grw`) lemma. -/
structure GRWLemma where
  declName : Name
  mainSubgoals : Array (Nat × Nat)
  deriving Inhabited, Repr

/-- Environment extension for "generalized rewriting" (`grw`) lemmas. -/
initialize grwExt : SimpleScopedEnvExtension (Name × GRWLemma)
    (HashMap Name (Array GRWLemma)) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m (n, lem) => m.insert n ((m.findD n #[]).push lem)
    initial := {}
  }

/-- Attribute marking "generalized rewriting" (`grw`) lemmas.  Such lemmas must have a
conclusion of a form such as `P x₁ y z₁ → P x₂ y z₂`; that is, an implication between the
application of a predicate to two argument lists, in which the "varying argument" pairs (here
`x₁`/`x₂` and `z₁`/`z₂`) are all free variables.

For example, this lemma shows `grw` how to convert `a < b` into `a' < b'`.
```lean
@[grw] lemma rewrite_lt {α : Type*} [Preorder α] {a b a' b' : α}
    (ha : a' ≤ a) (hb : b ≤ b') (H : a < b) : a' < b'
```
The most common `@[grw]` lemmas are transitivity lemmas, as above, but other forms are possible.
For example, this lemma shows `grw` to to rewrite `a ∈ X` into `a ∈ X'`.
```lean
@[grw] lemma rewrite_mem {α : Type*} {a : α} {X X' : Set α} (hX : X ⊆ X') (H : a ∈ X) : a ∈ X'
```

The antecedents of a `@[grw]` lemma are classified as generating "main goals" if they are of the
form `x₁ ≈ x₂` for some "varying argument" pair `x₁`/`x₂` and some relation `≈`. The `gcongr` tactic
will be used to resolve these.

Hopefully all other arguments will be resolved by unification/typeclass inference/etc; the `grw`
tactic will fail if they are not. -/
initialize registerBuiltinAttribute {
  name := `grw
  descr := "generalized rewriting"
  add := fun decl _ kind ↦ MetaM.run' do
    let declTy := (← getConstInfo decl).type
    withReducible <| forallTelescopeReducing declTy fun xs targetTy => do
    let fail := throwError
      "@[grw] attribute only applies to lemmas proving {
      ""}x₁ ~₁ x₁' → ... xₙ ~ₙ xₙ' → P x₁ ... xₙ → P x₁' ... xₙ', got {declTy}"
    -- verify that conclusion of the lemma is of the form `head y₁ ... yₙ`
    let rhs ← whnf targetTy
    let (some head', rhsArgs) := rhs.withApp fun e a => (e.constName?, a) | fail
    trace[GRW] "head' is {head'}"
    -- verify that last antecedent of the lemma is of the form `head x₁ ... xₙ`
    let lhs ← whnf (← inferType  xs.back)
    trace[GRW] "lhs is {lhs}"
    let (some head, lhsArgs) := lhs.withApp fun e a => (e.constName?, a) | fail
    trace[GRW] "head is {head}"
    unless head == head' && lhsArgs.size == rhsArgs.size do fail
    let mut prev := 0
    let mut curr := 0
    let mut pairs := #[]
    -- iterate through each pair of corresponding (LHS/RHS) inputs to the head predicate `head` in
    -- the conclusion of the lemma
    for e1 in lhsArgs, e2 in rhsArgs do
      prev := curr
      curr := curr + 1
      -- we call such a pair a "varying argument" pair if the LHS/RHS inputs are not defeq
      let isEq ← isDefEq e1 e2
      if !isEq then
        -- verify that the "varying argument" pairs are free variables
        unless e1.isFVar && e2.isFVar do fail
        -- add such a pair to the `pairs` array
        pairs := pairs.push (prev, e1, e2)
    let mut mainSubgoals := #[]
    let mut i := 0
    -- iterate over antecedents `hyp` to the lemma
    for hyp in xs.pop do
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
    -- store all the information from this parse of the lemma's structure in a `GRWLemma`
    grwExt.add
      (head, { declName := decl, mainSubgoals }) kind
}


open GCongr

/-- Given `relationType := R a b`, returns `(a, b)` -/
def getNeedleReplacement (relationType : Expr) : MetaM (Expr × Expr) := do
  let args := relationType.getAppArgs
  if args.size < 2 then
    throwError "Expecting relation but got {relationType}"
  return (args[args.size - 2]!, args[args.size - 1]!)

/--
Constructs the new expression after rewriting occurrences of the LHS of `rule` with the RHS
in `oldExpr` (or vice versa when `rev` is true). Returns `(template, newExpr)` where `newExpr` is
the replaced expression and `template` is the rewrite motive with the bound variable replaced with
a fresh mvar (used as input to gcongr).
-/
def getNewExpr (rule : Expr) (rev : Bool) (oldExpr : Expr) : MetaM (Expr × Expr) := do
  let ruleType ← instantiateMVars (← inferType rule)
  let (needle, replacement) ← if rev then
    Prod.swap <$> getNeedleReplacement ruleType
  else
    getNeedleReplacement ruleType
  trace[GRW] "Got needle = {needle} replacement = {replacement}"
  let abst ← withReducible <| kabstract oldExpr needle
  if !abst.hasLooseBVars then
    throwError "Could not find pattern {needle} in {oldExpr}"
  let newExpr := abst.instantiate1 replacement
  trace[GRW] "old expr {oldExpr} new expr {newExpr}"
  let template := abst.instantiate1 (← mkFreshExprSyntheticOpaqueMVar ruleType)
  return (← whnfR template, newExpr)

/-- Try to discharge the goal `goal` using `gcongr` using the provided `template` and using only
`rule` for discharging the main subgoals. -/
def useRule (template rule : Expr) (goal : MVarId) : MetaM (Array MVarId) := do
  let template ← instantiateMVars template
  try
    if template.hasExprMVar then failure
    goal.applyRfl
    trace[GRW] "used reflexivity"
    return #[]
  catch _ => pure ()
  let (_, _, subgoals) ← goal.gcongr template []
    (mainGoalDischarger := fun g => g.gcongrForward #[rule])

  trace[GRW] "Got proof {← instantiateMVars (.mvar goal)}"
  return subgoals

/--
Use the relation `rule : x ~ y` to rewrite the type of an mvar. Assigns the mvar and returns a new
mvar of type either `p[x/y]` or `p[y/x]` depending on the value of the `rev` parameter

Parameters:
* `goal` The mvar for the current goal
* `expr` the expression to rewrite in
* `rule` An expression of type `x ~ y` where `~` is some relation
* `rev` if true, we will rewrite `expr` to `newExpr := expr[y/x]`, otherwise `newExpr := expr[x/y]`
* `isTarget` if true we are proving `newExpr → expr` otherwise we are proving `expr → newExpr`

Returns:
* `newExpr` The rewritten version of `expr`
* `proof` if `isTarget` is true this is a value of type `newExpr → expr`,
  otherwise it has type `expr → newExpr`
* `subgoals` list of side goals created by `gcongr`. This does not include the goals
  successfully filled by `gcongr_discharger`
-/
def _root_.Lean.MVarId.grw (goal : MVarId) (expr rule : Expr) (rev isTarget : Bool) :
    MetaM (Expr × Expr × Array MVarId) := do
  let oldExpr ← instantiateMVars expr
  let (ruleArgs, _, resultType) ← forallMetaTelescope (← inferType rule)
  if (← whnfR resultType).isEq then
    let ⟨newExpr, eqProof, subgoals⟩ ← goal.rewrite expr rule rev
    let proof ← if isTarget then
      mkAppOptM ``cast #[newExpr, expr, ← mkEqSymm eqProof]
    else
      mkAppOptM ``cast #[expr, newExpr, eqProof]
    return ⟨newExpr, proof, subgoals.toArray⟩
  let rule := mkAppN rule ruleArgs
  let (template, newExpr) ← getNewExpr rule rev oldExpr
  let (lhsExpr, rhsExpr) := if isTarget then (newExpr, oldExpr) else (oldExpr, newExpr)

  let keyExpr ← whnfR oldExpr
  trace[GRW] "predicate is {keyExpr} which has type {keyExpr.ctorName}"
  if !keyExpr.isApp then throwError "expecting {keyExpr} to be a function application"
  let keyExprAux := keyExpr.getAppFn
  trace[GRW] "identifying key in the expression {keyExprAux}"
  let some key := keyExprAux.constName? | throwError "expecting {keyExprAux} to be a constant"

  trace[GRW] "will look up the grw lemma(s) with key {key}"
  -- TODO do we want to enforce that there be at most one lemma per predicate?"
  for lem in (grwExt.getState (← getEnv)).findD key #[] do
    let lemResult ← withTraceNode `GRW (fun _ ↦ return m!"trying lemma {lem.declName}") do
      let lemResult ← try commitIfNoEx do
        let lemExpr ← mkConstWithFreshMVarLevels lem.declName
        let lemType ← inferType lemExpr
        let (metas, _, _) ← withReducible <| forallMetaTelescopeReducing lemType
        guard <| ← isDefEq rhsExpr (← inferType (mkAppN lemExpr metas))

        withLocalDeclD (← mkFreshUserName `h) lhsExpr fun value => do
          withReducible <| metas.back.mvarId!.assignIfDefeq value

          trace[GRW] "Lemma {lem.declName} matches, trying to fill args"
          let e := mkAppN lemExpr metas.pop
          trace[GRW] "working on {e}"
          pure <| some ⟨e, metas⟩
      catch ex => do
        trace[GRW] "error in lemma {lem.declName}: {ex.toMessageData}"
        pure none

      if let some (lemExpr, metas) := lemResult then

        let args := lemExpr.getAppArgs
        let tplArgs := template.getAppArgs

        trace[GRW] "{lem.mainSubgoals.size} congruences to try to fill"

        let mut subgoals := #[]
        -- If the `apply` succeeds, iterate over `(i, j)` belonging to the lemma's `mainSubgoal`
        -- list: here `i` is an index in the lemma's array of antecedents, and `j` is an index in
        -- the array of arguments to the head predicate in the conclusion of the lemma (this should
        -- be the same as the head predicate of the goal/hypothesis we are rewriting at), such that
        -- the `i`-th antecedent to the lemma is a relation between the LHS and RHS `j`-th inputs to
        -- the head predicate.
        for (i, j) in lem.mainSubgoals do
          -- We anticipate that such a "main" subgoal should not have been solved by the `apply` by
          -- unification ...
          let some (.mvar mvarId) := args[i]? | panic! "what kind of lemma is this?"
          -- Look up the part of the template corresponding to the `j`-th input to the head
          -- predicate
          let tpl := tplArgs[j]!
          -- call `useRule` on the subgoal; that is, try to solve it with `gcongr` with the
          -- appropriate pattern (or with `rfl` if the pattern is trivial)
          let subgoals2 ← do
            withTraceNode `GRW (fun _ ↦ return m!"Trying to prove {← mvarId.getType}, {
              ""} which we expect to be a relation of pattern {tpl}") do
              withReducibleAndInstances <| useRule tpl rule mvarId
          (subgoals) := (subgoals ++ subgoals2)

        let bad ← (metas.map Expr.mvarId!).filterM fun x => not <$> x.isAssigned
        if !bad.isEmpty then throwError "unsolved goals {← bad.mapM MVarId.getType} associated to {
          ""}the grw lemma {lem.declName} for {key}"
        trace[GRW] "Got subgoals {subgoals}"
        return some (lemExpr, subgoals)
      else
        return none

    if let some (proof, subgoals) := lemResult then
      trace[GRW] "Got proof {proof}"
      let ruleSubgoals ← (ruleArgs.map Expr.mvarId!).filterM fun x => not <$> x.isAssigned
      return (newExpr, proof, ruleSubgoals ++ subgoals)
  throwError "No grw lemmas worked"
