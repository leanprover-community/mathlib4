/-
Copyright (c) 2023 Gareth Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gareth Ma
-/
import Lean
import Mathlib.Tactic.DefEqTransformations

/-!
# The `setm` tactic

The `setm` tactic ("`set` with matching") is used for introducing `let` declarations representing
subexpressions of the goal or in the types of local hypotheses.

For example, if the goal is `⊢ (x + 5) ^ 2 + (2 * y + x) * (x + 5) + 3 = 28` (with `x y : ℕ`), then
`setm ?a ^ 2 + ?b * ?a + 3 = 28` would introduce `a : ℕ := x + 5` and `b : ℕ := 2 * y + 5` into the
context and change the goal to `a ^ 2 + b * a + 3 = 28`
-/

namespace Mathlib.Tactic
open Lean Parser Tactic Elab Tactic Meta

initialize registerTraceClass `Tactic.setm

/-- This is the core to the `setm` tactic. It takes an expression `e` and pattern `stx` containing
named holes whose form should match `e`. For each named hole in `stx`, we create a `let` declaration
of the same name whose value is filled by the corresponding subexpression of `e`. We then rewrite
at the `loc`ations given using the new declarations. -/
def setMCore (e : Expr) (stx : TSyntax `term) (loc : Location) : TacticM Unit := withMainContext do
  let (origPattern, mvarIds) ← elabTermWithHoles stx none (←getMainTag) (allowNaturalHoles := true)
  /- Named holes are by default syntheticOpaque and not assignable, so we change that -/
  mvarIds.forM fun mvarId => mvarId.setKind .natural
  trace[Tactic.setm] "origPattern : {← ppExpr origPattern}"

  /- Create new placeholder mvars -/
  let mvarIdsPairs ← mvarIds.mapM
    (fun x => return (x, ←mkFreshExprMVar none (userName := (← x.getDecl).userName)))
  let mvarIdsMap : HashMap MVarId Expr := .ofList mvarIdsPairs

  /- newPattern is the placeholder pattern with a bunch of placeholder mvars -/
  let newPattern := origPattern.replace fun x => match x with
    | .mvar x => mvarIdsMap.find? x
    | _ => none

  /- We let isDefEq match the given pattern -/
  let mctx ← getMCtx
  let mdecls := mctx.decls
  if ← isDefEq e newPattern then
    /- We iterate over the (old, new) vars -/
    mvarIdsPairs.forM fun (mvarIdOld, mvarExprNew) => do
      let mvarIdNew := mvarExprNew.mvarId!
      match (mdecls.find! mvarIdNew).userName with
      | Name.anonymous => mvarIdOld.assign mvarExprNew
      | name =>
        let a := mkIdent name
        let ha := mkIdent <| name.appendBefore "h"
        let goal ← getMainGoal
        match (←getExprMVarAssignment? mvarIdNew) with
        | .some mvarAss =>
          /-
          Here mvarIdNew is assigned to mvarAss, and mvarIdOld <-> mvarIdNew, so we
            (1) let $a := mvarAss -- Here fvarId stores $a (?)
            (2) have $ha : $a = mvarAss := rfl
            (3) assign $a to mvarIdOld
          -/
          let mvarType ← inferType mvarAss
          let (fvarId, goal) ← (←goal.define a.getId mvarType mvarAss).intro1P
          replaceMainGoal [goal]
          evalTactic (←`(tactic| have $ha : $a = $(←Term.exprToSyntax mvarAss) := rfl))
          mvarIdOld.assign (.fvar fvarId)
          withLocation loc
            (discard <| tryTactic <| rewriteLocalDecl ha true ·)
            (discard <| tryTactic <| rewriteTarget ha true)
            (discard <| return ·)
        | none => throwError "setm: mvar not assigned. File a bug report!"
      mvarIdOld.setUserName <| (← mkFreshUserName (← mvarIdOld.getDecl).userName)
      mvarIdNew.setUserName <| (← mkFreshUserName (← mvarIdNew.getDecl).userName)
  else
    throwError "setm: {stx} is not definitionally equal to the goal."

/--
The `setm` tactic ("`set` with matching") matches a pattern containing named holes the type of a
local declaration (using the `at h` syntax) or the main goal, and introduces `let` bound variables
representing subexpressions whose location corresponds to the given named hole. These variables are
also substituted into the type of declaration (or main goal).

For example, if the goal is `⊢ (x + 5) ^ 2 + (2 * y + x) * (x + 5) + 3 = 28` (with `x y : ℕ`), then
`setm ?a ^ 2 + ?b * ?a + 3 = 28` would introduce `a : ℕ := x + 5` and `b : ℕ := 2 * y + 5` into the
context and change the goal to `a ^ 2 + b * a + 3 = 28`.

Likewise if the local context contains `h : (x + 5) ^ 2 + (2 * y + x) * (x + 5) + 3 = 28`
(with `x y : ℕ`), then `setm ?a ^ 2 + ?b * ?a + 3 = 28 at h` would introduce `a : ℕ := x + 5` and
`b : ℕ := 2 * y + 5` into the context and changes the type to `h : a ^ 2 + b * a + 3 = 28`. -/
syntax (name := setM) "setm" term (" using " term)? (location)? : tactic
elab_rules : tactic
| `(tactic| setm $stx $[using $usingArg]? $[$loc]?) => do
  let target ← match (← usingArg.mapM (elabTerm · none)) with
  | some target => inferType target
  | none => getMainTarget
  let loc := (loc.map expandLocation).getD (.targets #[] true)
  setMCore target stx loc
