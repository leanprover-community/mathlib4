/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek, Patrick Massot, Scott Morrison
-/
import Mathlib.Lean.Expr.Basic
import Mathlib.Order.Monotone.Basic

/-!
# The `apply_fun` tactic.

Apply a function to an equality or inequality in either a local hypothesis or the goal.

## Porting notes
When the `mono` tactic has been ported we can attempt to automatically discharge `Monotone f` goals.

When `Logic.Equiv.Basic` and `Order.Hom.Basic` have been ported some additional testing is required.
-/

namespace Mathlib.Tactic
open Lean Parser Tactic Elab Tactic Meta

initialize registerTraceClass `apply_fun

/-- Apply a function to a hypothesis. -/
def applyFunHyp (f : Term) (using? : Option Expr) (h : FVarId) (g : MVarId) :
    TacticM (List MVarId) := do
  let d ← h.getDecl
  let (prf, newGoals) ← match (← whnfR (← instantiateMVars d.type)).getAppFnArgs with
  | (``Eq, #[_, lhs, rhs]) => do
    let (eq', gs) ← withCollectingNewGoalsFrom (tagSuffix := `apply_fun) <|
      withoutRecover <| runTermElab <| do
        let f ← Term.elabTerm f none
        let lhs' ← Term.elabAppArgs f #[] #[.expr lhs] none false false
        let rhs' ← Term.elabAppArgs f #[] #[.expr rhs] none false false
        unless ← isDefEq (← inferType lhs') (← inferType rhs') do
          let msg ← mkHasTypeButIsExpectedMsg (← inferType rhs') (← inferType lhs')
          throwError "In generated equality, right-hand side {msg}"
        let eq ← mkEq lhs'.headBeta rhs'.headBeta
        Term.synthesizeSyntheticMVarsUsingDefault
        instantiateMVars eq
    let mvar ← mkFreshExprMVar eq'
    let [] ← mvar.mvarId!.congrN! | throwError "`apply_fun` could not construct congruence"
    pure (mvar, gs)
  | (``LE.le, _) =>
    let (monotone_f, newGoals) ← match using? with
    -- Use the expression passed with `using`
    | some r => pure (r, [])
    -- Create a new `Monotone f` goal
    | none => do
      let f ← elabTermForApply f
      let ng ← mkFreshExprMVar (← mkAppM ``Monotone #[f])
      -- TODO attempt to solve this goal using `mono` when it has been ported,
      -- via `synthesizeUsing`.
      pure (ng, [ng.mvarId!])
    pure (← mkAppM' monotone_f #[d.toExpr], newGoals)
  | _ => throwError "apply_fun can only handle hypotheses of the form `a = b` or `a ≤ b`."

  let g ← g.clear h
  let (_, g) ← g.note d.userName prf
  return g :: newGoals

/-- Failure message for `applyFunTarget`. -/
def applyFunTargetFailure (f : Term) : MetaM (List MVarId) := do
  throwError "`apply_fun` could not apply `{f}` to the main goal."

/-- Given a metavariable `ginj` of type `Injective f`, try to prove it. -/
def proveInjective (ginj : Expr) (using? : Option Expr) : MetaM Bool := do
  -- Try the `using` clause
  if let some u := using? then
    if ← isDefEq ginj u then
      ginj.mvarId!.assign u
      return true
    else
      let err ← mkHasTypeButIsExpectedMsg (← inferType u) (← inferType ginj)
      throwError "Using clause {err}"
  -- Try an assumption
  try ginj.mvarId!.assumption; return true catch _ => pure ()
  -- Try using that this is an equivalence
  let ok ← observing? do
    let [] ← ginj.mvarId!.apply (← mkConstWithFreshMVarLevels ``Equiv.injective) | failure
  if ok.isSome then return true
  return false

/-- Apply a function to the main goal. -/
def applyFunTarget (f : Term) (using? : Option Expr) (g : MVarId) : TacticM (List MVarId) := do
  -- handle applying a two-argument theorem whose first argument is f
  let handle (thm : Name) : TacticM (List MVarId) := do
    let ng ← mkFreshExprMVar none
    let pf ← withoutRecover <| runTermElab do
      let pf ← Term.elabTermEnsuringType (← ``($(mkIdent thm) $f $(← Term.exprToSyntax ng)))
                  (← g.getType)
      Term.synthesizeSyntheticMVarsUsingDefault
      return pf
    g.assign pf
    return [ng.mvarId!]
  match (← g.getType).getAppFnArgs with
  | (``Ne, #[_, _, _]) => handle ``ne_of_apply_ne
  | (``Not, #[p]) => match p.getAppFnArgs with
    | (``Eq, #[_, _, _]) => handle ``ne_of_apply_ne
    | _ => applyFunTargetFailure f
  -- TODO Once `Order.Hom.Basic` has been ported, verify these work.
  -- | (``LE.le, _) => g.apply (← mkAppM ``OrderIso.le_iff_le #[f])
  -- | (``GE.ge, _) => g.apply (← mkAppM ``OrderIso.le_iff_le #[f])
  -- | (``LT.lt, _) => g.apply (← mkAppM ``OrderIso.lt_iff_lt #[f])
  -- | (``GT.gt, _) => g.apply (← mkAppM ``OrderIso.lt_iff_lt #[f])
  | (``Eq, #[_, _, _]) => do
    -- g' is the `f lhs = f rhs` goal, ginj is the `Injective f` goal.
    let (g', ginj) ← withoutRecover <| runTermElab do
      let finj ← Term.elabTerm (← ``(Function.Injective $f)) none
      let ginj ← mkFreshExprMVar finj
      let g' ← mkFreshExprMVar none
      let pf ← Term.elabAppArgs ginj #[] #[.expr g'] (← g.getType) false false
      let pf ← Term.ensureHasType (← g.getType) pf
      Term.synthesizeSyntheticMVarsUsingDefault
      g.assign pf
      return (g', ginj)
    if ← proveInjective ginj using? then
      return [g'.mvarId!]
    else
      return [g'.mvarId!, ginj.mvarId!]
  | _ => applyFunTargetFailure f

/--
Apply a function to an equality or inequality in either a local hypothesis or the goal.

* If we have `h : a = b`, then `apply_fun f at h` will replace this with `h : f a = f b`.
* If we have `h : a ≤ b`, then `apply_fun f at h` will replace this with `h : f a ≤ f b`,
  and create a subsidiary goal `Monotone f`.
  `apply_fun` will automatically attempt to discharge this subsidiary goal using `mono`,
  or an explicit solution can be provided with `apply_fun f at h using P`, where `P : monotone f`.
* If the goal is `a ≠ b`, `apply_fun f` will replace this with `f a ≠ f b`.
* If the goal is `a = b`, `apply_fun f` will replace this with `f a = f b`,
  and create a subsidiary goal `injective f`.
  `apply_fun` will automatically attempt to discharge this subsidiary goal using local hypotheses,
  or if `f` is actually an `Equiv`,
  or an explicit solution can be provided with `apply_fun f using P`, where `P : Injective f`.
* If the goal is `a ≤ b` (or similarly for `a < b`), and `f` is actually an `OrderIso`,
  `apply_fun f` will replace the goal with `f a ≤ f b`.
  If `f` is anything else (e.g. just a function, or an `Equiv`), `apply_fun` will fail.


Typical usage is:
```lean
open Function

example (X Y Z : Type) (f : X → Y) (g : Y → Z) (H : Injective <| g ∘ f) :
    Injective f := by
  intros x x' h
  apply_fun g at h
  exact H h
```
 -/
syntax (name := applyFun) "apply_fun " term (ppSpace location)? (" using " term)? : tactic

elab_rules : tactic | `(tactic| apply_fun $f $[$loc]? $[using $P]?) => do
  let P ← P.mapM (elabTerm · none)
  withLocation (expandOptLocation (Lean.mkOptionalNode loc))
    (atLocal := fun h ↦ do replaceMainGoal <| ← applyFunHyp f P h (← getMainGoal))
    (atTarget := withMainContext do
      replaceMainGoal <| ← applyFunTarget f P (← getMainGoal))
    (failed := fun _ ↦ throwError "apply_fun failed")
