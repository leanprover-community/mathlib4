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

/--
Helper function to fill implicit arguments with metavariables.
-/
partial def fillImplicitArgumentsWithFreshMVars (e : Expr) : MetaM Expr := do
  match ← inferType e with
  | Expr.forallE _ _ _ .implicit
  | Expr.forallE _ _ _ .instImplicit => do
    fillImplicitArgumentsWithFreshMVars (mkApp e (← mkFreshExprMVar none))
  | _                    => pure e

/-- Apply a function to a hypothesis. -/
def applyFunHyp (f : Expr) (using? : Option Expr) (h : FVarId) (g : MVarId) :
    MetaM (List MVarId) := do
  let d ← h.getDecl
  let (prf, newGoals) ← match (← whnfR (← instantiateMVars d.type)).getAppFnArgs with
  | (``Eq, #[α, _, _]) => do
    -- We have to jump through a hoop here!
    -- At this point Lean may think `f` is a dependently-typed function,
    -- so we can't just feed it to `congrArg`.
    -- To solve this, we first fill any implicit arguments for `f` with metavariables,
    -- and then try to unify with a metavariable `_ : α → _`
    -- (i.e. an arrow, but with the target as some fresh type metavariable).
    -- (Arguably `Lean.Meta.mkCongrArg` could do this all itself.)
    let arrow ← mkFreshExprMVar (← mkArrow α (← mkFreshTypeMVar))
    let f' ← fillImplicitArgumentsWithFreshMVars f
    if ¬ (← isDefEq f' arrow) then
      throwError "Can not use `apply_fun` with a dependently typed function."
    pure (← mkCongrArg f' d.toExpr, [])
  | (``LE.le, _) =>
    let (monotone_f, newGoals) ← match using? with
    -- Use the expression passed with `using`
    | some r => pure (r, [])
    -- Create a new `Monotone f` goal
    | none => do
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
def applyFunTargetFailure (f : Expr) : MetaM (List MVarId) := do
  throwError "`apply_fun` could not apply `{f}` to the main goal."

/-- Apply a function to the main goal. -/
def applyFunTarget (f : Expr) (using? : Option Expr) (g : MVarId) : MetaM (List MVarId) := do
  match (← g.getType).getAppFnArgs with
  | (``Ne, #[_, _, _]) => g.apply (← mkAppM ``ne_of_apply_ne #[f])
  | (``Not, #[p]) => match p.getAppFnArgs with
    | (``Eq, #[_, _, _]) => g.apply (← mkAppM ``ne_of_apply_ne #[f])
    | _ => applyFunTargetFailure f
  -- TODO Once `Order.Hom.Basic` has been ported, verify these work.
  -- | (``LE.le, _) => g.apply (← mkAppM ``OrderIso.le_iff_le #[f])
  -- | (``GE.ge, _) => g.apply (← mkAppM ``OrderIso.le_iff_le #[f])
  -- | (``LT.lt, _) => g.apply (← mkAppM ``OrderIso.lt_iff_lt #[f])
  -- | (``GT.gt, _) => g.apply (← mkAppM ``OrderIso.lt_iff_lt #[f])
  | (``Eq, #[_, _, _]) => do
    let ng ← mkFreshExprMVar (← mkAppM ``Function.Injective #[f])
    -- Try the `using` clause
    if let some u := using? then _ ← isDefEq ng u
    -- Try an assumption
    try ng.mvarId!.assumption catch _ =>
      -- TODO Once `Logic.Equiv.Basic` has been ported, verify this works.
      -- try return ← ng.mvarId!.apply (mkConst ``Equiv.injective) catch _ =>
      pure ()
    g.apply ng
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
  let f ← elabTermForApply f
  let P ← P.mapM (elabTerm · none)
  withLocation (expandOptLocation (Lean.mkOptionalNode loc))
    (atLocal := fun h ↦ liftMetaTactic <| applyFunHyp f P h)
    (atTarget := liftMetaTactic <| applyFunTarget f P)
    (failed := fun _ ↦ throwError "apply_fun failed")
