/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek, Patrick Massot, Scott Morrison
-/
import Mathlib.Lean.Expr.Basic
import Mathlib.Order.Monotone
-- TODO when `mono` is ported
-- import Mathlib.Tactic.Monotonicity

namespace Mathlib.Tactic
open Lean Parser Tactic Elab Tactic

/--
Apply a function to an equality or inequality in either a local hypothesis or the goal.

* If we have `h : a = b`, then `apply_fun f at h` will replace this with `h : f a = f b`.
* If we have `h : a ≤ b`, then `apply_fun f at h` will replace this with `h : f a ≤ f b`,
  and create a subsidiary goal `monotone f`.
  `apply_fun` will automatically attempt to discharge this subsidiary goal using `mono`,
  or an explicit solution can be provided with `apply_fun f at h using P`, where `P : monotone f`.
* If the goal is `a ≠ b`, `apply_fun f` will replace this with `f a ≠ f b`.
* If the goal is `a = b`, `apply_fun f` will replace this with `f a = f b`,
  and create a subsidiary goal `injective f`.
  `apply_fun` will automatically attempt to discharge this subsidiary goal using local hypotheses,
  or if `f` is actually an `equiv`,
  or an explicit solution can be provided with `apply_fun f using P`, where `P : injective f`.
* If the goal is `a ≤ b` (or similarly for `a < b`), and `f` is actually an `order_iso`,
  `apply_fun f` will replace the goal with `f a ≤ f b`.
  If `f` is anything else (e.g. just a function, or an `equiv`), `apply_fun` will fail.


Typical usage is:
```lean
open function

example (X Y Z : Type) (f : X → Y) (g : Y → Z) (H : injective $ g ∘ f) :
  injective f := by
  intros x x' h,
  apply_fun g at h,
  exact H h
```
 -/
syntax (name := applyFun) "apply_fun " term (ppSpace location)? (" using " term)? : tactic

open Lean.Meta

initialize registerTraceClass `apply_fun

/--
`g.note n ty by` creates a new hypothesis with name `n`, type `ty`, and proof `by`.
If `ty` is omitted it is inferred from `by`.
-/
def _root_.Lean.MVarId.note (g : MVarId) (n : Name := .anonymous) (type : Option Expr)
    (body : Expr) : MetaM (FVarId × MVarId) := do
  (←(g.assert n (type.getD (← inferType body)) body)).intro1P

/-- Apply a function to a hypothesis. -/
def applyFunHyp (f : Expr) (using? : Option Expr) (h : FVarId) (g : MVarId) : MetaM (List MVarId) := do
  let d ← h.getDecl
  let (prf, newGoals) ← match d.type.getAppFnArgs with
  | (``Eq, #[α, _, _]) => do
    -- We have to jump through a hoop here!
    -- At this point Lean may think `f` is a dependently-typed function,
    -- so we can't just feed it to `congrArg`.
    -- To solve this, we first unify `f` with a metavariable `_ : α → _`
    -- (i.e. an arrow, but with the target as some fresh type metavariable).
    if ¬ (← isDefEq f (← mkFreshExprMVar (← mkArrow α (← mkFreshTypeMVar)))) then
      throwError "Can not use `apply_fun` with a dependently typed function."
    pure (← mkCongrArg f d.toExpr, [])
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
  let (_, g) ← g.note d.userName none prf
  return g :: newGoals

/-- Failure message for `applyFunTarget`. -/
def applyFunTargetFailure (f : Expr) : MetaM (List MVarId) := do
  throwError "`apply_fun` could not apply `f` to the main goal."

/-- Apply a function to the main goal. -/
def applyFunTarget (f : Expr) (using? : Option Expr) (g : MVarId) : MetaM (List MVarId) := do
  match (← g.getType).getAppFnArgs with
  | (``Ne, #[_, _, _]) => g.apply (← mkAppM ``ne_of_apply_ne #[f])
  | (``Not, #[p]) => match p.getAppFnArgs with
    | (``Eq, #[_, _, _]) => g.apply (← mkAppM ``ne_of_apply_ne #[f])
    | _ => applyFunTargetFailure f
  | (``Eq, #[_, _, _]) => do
    let ng ← mkFreshExprMVar (← mkAppM ``Function.injective #[f])
    -- Try the `using` clause
    _ ← using?.mapM (fun u => isDefEq ng u)
    -- Try an assumption
    _ ← try ng.mvarId!.assumption catch _ => pure ()
    -- TODO when `equiv` is ported, try to solve this goal using `equiv.injective`.
    g.apply ng
  -- TODO when order isomorphisms are ported, add more cases here following mathlib3
  | _ => applyFunTargetFailure f

@[tactic applyFun] elab_rules : tactic | `(tactic| apply_fun $f $[$loc]? $[using $P]?) => do
  let f ← elabTermForApply f
  let P ← P.mapM (elabTerm · none)
  withLocation (expandOptLocation (Lean.mkOptionalNode loc))
    (atLocal := fun h => liftMetaTactic <| applyFunHyp f P h)
    (atTarget := liftMetaTactic <| applyFunTarget f P)
    (failed := fun _ => throwError "apply_fun failed")
