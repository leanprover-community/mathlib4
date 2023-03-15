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

Returns an array of the metavariables as well.
-/
partial def fillImplicitArgumentsWithFreshMVars (e : Expr) : MetaM (Expr × Array MVarId) := do
  loop #[] (← instantiateMVars (← inferType e)) (← instantiateMVars e)
where
  loop (mvars : Array MVarId) (ty e : Expr) : MetaM (Expr × Array MVarId) := do
    if ty.isForall then
      if ty.bindingInfo! == .implicit then
        let mvar ← mkFreshExprMVar ty.bindingDomain! MetavarKind.natural ty.bindingName!
        return ← loop (mvars.push mvar.mvarId!) (ty.bindingBody!.instantiate1 mvar) (e.beta #[mvar])
      else if ty.bindingInfo! == .instImplicit then
        let mvar ← mkFreshExprMVar ty.bindingDomain! MetavarKind.synthetic ty.bindingName!
        return ← loop (mvars.push mvar.mvarId!) (ty.bindingBody!.instantiate1 mvar) (e.beta #[mvar])
    return (e, mvars)

/-- Returns a function. Ensures all leading implicit variables are filled, and (recursively)
uses `CoeFun` instances. -/
private def ensureFun (f : Expr) (steps : Nat := 10000) : MetaM (Expr × Array MVarId) :=
  match steps with
  | 0 => throwError "Could not coerce to function (iteration limit reached)"
  | steps + 1 => do
    let (f, mvars) ← fillImplicitArgumentsWithFreshMVars f
    if (← inferType f).isForall then
      return (f, mvars)
    else
      let some f ← coerceToFunction? f
        | throwError "Could not coerce to function"
      let (f', mvars') ← ensureFun f steps
      return (f', mvars ++ mvars')

/-- Apply a function to a hypothesis. -/
def applyFunHyp (f : Expr) (using? : Option Expr) (h : FVarId) (g : MVarId) :
    MetaM (List MVarId) := do
  let d ← h.getDecl
  let (prf, newGoals) ← match (← whnfR (← instantiateMVars d.type)).getAppFnArgs with
  | (``Eq, #[ty, lhs, rhs]) => do
    let (f, mvars) ← ensureFun f
    let argTy := (← inferType f).bindingDomain!
    unless ← isDefEq argTy ty do
      throwAppTypeMismatch argTy ty
    -- Note: there might be implicit arguments *after* lhs and rhs
    let (lhs', mvarslhs) ← fillImplicitArgumentsWithFreshMVars (f.beta #[lhs])
    let (rhs', mvarsrhs) ← fillImplicitArgumentsWithFreshMVars (f.beta #[rhs])
    unless ← isDefEq (← inferType lhs') (← inferType rhs') do
      let msg ← mkHasTypeButIsExpectedMsg (← inferType rhs') (← inferType lhs')
      throwError "In generated equality, right-hand side {msg}"
    let mvars := mvars ++ mvarslhs ++ mvarsrhs
    -- `mkAppN` would do this, but it uses `withNewMCtxDepth`.
    for mvarId in mvars do
      let d ← mvarId.getDecl
      if let .synthetic := d.kind then
        mvarId.assign (← synthInstance (← mvarId.getType))
    let eq' ← instantiateMVars (← mkEq lhs' rhs')
    let mvar ← mkFreshExprMVar eq'
    let [] ← mvar.mvarId!.congrN | throwError "`apply_fun` could not construct congruence"
    pure (mvar, mvars.toList)
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
