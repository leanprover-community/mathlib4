/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Meta.Tactic.Assert
import Lean.Meta.Tactic.Clear
import Std.Data.Option.Basic
import Std.Data.List.Basic

/-! ## Additional utilities in `Lean.MVarId` -/

set_option autoImplicit true

open Lean Meta

namespace Lean.MVarId

/-- Add the hypothesis `h : t`, given `v : t`, and return the new `FVarId`. -/
def «let» (g : MVarId) (h : Name) (v : Expr) (t : Option Expr := .none) :
    MetaM (FVarId × MVarId) := do
  (← g.define h (← t.getDM (inferType v)) v).intro1P

/-- Has the effect of `refine ⟨e₁,e₂,⋯, ?_⟩`.
-/
def existsi (mvar : MVarId) (es : List Expr) : MetaM MVarId := do
  es.foldlM (λ mv e => do
      let (subgoals,_) ← Elab.Term.TermElabM.run <| Elab.Tactic.run mv do
        Elab.Tactic.evalTactic (← `(tactic| refine ⟨?_,?_⟩))
      let [sg1, sg2] := subgoals | throwError "expected two subgoals"
      sg1.assign e
      pure sg2)
    mvar

/-- Applies `intro` repeatedly until it fails. We use this instead of
`Lean.MVarId.intros` to allowing unfolding.
For example, if we want to do introductions for propositions like `¬p`,
the `¬` needs to be unfolded into `→ False`, and `intros` does not do such unfolding. -/
partial def intros! (mvarId : MVarId) : MetaM (Array FVarId × MVarId) :=
  run #[] mvarId
  where
  /-- Implementation of `intros!`. -/
  run (acc : Array FVarId) (g : MVarId) :=
  try
    let ⟨f, g⟩ ← mvarId.intro1
    run (acc.push f) g
  catch _ =>
    pure (acc, g)

/--
Try to convert an `Iff` into an `Eq` by applying `iff_of_eq`.
If successful, returns the new goal, and otherwise returns the original `MVarId`.

This may be regarded as being a special case of `Lean.MVarId.liftReflToEq`, specifically for `Iff`.
-/
def iffOfEq (mvarId : MVarId) : MetaM MVarId := do
  let res ← observing? do
    let [mvarId] ← mvarId.apply (mkConst ``iff_of_eq []) | failure
    return mvarId
  return res.getD mvarId

/--
Try to convert an `Eq` into an `Iff` by applying `propext`.
If successful, then returns then new goal, otherwise returns the original `MVarId`.
-/
def propext (mvarId : MVarId) : MetaM MVarId := do
  let res ← observing? do
    -- Avoid applying `propext` if the target is not an equality of `Prop`s.
    -- We don't want a unification specializing `Sort*` to `Prop`.
    let tgt ← withReducible mvarId.getType'
    let some (ty, _, _) := tgt.eq? | failure
    guard ty.isProp
    let [mvarId] ← mvarId.apply (mkConst ``propext []) | failure
    return mvarId
  return res.getD mvarId

/--
Try to close the goal with using `proof_irrel_heq`. Returns whether or not it succeeds.

We need to be somewhat careful not to assign metavariables while doing this, otherwise we might
specialize `Sort _` to `Prop`.
-/
def proofIrrelHeq (mvarId : MVarId) : MetaM Bool :=
  mvarId.withContext do
    let res ← observing? do
      mvarId.checkNotAssigned `proofIrrelHeq
      let tgt ← withReducible mvarId.getType'
      let some (_, lhs, _, rhs) := tgt.heq? | failure
      -- Note: `mkAppM` uses `withNewMCtxDepth`, which prevents `Sort _` from specializing to `Prop`
      let pf ← mkAppM ``proof_irrel_heq #[lhs, rhs]
      mvarId.assign pf
      return true
    return res.getD false

/--
Try to close the goal using `Subsingleton.elim`. Returns whether or not it succeeds.

We are careful to apply `Subsingleton.elim` in a way that does not assign any metavariables.
This is to prevent the `Subsingleton Prop` instance from being used as justification to specialize
`Sort _` to `Prop`.
-/
def subsingletonElim (mvarId : MVarId) : MetaM Bool :=
  mvarId.withContext do
    let res ← observing? do
      mvarId.checkNotAssigned `subsingletonElim
      let tgt ← withReducible mvarId.getType'
      let some (_, lhs, rhs) := tgt.eq? | failure
      -- Note: `mkAppM` uses `withNewMCtxDepth`, which prevents `Sort _` from specializing to `Prop`
      let pf ← mkAppM ``Subsingleton.elim #[lhs, rhs]
      mvarId.assign pf
      return true
    return res.getD false

end Lean.MVarId

namespace Lean.Meta

/-- Count how many local hypotheses appear in an expression. -/
def countLocalHypsUsed [Monad m] [MonadLCtx m] [MonadMCtx m] (e : Expr) : m Nat := do
  let e' ← instantiateMVars e
  return (← getLocalHyps).toList.countP fun h => h.occurs e'

/--
Given a monadic function `F` that takes a type and a term of that type and produces a new term,
lifts this to the monadic function that opens a `∀` telescope, applies `F` to the body,
and then builds the lambda telescope term for the new term.
-/
def mapForallTelescope' (F : Expr → Expr → MetaM Expr) (forallTerm : Expr) : MetaM Expr := do
  forallTelescope (← Meta.inferType forallTerm) fun xs ty => do
    Meta.mkLambdaFVars xs (← F ty (mkAppN forallTerm xs))

/--
Given a monadic function `F` that takes a term and produces a new term,
lifts this to the monadic function that opens a `∀` telescope, applies `F` to the body,
and then builds the lambda telescope term for the new term.
-/
def mapForallTelescope (F : Expr → MetaM Expr) (forallTerm : Expr) : MetaM Expr := do
  mapForallTelescope' (fun _ e => F e) forallTerm


/-- Get the type the given metavariable after instantiating metavariables and cleaning up
annotations. -/
def _root_.Lean.MVarId.getType'' (mvarId : MVarId) : MetaM Expr :=
  return (← instantiateMVars (← mvarId.getType)).cleanupAnnotations

end Lean.Meta

namespace Lean.Elab.Tactic

/-- Analogue of `liftMetaTactic` for tactics that return a single goal. -/
-- I'd prefer to call that `liftMetaTactic1`,
-- but that is taken in core by a function that lifts a `tac : MVarId → MetaM (Option MVarId)`.
def liftMetaTactic' (tac : MVarId → MetaM MVarId) : TacticM Unit :=
  liftMetaTactic fun g => do pure [← tac g]

@[inline] private def TacticM.runCore (x : TacticM α) (ctx : Context) (s : State) :
    TermElabM (α × State) :=
  x ctx |>.run s

@[inline] private def TacticM.runCore' (x : TacticM α) (ctx : Context) (s : State) : TermElabM α :=
  Prod.fst <$> x.runCore ctx s

/-- Copy of `Lean.Elab.Tactic.run` that can return a value. -/
-- We need this because Lean 4 core only provides `TacticM` functions for building simp contexts,
-- making it quite painful to call `simp` from `MetaM`.
def run_for (mvarId : MVarId) (x : TacticM α) : TermElabM (Option α × List MVarId) :=
  mvarId.withContext do
   let pendingMVarsSaved := (← get).pendingMVars
   modify fun s => { s with pendingMVars := [] }
   let aux : TacticM (Option α × List MVarId) :=
     /- Important: the following `try` does not backtrack the state.
        This is intentional because we don't want to backtrack the error message
        when we catch the "abort internal exception"
        We must define `run` here because we define `MonadExcept` instance for `TacticM` -/
     try
       let a ← x
       pure (a, ← getUnsolvedGoals)
     catch ex =>
       if isAbortTacticException ex then
         pure (none, ← getUnsolvedGoals)
       else
         throw ex
   try
     aux.runCore' { elaborator := .anonymous } { goals := [mvarId] }
   finally
     modify fun s => { s with pendingMVars := pendingMVarsSaved }

end Lean.Elab.Tactic
