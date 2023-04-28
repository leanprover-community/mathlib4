/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Elab
import Lean.Meta.Tactic.Assert
import Lean.Meta.Tactic.Clear
import Std.Data.Option.Basic

/-! ## Additional utilities in `Lean.MVarId` -/

open Lean Meta

namespace Lean.MVarId

/-- Solve a goal by synthesizing an instance. -/
-- FIXME: probably can just be `g.inferInstance` once lean4#2054 is fixed
def synthInstance (g : MVarId) : MetaM Unit := do
  g.assign (← Lean.Meta.synthInstance (← g.getType))

/--
Replace hypothesis `hyp` in goal `g` with `proof : typeNew`.
The new hypothesis is given the same user name as the original,
it attempts to avoid reordering hypotheses, and the original is cleared if possible.
-/
-- adapted from Lean.Meta.replaceLocalDeclCore
def replace (g : MVarId) (hyp : FVarId) (proof : Expr) (typeNew : Option Expr := none) :
    MetaM AssertAfterResult :=
  g.withContext do
    let typeNew ← typeNew.getDM (inferType proof)
    let ldecl ← hyp.getDecl
    -- `typeNew` may contain variables that occur after `hyp`.
    -- Thus, we use the auxiliary function `findMaxFVar` to ensure `typeNew` is well-formed
    -- at the position we are inserting it.
    let (_, ldecl') ← findMaxFVar typeNew |>.run ldecl
    let result ← g.assertAfter ldecl'.fvarId ldecl.userName typeNew proof
    (return { result with mvarId := ← result.mvarId.clear hyp }) <|> pure result
where
  /-- Finds the `LocalDecl` for the FVar in `e` with the highest index. -/
  findMaxFVar (e : Expr) : StateRefT LocalDecl MetaM Unit :=
    e.forEach' fun e ↦ do
      if e.isFVar then
        let ldecl' ← e.fvarId!.getDecl
        modify fun ldecl ↦ if ldecl'.index > ldecl.index then ldecl' else ldecl
        return false
      else
        return e.hasFVar

/-- Add the hypothesis `h : t`, given `v : t`, and return the new `FVarId`. -/
def note (g : MVarId) (h : Name) (v : Expr) (t : Option Expr := .none) :
    MetaM (FVarId × MVarId) := do
  (← g.assert h (← t.getDM (inferType v)) v).intro1P

/-- Add the hypothesis `h : t`, given `v : t`, and return the new `FVarId`. -/
def «let» (g : MVarId) (h : Name) (v : Expr) (t : Option Expr := .none) :
    MetaM (FVarId × MVarId) := do
  (← g.define h (← t.getDM (inferType v)) v).intro1P

/-- Has the effect of `refine ⟨e₁,e₂,⋯, ?_⟩`.
-/
def existsi (mvar : MVarId) (es : List Expr) : MetaM MVarId := do
  es.foldlM (λ mv e => do
      let (subgoals,_) ← Elab.Term.TermElabM.run $ Elab.Tactic.run mv do
        Elab.Tactic.evalTactic (←`(tactic| refine ⟨?_,?_⟩))
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

end Lean.MVarId

namespace Lean.Meta

/-- Return local hypotheses which are not "implementation detail", as `Expr`s. -/
def getLocalHyps : MetaM (Array Expr) := do
  let mut hs := #[]
  for d in ← getLCtx do
    if !d.isImplementationDetail then hs := hs.push d.toExpr
  return hs

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

end Lean.Meta

section SynthInstance

/-- Elaborate the following term with `set_option synthInstance.etaExperiment true`. -/
macro "eta_experiment% " a:term : term => `(term|set_option synthInstance.etaExperiment true in $a)

end SynthInstance

namespace Lean.Elab.Tactic

/-- Analogue of `liftMetaTactic` for tactics that return a single goal. -/
-- I'd prefer to call that `liftMetaTactic1`,
-- but that is taken in core by a function that lifts a `tac : MVarId → MetaM (Option MVarId)`.
def liftMetaTactic' (tac : MVarId → MetaM MVarId) : TacticM Unit :=
  liftMetaTactic fun g => do pure [← tac g]

/-- Analogue of `liftMetaTactic` for tactics that do not return any goals. -/
def liftMetaFinishingTactic (tac : MVarId → MetaM Unit) : TacticM Unit :=
  liftMetaTactic fun g => do tac g; pure []

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
