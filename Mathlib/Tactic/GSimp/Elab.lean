/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Tactic.GSimp.Core

/-!
# generalized rewriting

This module implements the generalized rewriting similar to how `simp` is implemented,
hence this will be called the `gsimp` tactic.
-/

public meta section

namespace Mathlib.Tactic.GSimp
open Lean Meta Elab Tactic

declare_config_elab elabGSimpConfig Config

/--
Implement a `gsimp` discharge function using the given tactic syntax code.
Recall that `gsimp` dischargers are in `MetaM` which does not have access to `Term.State`.
We need access to `Term.State` to store messages and update the info tree.
Thus, we create an `IO.ref` to track these changes at `Term.State` when we execute `tacticCode`.
We must set this reference with the current `Term.State` before we execute `simp` using the
generated `Simp.Discharge`. -/
def tacticToDischarge (tacticCode : Syntax) : TacticM (IO.Ref Term.State × Discharge) := do
  let tacticCode ← `(tactic| try ($(⟨tacticCode⟩):tacticSeq))
  let ref ← IO.mkRef (← getThe Term.State)
  let ctx ← readThe Term.Context
  let disch : Discharge := fun e => do
    let mvar ← mkFreshExprSyntheticOpaqueMVar e `gsimp.discharger
    let s ← ref.get
    let runTac? : TermElabM (Option Expr) :=
      try
        /- We must only save messages and info tree changes.
        Recall that `simp` uses temporary metavariables (`withNewMCtxDepth`).
        So, we must not save references to them at `Term.State`. -/
        Term.withoutModifyingElabMetaStateWithInfo do
          Term.withSynthesize (postpone := .no) do
            Term.runTactic (report := false) mvar.mvarId! tacticCode .term
          let result ← instantiateMVars mvar
          if result.hasExprMVar then
            return none
          else
            return some result
      catch _ =>
        return none
    let (result?, s) ← liftM (m := MetaM) <| Term.TermElabM.run runTac? ctx s
    ref.set s
    return result?
  return (ref, disch)

inductive DischargeWrapper where
  | default
  | custom (ref : IO.Ref Term.State) (discharge : Discharge)

def DischargeWrapper.with {α} (w : DischargeWrapper)
    (x : Option Discharge → TacticM α) : TacticM α := do
  match w with
  | default => x none
  | custom ref d =>
    ref.set (← getThe Term.State)
    try
      x d
    finally
      set (← ref.get)

/-- Construct a `Simp.DischargeWrapper` from the `Syntax` for a `simp` discharger. -/
private def mkDischargeWrapper (optDischargeSyntax : Syntax) : TacticM DischargeWrapper := do
  if optDischargeSyntax.isNone then
    return .default
  else
    let (ref, d) ← tacticToDischarge optDischargeSyntax[0][3]
    return .custom ref d

/--
`simpLocation ctx discharge? varIdToLemmaId loc`
runs the simplifier at locations specified by `loc`,
using the simp theorems collected in `ctx`
optionally running a discharger specified in `discharge?` on generated subgoals.

Its primary use is as the implementation of the
`simp [...] at ...` and `simp only [...] at ...` syntaxes,
but can also be used by other tactics when a `Syntax` is not available.

For many tactics other than the simplifier,
one should use the `withLocation` tactic combinator
when working with a `location`.
-/
def gsimpLocation (ctx : Context) (discharge? : Option Discharge := none) (loc : Location) :
    TacticM Unit := do
  match loc with
  | Location.targets hyps simplifyTarget =>
    withMainContext do
      let fvarIds ← getFVarIds hyps
      go fvarIds simplifyTarget
  | Location.wildcard =>
    withMainContext do
      go (← (← getMainGoal).getNondepPropHyps) (simplifyTarget := true)
where
  go (fvarIdsToSimp : Array FVarId) (simplifyTarget : Bool) : TacticM Unit := do
    let mvarId ← getMainGoal
    let result? ← gsimpGoal mvarId ctx discharge? simplifyTarget fvarIdsToSimp
    match result? with
    | none => replaceMainGoal []
    | some (_, mvarId) => replaceMainGoal [mvarId]



private def resolveGSimpIdTheorem? (simpArgTerm : Term) : TermElabM (Option Expr) := do
  match simpArgTerm with
  | `($id:ident) =>
    if let some e ← Term.resolveId? simpArgTerm (withInfo := true) then
      return e
    else
      throwUnknownIdentifierAt id id.getId
  | _ =>
    return none

private def elabGSimpTheorem (id : Origin) (stx : Syntax)
    (post : Bool) (inv : Bool) : TermElabM (Option GSimpTheorem) := do
  let thm? ← Term.withoutModifyingElabMetaStateWithInfo <| withRef stx do
    let e ← Term.elabTerm stx .none
    Term.synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
    let e ← instantiateMVars e
    if e.hasSyntheticSorry then
      return .none
    let e := e.eta
    if e.hasMVar then
      let r ← abstractMVars e
      return some (r.paramNames, r.expr)
    else
      return some (#[], e)
  thm?.mapM fun (levelParams, proof) ↦
    mkGSimpTheoremFromExpr id levelParams proof (post := post) (inv := inv)

/-- Parses a `Lean.Parser.Tactic.simpLemma` as a `gsimp` lemma. -/
private def elabGSimpArg (arg : Syntax) : TacticM (Option GSimpTheorem) := withRef arg do
  try
    if arg.getKind == ``Lean.Parser.Tactic.simpLemma then
      let post :=
        if arg[0].isNone then
          true
        else
          arg[0][0].getKind == ``Parser.Tactic.simpPost
      let inv  := !arg[1].isNone
      let term := arg[2]
      match ← resolveGSimpIdTheorem? ⟨term⟩ with
      | some e  =>
        let name ← mkFreshId
        some <$> mkGSimpTheoremFromExpr (.stx name arg) #[] e (post := post) (inv := inv)
      | none    =>
        let name ← mkFreshId
        elabGSimpTheorem (.stx name arg) term (post := post) (inv := inv)
    else
      throwUnsupportedSyntax
  catch ex =>
    if (← read).recover then
      logException ex
      return none
    else
      throw ex

/--
Elaborate extra gsimp theorems provided to `gsimp`. `stx` is of the form `"[" simpTheorem,* "]"`
When `recover := true`, try to recover from errors as much as possible so that users keep seeing
the current goal.
-/
def elabGSimpArgs (stx : Syntax) (thms : GSimpTheorems) : TacticM GSimpTheorems := do
  if stx.isNone then
    return thms
  else
    let go := withMainContext do
      let mut thms := thms
      for argStx in stx[1].getSepArgs do
        if let some thm ← elabGSimpArg argStx then
          thms := thms.unerase thm.origin
          thms := thms.addGSimpTheorem thm
      return thms
    -- If recovery is disabled, then we want simp argument elaboration failures to be exceptions.
    -- This affects `addGSimpTheorem`.
    if (← read).recover then
      go
    else
      Term.withoutErrToSorry go

/-- Create the `GSimp.Context` for the `gsimp` tactic. -/
def mkGSimpContext (stx : Syntax) (gsimpTheorems : CoreM GSimpTheorems := pure {}) :
    TacticM Context := do
  -- let simpOnly := !stx[simpOnlyPos].isNone
  let config ← elabGSimpConfig stx[1]
  let gcongrTheorems := GCongr.gcongrExt.getState (← getEnv)
  let gsimpTheorems ← elabGSimpArgs stx[4] (← gsimpTheorems)
  return {
    config
    gsimpTheorems
    gcongrTheorems
    idx := 0 -- The index for the implication relation is 0
    rel := default
    relName := `_Forall }

open Parser.Tactic in
/--
The `gsimp` tactic.
-/
syntax (name := gsimpStx) "gsimp" optConfig (discharger)? (&" only")?
  (" [" withoutPosition(simpLemma,*,?) "]")? (location)? : tactic
/-
  "gsimp" optConfig (discharger)? (" only")? (" [" (simpLemma,*,?) "]")?
  (location)?
-/
@[tactic Lean.Parser.Tactic.simp] def evalGSimp : Tactic := fun stx => withMainContext do
  let dischargeWrapper ← mkDischargeWrapper stx[2]
  let ctx ← mkGSimpContext stx
  let stats ← dischargeWrapper.with fun discharge? =>
    gsimpLocation ctx discharge? (expandOptLocation stx[5])

end Mathlib.Tactic.GSimp
