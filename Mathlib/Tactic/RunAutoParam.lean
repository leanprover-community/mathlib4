import Lean
-- import Mathlib

open Lean Meta Elab Tactic

namespace Mathlib.Meta

private def tacticToDischarge' (tacticCode : Syntax) : TacticM (IO.Ref Term.State × (Expr → MetaM (Option Expr))) := do
  let tacticCode : TSyntax `Lean.Parser.Tactic.tacticSeq := ⟨tacticCode⟩
  let tacticCode ← `(tactic| try ($tacticCode:tacticSeq))
  let ref ← IO.mkRef (← getThe Term.State)
  let ctx ← readThe Term.Context
  let disch : Expr → MetaM (Option Expr) := fun e => do
    let mvar ← mkFreshExprSyntheticOpaqueMVar e `simp.discharger
    let s ← ref.get
    let runTac? : TermElabM (Option Expr) :=
      try
        /- We must only save messages and info tree changes. Recall that `simp` uses temporary metavariables (`withNewMCtxDepth`).
           So, we must not save references to them at `Term.State`.
        -/
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
    let (result?, s) ← Term.TermElabM.run runTac? ctx s
    ref.set s
    return result?
  return (ref, disch)

syntax (name:=runAutoParamStx) "run_auto_param" : tactic

@[tactic runAutoParamStx]
def runAutoParam : Tactic := fun _ => do

  let goal ← getMainGoal
  let type ← goal.getType

  let some (.const tacticDecl _) := type.getAutoParamTactic?
    | return ()
  let type := type.appFn!.appArg!

  let env ← getEnv
  let opts ← getOptions
  let .ok tacticSyntax := evalSyntaxConstant env  opts tacticDecl
    | return ()

  let (_, disch) ← tacticToDischarge' tacticSyntax

  let some prf ← disch type
    | return ()

  goal.assign prf
