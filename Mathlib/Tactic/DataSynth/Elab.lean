-- import Lean.Elab.Tactic.Conv
import Mathlib.Tactic.DataSynth.Core
-- import Mathlib.Tactic.FunProp.Elab
-- import Mathlib.Tactic.DataSynth.Simproc

namespace Mathlib.Meta.DataSynth

open Lean Meta Elab Tactic Term Conv

declare_config_elab elabDataSynthConfig Config

def elabConvRewrite (stx : TSyntax `conv) (e : Expr) :
    TermElabM Simp.Result := do

  let (rhs, eq) ← mkConvGoalFor e
  let goals ← Tactic.run eq.mvarId! do
    let (lhsNew, proof) ← convert e (Tactic.evalTactic stx)
    updateLhs lhsNew proof

  -- the rewrite failed as there are left over goals, return original expression
  unless goals.length = 1 do
    return { expr:=e }

  -- fill in the equality goal, this will set `rhs` to `lhsNew`
  (goals[0]!).refl

  return {
    expr := ← instantiateMVars rhs
    proof? := ← instantiateMVars eq
  }

open Parser.Tactic.Conv in
def elabNormalizer (stx? : Option (TSyntax ``convSeq)) (e : Expr) : MetaM Simp.Result := do
  match stx? with
  | .none => pure { expr:=e }
  | .some stx => 
    let (r,_) ← (elabConvRewrite (← `(conv| ($stx))) e).run {} {}
    return r

open Parser.Tactic.Conv in
syntax normalizer := 
  atomic(" (" patternIgnore(&"normalizer" <|> &"norm")) " := " withoutPosition(convSeq) ")"

open Parser.Tactic Conv in
syntax (name:=data_synth_tac) 
  "data_synth" optConfig (discharger)? (normalizer)? ("=>" convSeq)? : tactic

@[tactic data_synth_tac] unsafe def dataSynthTactic : Tactic
| `(tactic| data_synth $cfg:optConfig $[$disch?]? $[(norm := $norm)]? $[=> $c]?) => do
  let m ← getMainGoal
  m.withContext do
  let e ← m.getType

  let cfg ← elabDataSynthConfig cfg

  let some g ← isDataSynthGoal? e
    | throwError "{e} is not `data_synth` goal"

  let ctx : Context := { 
    config := cfg 
    norm := fun e => do
      elabNormalizer norm e
  }
  let thms := theoremsExt.getState (← getEnv)
  let stateRef : IO.Ref DataSynth.State ← IO.mkRef {theorems:=thms}

  -- let disch : Expr → MetaM (Option Expr) :=
  --   pmatch disch? with
  --   | none => fun _ => return none
  --   | some _stx => Mathlib.Meta.FunProp.tacticToDischarge ⟨stx.raw[3]⟩

  let simpContext ← Simp.mkContext (config := cfg.toConfig) (simpTheorems := #[← getSimpTheorems])
  let simpStateRef : IO.Ref Simp.State ← IO.mkRef {}
  let simpMethodsRef := (← Simp.mkDefaultMethods).toMethodsRef

  let r? ← dataSynth g 
    ctx stateRef
    simpMethodsRef simpContext simpStateRef

  match r? with
  | some r =>
    let mut e' := r.getSolvedGoal
    if ← isDefEq e e' then
      m.assign r.proof
      setGoals []
    else
      throwError "faield to assign data {e'}"
  | none =>
    throwError "`data_synth` failed"
| _ => throwUnsupportedSyntax


end Mathlib.Meta.DataSynth
