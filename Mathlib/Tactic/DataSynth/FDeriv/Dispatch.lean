import Mathlib.Tactic.DataSynth.FDeriv.Basic
import Mathlib.Tactic.DataSynth.ToBatteries

namespace Mathlib.Meta.DataSynth

open Lean Meta Mathlib.Meta.DataSynth in
def hasFDerivAtDispatch (goal : Goal) : DataSynthM (Option Result) := do
    trace[Meta.Tactic.data_synth] m!"calling custom callback for HasFDerivAt"
    let (_, e) ← goal.mkFreshProofGoal
    let fn := e.getArg! 10
    match (← whnfR fn) with
    | .lam _ _ b _ =>
      match b with
      | .app .. =>
        let .some (f, g) ← lambdaDecompose fn | return none
    
        let compThm ← getTheoremFromConst ``HasFDerivAt.fun_comp
        let hints := #[(11, g), (13, f)]

        return ← goal.tryTheorem? compThm hints #[]
      | _ => return none
    | _ => 
      return none

-- hmm this does not seem to be persisten across imports :(
run_meta Mathlib.Meta.DataSynth.setCustomDispatch ``HasFDerivAt ``hasFDerivAtDispatch

end Mathlib.Meta.DataSynth
