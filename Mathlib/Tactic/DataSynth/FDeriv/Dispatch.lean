import Mathlib.Tactic.DataSynth.FDeriv.Basic
import Mathlib.Tactic.DataSynth.ToBatteries

namespace Mathlib.Meta.DataSynth

open Lean Meta Mathlib.Meta.DataSynth

inductive LambdaTheorems

def hasFDerivAtDispatch (goal : Goal) : DataSynthM (Option Result) := do
    trace[Meta.Tactic.data_synth] m!"calling custom callback for HasFDerivAt"
    let (_, e) ← goal.mkFreshProofGoal
    let fn := e.getArg! 10
    match (← whnfR fn) with
    | .lam _ _ b _ =>

      -- body does not depend on the input
      if ¬(b.hasLooseBVar 0) then
        let constThm ← getTheoremFromConst ``hasFDerivAt_const
        return ← goal.tryTheorem? constThm #[] #[]

      match b with
      | .app .. =>
        let .some (f, g) ← lambdaDecompose fn | return none

        let compThm ← getTheoremFromConst ``HasFDerivAt.fun_comp
        let hints := #[(11, g), (13, f)]

        return ← goal.tryTheorem? compThm hints #[]
      | _ => return none
    | _ =>
      return none

run_meta Mathlib.Meta.DataSynth.setCustomDispatch ``HasFDerivAt ``hasFDerivAtDispatch


def hasFDerivAtRegisterTheorem (thmName : Name) (_ : Syntax) (_ : AttributeKind) :
    AttrM Bool :=
  Prod.fst <$> MetaM.run do
  let info ← getConstInfo thmName

  forallTelescope info.type fun xs b => do
    let fn := b.getArg! 10

    match fn with
    | .lam _ _ b _ =>

      if ¬b.hasLooseBVars then
        logInfo m!"Constant theorem!"
        return true

      match b with
      | (.app (.fvar fId) (.app (.fvar gId) (.bvar 0))) =>
        let .some fArg := xs.findIdx? (· == .fvar fId) | return false
        let .some gArg := xs.findIdx? (· == .fvar gId) | return false

        logInfo m!"Composition theorem with gArg={gArg} and fArg={fArg}"
        return true
      | _ => return false

    | _ => return false

run_meta
  Mathlib.Meta.DataSynth.setCustomTheoremRegister ``HasFDerivAt ``hasFDerivAtRegisterTheorem

end Mathlib.Meta.DataSynth
