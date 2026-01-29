-- import Lean.Elab.Tactic.Conv
import Mathlib.Tactic.DataSynth.Core
import Mathlib.Tactic.FunProp.Elab
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
def elabNormalizer (stx? : Option (TSyntax ``convSeq)) : Normalize := fun e => do
  match stx? with
  | .none => return { expr := e }
  | .some stx =>
    let (r,_) ← (elabConvRewrite (← `(conv| ($stx))) e).run {} {}
    return r

open Parser.Tactic.Conv in
syntax normalizer :=
  atomic(" (" patternIgnore(&"normalizer" <|> &"norm")) " := " withoutPosition(convSeq) ")"

open Parser.Tactic Conv in
syntax (name:=data_synth_tac)
  "data_synth" optConfig (discharger)? (normalizer)? ("[" term,* "]")? : tactic

inductive ArgResult
  | simpThm (s : Array SimpTheorem)
  | dataSynthThm (s : DataSynth.Theorem)
  | discharger (f : Simp.Discharge)
  | normalizer (f : DataSynth.Normalize)
  -- todo: support pre and post
  | simproc (decl : Name)

open Lean Elab Term Mathlib.Meta.DataSynth Qq
unsafe def elabArgImpl (arg : Term) : TermElabM ArgResult := do
  let x ← elabTerm arg none
  let type ← inferType x

  -- is an identifier
  if Syntax.isIdent arg then
    let (declName,_) := x.getAppFnArgs

    let (_,_,b) ← forallMetaTelescope type

    -- simp theorem
    if b.isEq then
      let thm ← mkSimpTheoremFromConst declName
      return .simpThm thm

    -- data_synth theorem
    if (← getDataSynth? b).isSome then
      let thm ← DataSynth.getTheoremFromConst declName
      return .dataSynthThm thm

    if (← isDefEq type q(Simp.Simproc)) then
      return .simproc declName

  -- discharger
  if (← isDefEq type q(Simp.Discharge)) then
    let disch : Simp.Discharge ← Meta.evalExpr Simp.Discharge q(Simp.Discharge) x
    return .discharger disch

  -- normalizer
  if (← isDefEq type q(Normalize)) then
    let norm : Normalize ← Meta.evalExpr Normalize q(Normalize) x
    return .normalizer norm

  throwErrorAt arg m!"Unrecognized argument type! \
    It has to be theorem name, discharger, normalizer or simproc."

@[implemented_by elabArgImpl]
opaque elabArg (arg : Term) : TermElabM ArgResult

structure ArgsResult where
  simpThms : SimpTheoremsArray := #[]
  dataSynthThms : Array Theorem := #[]
  discharger : Simp.Discharge := fun _ => return none
  normalizer : Normalize := fun e => return { expr := e}
  -- todo: support pre and post
  simprocs : Simp.SimprocsArray := #[]

def _root_.Lean.Meta.Simp.Discharge.tryNext (f g : Simp.Discharge) : Simp.Discharge := fun e => do
  match ← f e with
  | some prf => return prf
  | none => g e

@[always_inline]
def andThen (f g : Normalize) : Normalize := fun e => do
  (← f e).mkEqTrans (← g e)

instance : AndThen Normalize := ⟨fun x y => andThen x (y ())⟩

def elabArgs (args : Option (Syntax.TSepArray `term ",")) : TermElabM ArgsResult := do
  let args := args.getD ⟨#[]⟩ |>.getElems
  let mut r : ArgsResult := {}
  for arg in args do
    match ← elabArg arg with
    | .simpThm _ =>
      throwErrorAt arg "Currently simp theorems are not supported!"
    | .dataSynthThm s =>
      r := { r with dataSynthThms := r.dataSynthThms.push s }
    | .discharger f =>
      r := { r with discharger := r.discharger.tryNext f }
    | .normalizer f =>
      r := { r with normalizer := r.normalizer >> f }
    | .simproc _ =>
      throwErrorAt arg "Currently simprocs are not supported!"
  return r

@[tactic data_synth_tac] unsafe def dataSynthTactic : Tactic
| `(tactic| data_synth $cfg:optConfig $[$disch?]? $[(norm := $norm)]? $[[$args:term,*]]?) => do
  let m ← getMainGoal
  m.withContext do
  let e ← m.getType

  let cfg ← elabDataSynthConfig cfg

  let some g ← isDataSynthGoal? e
    | throwError "{e} is not `data_synth` goal"

  let args ← elabArgs args

  let ctx : Context := {
    config := cfg
    norm := elabNormalizer norm >> args.normalizer
  }
  let thms := theoremsExt.getState (← getEnv)
  let stateRef : IO.Ref DataSynth.State ← IO.mkRef { theorems:= ← thms.add args.dataSynthThms }

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
