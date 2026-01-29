import Lean

import Mathlib.Tactic.DataSynth.Elab
import Mathlib.Tactic.DataSynth.FDeriv.Init
import Mathlib.Tactic.DataSynth.FDeriv.Basic

open Lean Meta Mathlib.Meta DataSynth
simproc_decl fderiv_simproc_at (fderiv _ _ _) := fun e => do

  -- get arguments
  let x := e.appArg!
  let f := e.appFn!.appArg!
  let R := e.getArg! 0

  -- initialize `HasFDerivAt R f ?f' x`
  let hasFDerivAt := ← mkConstWithFreshMVarLevels ``HasFDerivAt
  let (xs,_,_) ← forallMetaTelescope (←inferType hasFDerivAt)
  xs[0]!.mvarId!.assignIfDefEq R
  xs[xs.size-3]!.mvarId!.assignIfDefEq f
  xs[xs.size-1]!.mvarId!.assignIfDefEq x
  let hasFDerivAt := hasFDerivAt.beta xs

  -- create data_synth goal
  let .some g ← isDataSynthGoal? hasFDerivAt | return .continue

  -- prepare data_synth context and state
  let cfg ← Simp.getConfig
  let ctx : DataSynth.Context := {
    config := { cfg with norm_simp := true }
    disch := (← Simp.getMethods).discharge?
  }
  let state : IO.Ref DataSynth.State ←
    IO.mkRef { theorems := theoremsExt.getState (← getEnv) }

  -- call data_synth
  let .some r ← dataSynth g ctx state | return .continue

  -- produce simp result
  let proof ← mkAppM ``HasFDerivAt.fderiv #[r.proof]
  let f' := r.xs[0]!

  return .visit { expr := f', proof? := proof }

open Lean Meta in
simproc_decl fderiv_simproc_any (fderiv _ _) := fun e => do

  let f := e.appArg!
  let .some (E, _) := (← inferType f).arrow? | return .continue

  -- introduce point where to differentiate
  withLocalDecl `x default E fun x => do

    -- bind the free variable `x` to the result
    let fixResult (r : Simp.Result) : MetaM Simp.Result := do
      return { r with
        expr := ← mkLambdaFVars #[x] r.expr
        proof? := ← r.proof?.mapM (fun p => mkLambdaFVars #[x] p >>= (mkAppM ``funext #[·]))
      }

    -- call simproc for `fderiv R f x` and bind the free variable `x`
    match (← fderiv_simproc_at (e.beta #[x])) with
    | .done r => return .done (← fixResult r)
    | .visit r => return .visit (← fixResult r)
    | .continue (some r) => return .continue (some (← fixResult r))
    | .continue none => return .continue

attribute [fderiv_simproc] fderiv_simproc_at fderiv_simproc_any
