/-
Copyright (c) 2025 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/

import Lean
-- import SciLean.Tactic.LSimp.Main
-- import SciLean.Tactic.DataSynth.Decl
-- import SciLean.Lean.Meta.Uncurry
-- import SciLean.Lean.Meta.Basic

-- import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.DataSynth.Decl

open Lean Meta

namespace Mathlib.Meta.DataSynth

-- initialize registerTraceClass `Meta.Tactic.data_synth
-- initialize registerTraceClass `Meta.Tactic.data_synth.attr
-- initialize registerTraceClass `Debug.Meta.Tactic.data_synth

/-- Structure holding information about `data_synth` goal like `HasFDeriv R f ?f'` -/
structure Goal where
  /-- Expression for `fun (x₁ : X₁) ... (xₙ : Xₙ) → P` for some `P : Sort u`
  The goal is to find `x₁`, ..., `xₙ` and proof/term of type `P x₁ ... xₙ` -/
  goal : Expr
  /-- Corresponding `data_synth` declaration.  -/
  dataSynthDecl : DataSynthDecl
deriving Hashable, BEq

namespace Goal

/-- Make fresh goal type from `DataSynthGoal` and also return all fresh meta-variables. -/
def mkFreshProofGoal (g : Goal) : MetaM (Array Expr × Expr) := do
  let (xs,_,e) ← lambdaMetaTelescope g.goal
  return (xs,e)

/-- Pretty print of the goal. -/
def pp (g : Goal) : MetaM MessageData := do
  let (_,_,e) ← lambdaMetaTelescope g.goal
  return m!"{e}"

end Goal

/-- Result of data synthesization.

Synthesized data `xs = #[x₁, ..., xₙ]` and proof `proof` of `goal x₁ ... xₙ`. -/
structure Result where
  xs : Array Expr
  proof : Expr
  goal : Goal


namespace Result

def getSolvedGoal (r : Result) : Expr := r.goal.goal.beta r.xs

/-- Given result for `g` and alternative data `xs` that is propositional to the data of the result
`hs`. Proof `hs[i]` can be none if `r.xs[i]` and `xs[i]` are defeq.

Return result with `xs` data. -/
def congr (r : Result) (rs : Array Simp.Result) : MetaM Result := do
  let goal := r.goal.goal

  -- proof that original result is equal to the result with normalized data
  let hgoal ←
      (r.xs.zip rs).foldlM (init:= ← mkEqRefl goal)
        (fun g (x,r) =>
          match r.proof? with
          | some hx => mkCongr g hx
          | none => mkCongrFun g x)
  let xs := rs.map (·.expr)

  -- cast proof of the orignal result to a proof of the new goal
  -- note: originaly we used `mkAppOptM` but replacing it with the following made
  --       `data_synth` four times faster on one test
  let .sort u ← inferType r.getSolvedGoal | throwError "bug"
  let proof := mkAppN (.const ``Eq.mp [u]) #[r.getSolvedGoal, goal.beta xs, hgoal, r.proof]

  return { xs := xs, proof := proof, goal := r.goal }

end Result

-- /-- For a `Goal` and its proof extract `Result` from it. -/
-- def Goal.getResultFrom (g : Goal) (proof : Expr) : MetaM Result := do

--   -- todo: maybe add same sanity checks that we are doing reasonable things

--   let P ← inferType proof
--   let (xs,goal) ← g.mkFreshProofGoal
--   if ¬(← isDefEq goal P) then
--     throwError "invalid result of {← ppExpr P}"
--   let xs ← xs.mapM instantiateMVars

--   let r : Result := {
--     xs := xs
--     proof := ← instantiateMVars proof
--     goal := g
--   }
--   return r

-- what are `data_synth` specific config options?
structure DataSynthConfig where
  maxNumSteps := 100

structure Config extends DataSynthConfig, Simp.Config

structure Context where
  config : Config := {}

structure State where
  numSteps := 0
  /-- Cache for results. -/
  cache : Std.HashMap Goal Result := {}
  /-- Cache for failed goals. -/
  failedCache : Std.HashSet Goal := {}
  /-- Log failures messages that should be displayed to the user at the end. -/
  msgLog : List MessageData := []

abbrev DataSynthM := ReaderT Context <| StateRefT State Simp.SimpM

instance : MonadCache Goal Result DataSynthM where
  findCached? g := return (← get).cache[g]?
  cache g r := modify fun s => {s with cache := s.cache.insert g r}

/-- Run `DataSynthM` in `SimpM` with default context and config.

Useful when running `data_synth` in simproc.

TODO: Add a mechanism to specify `DataSynth.Config` -/
def DataSynthM.runInSimpM {α} (e : DataSynthM α) : SimpM α := do
  let r := e {} (← ST.mkRef {})
  r

/-- Run `DataSynthM` in `MetaM` with default context and config -/
def DataSynthM.runInMetaM {α} (e : DataSynthM α) : MetaM α := do
  e {} (← ST.mkRef {})
       (← Simp.mkDefaultMethods).toMethodsRef
       (← Simp.mkContext)
       (← ST.mkRef {})

/-- Log error message that will displayed to the user at the end. -/
def logError (msg : MessageData) : DataSynthM Unit := do
  modify fun s =>
    {s with msgLog := msg :: s.msgLog }

/-- Forward declaration of main `data_synth` call. -/
initialize dataSynthRef : IO.Ref (Goal → DataSynthM (Option Result))
  ← IO.mkRef (fun _ => return none)

/-- Call `data_synth` tactic on a goal. -/
def dataSynth (g : Goal) : DataSynthM (Option Result) := do (← dataSynthRef.get) g

end Mathlib.Meta.DataSynth
