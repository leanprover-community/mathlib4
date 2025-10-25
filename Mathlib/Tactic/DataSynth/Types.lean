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
import Mathlib.Lean.Meta.RefinedDiscrTree

-- import Mathlib.Logic.Equiv.Defs
-- import Mathlib.Tactic.DataSynth.Decl

open Lean Meta

namespace Mathlib.Meta.DataSynth

initialize registerTraceClass `Meta.Tactic.data_synth
initialize registerTraceClass `Meta.Tactic.data_synth.input
initialize registerTraceClass `Meta.Tactic.data_synth.normalize
initialize registerTraceClass `Debug.Meta.Tactic.data_synth

/-- Structure holding information about `data_synth` goal like `HasFDeriv R f ?f'` -/
structure Goal where
  /-- Expression for `fun (x₁ : X₁) ... (xₙ : Xₙ) → P` for some `P : Sort u`
  The goal is to find `x₁`, ..., `xₙ` and proof/term of type `P x₁ ... xₙ` -/
  goal : Expr

  dataSynthName : Name
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

/-- For a `Goal` and its proof extract `Result` from it. -/
def Goal.getResultFrom (g : Goal) (proof : Expr) : MetaM Result := do

  let P ← inferType proof
  let (xs,goal) ← g.mkFreshProofGoal
  unless (← isDefEq goal P) do throwError "invalid result of {← ppExpr P}"
  let xs ← xs.mapM instantiateMVars

  let r : Result := {
    xs := xs
    proof := ← instantiateMVars proof
    goal := g
  }
  return r


/-- Data synth theorem and it discr three key. -/
structure Theorem where
  /-- function property name -/
  dataSynthName : Name
  /-- theorem name -/
  thmName : Name
  /-- discrimination tree keys used to index this theorem -/
  keys : List (RefinedDiscrTree.Key × RefinedDiscrTree.LazyEntry)
  /-- priority -/
  priority : Nat  := eval_prio default
  deriving Inhabited

/-- Structure holding transition or morphism theorems for `fun_prop` tactic. -/
structure Theorems where
  /-- Discrimination tree indexing theorems. -/
  theorems : RefinedDiscrTree Theorem := {}
  deriving Inhabited

def Theorems.add (t : Theorems) (thms : Array Theorem) : MetaM Theorems := do
  return {
    theorems := thms.foldl (init := t.theorems) (fun t thm =>
      thm.keys.foldl (init := t) (fun t (key,entry) => t.insert key (entry,thm)))
  }

/-- Configuration options for `data_synth` tactic. -/
structure DataSynthConfig where
  maxNumSteps := 100
  /-- Normalize result with dsimp. -/
  norm_dsimp := false
  /-- Normalize result with simp. -/
  norm_simp := false

structure Config extends DataSynthConfig, Simp.Config

abbrev Normalize := Expr → SimpM Simp.Result

structure Context where
  config : Config := {}
  disch : Simp.Discharge := fun _ => pure .none
  -- todo: do the same trick as `Simp.MethodsRef`/`Simp.Methods` which would
  --       allow us to define `Normalize` as `Expr → DataSynthM Simp.Result`
  --       i.e. use `DataSynthM` before defining it
  norm  : Normalize := fun e => return { expr := e }

structure State where
  numSteps := 0
  /-- Cache for results. -/
  cache : Std.HashMap Goal Result := {}
  /-- Cache for failed goals. -/
  failedCache : Std.HashSet Goal := {}
  /-- Log failures messages that should be displayed to the user at the end. -/
  msgLog : List MessageData := []
  /-- `RefinedDiscrTree` is lazy, so we store the partially evaluated tree. -/
  theorems : Theorems := default


abbrev DataSynthM := ReaderT Context <| StateRefT State Simp.SimpM

instance : MonadCache Goal Result DataSynthM where
  findCached? g := return (← get).cache[g]?
  cache g r := modify fun s => {s with cache := s.cache.insert g r}

def increaseStepOrThrow : DataSynthM Unit := do
  let steps := (← get).numSteps
  let maxSteps := (← read).config.maxNumSteps
  unless steps < maxSteps do
    throwError s!"Maximum number of steps {maxSteps} reached!"
  modify (fun s => { s with numSteps := steps+1 })


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
