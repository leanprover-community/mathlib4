/-
Copyright (c) 2025 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/

import Lean
import Mathlib.Lean.Meta.RefinedDiscrTree
import Mathlib.Lean.Meta.RefinedDiscrTree.Lookup

import Mathlib.Tactic.DataSynth.Types

open Lean Meta

namespace Mathlib.Meta.DataSynth

/-- Get proof of a theorem. -/
def Theorem.getProof (thm : Theorem) : MetaM Expr := do
  mkConstWithFreshMVarLevels thm.thmName

/-- Get transition theorems applicable to `e`.

For example calling on `e` equal to `Continuous f` might return theorems implying continuity
from linearity over finite dimensional spaces or differentiability. -/
def getTheorems (e : Expr) : DataSynthM (Array Theorem) := do
  let thms := (← get).theorems.theorems
  let cfg := (← read).config
  let (candidates, thms) ←
    withConfig (fun cfg' => { cfg' with iota := cfg.iota, zeta := cfg.zeta }) <|
      thms.getMatch e false true
  modify ({ · with theorems := ⟨thms⟩ })
  return (← MonadExcept.ofExcept candidates).toArray

def getTheoremFromConst (declName : Name) (prio : Nat := eval_prio default) : MetaM Theorem := do
  let info ← getConstInfo declName

  let (_,_,b) ← forallMetaTelescope info.type

  let .some dataSynthDecl ← getDataSynth? b
    | throwError s!"not generalized transformation {← ppExpr b} \n \n {← ppExpr (← whnfR b)}"

  -- replace output arguments with meta variables, we do not want to index them!
  let mut (fn,args) := b.withApp (fun fn args => (fn,args))
  for i in dataSynthDecl.outputArgs do
    let X ← inferType args[i]!
    args := args.set! i (← mkFreshExprMVar X)

  let b := fn.beta args
  let keys ← RefinedDiscrTree.initializeLazyEntryWithEta b

  trace[Meta.Tactic.data_synth]
    "dataSynth: {dataSynthDecl.name}\
   \nthmName: {declName}\
   \nkeys: {keys}"


  let thm : Theorem := {
    dataSynthName := dataSynthDecl.name
    thmName := declName
    keys    := keys
    priority  := prio
  }
  return thm


/-- Extensions for transition or morphism theorems -/
abbrev TheoremsExt := SimpleScopedEnvExtension Theorem Theorems

/-- Environment extension for transition theorems. -/
initialize theoremsExt : TheoremsExt ←
  registerSimpleScopedEnvExtension {
    name     := by exact decl_name%
    initial  := {}
    addEntry := fun d e =>
      {d with theorems := e.keys.foldl (fun thms (key, entry) =>
        RefinedDiscrTree.insert thms key (entry, e)) d.theorems}
  }

def addTheorem (declName : Name) (kind : AttributeKind := .global)
    (prio : Nat := eval_prio default) : MetaM Unit := do
  let thm ← getTheoremFromConst declName prio
  theoremsExt.add thm kind

end Mathlib.Meta.DataSynth
