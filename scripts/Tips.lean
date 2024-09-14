/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Lean.Expr.Basic
import ImportGraph.RequiredModules
--import Mathlib

/-!
# Find declarations that are not used by other declarations
-/

open Lean Elab Command

def elimOnce (consts : ConstMap) (tips : NameSet) : NameSet := Id.run do
  let mut tips := tips
  for (_declName, cinfo) in consts do
    let csts := cinfo.getUsedConstantsAsSet
    tips := tips.diff (csts.erase _declName)
  return tips

elab "#tips" : command => do
  let env ← getEnv
  let mut tips : NameSet := ← env.constants.map₁.foldM (init := {}) fun map n _ => do
    if (← n.isBlackListed) || n.getRoot == `Lean then return map else return map.insert n
  dbg_trace "Total declarations: {tips.size}"
  tips := elimOnce env.constants tips
  let withLengths ← liftCoreM do tips.foldM (init := (#[] : Array (Name × Nat))) fun arr n => do
    return arr.push (n, (← n.transitivelyUsedConstants).size)
  dbg_trace "Unused declarations: {tips.size}"
  dbg_trace "With size: {withLengths.qsort (·.2 < ·.2)}"

elab "#direct_deps" : command => do
  let env ← getEnv
  let mut tips : Std.HashMap Name Nat := ← liftCoreM do
    env.constants.map₁.foldM (init := {}) fun map n ci => do
      if (← n.isBlackListed) || n.getRoot == `Lean then return map else return map.insert n ci.getUsedConstantsAsSet.size
  dbg_trace "Total declarations: {tips.size}"
  dbg_trace "With size: {tips.toArray.qsort (·.2 < ·.2)}"

--#tips
#direct_deps
