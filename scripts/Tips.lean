/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Lean.Expr.Basic
--import Mathlib

/-!
# Find declarations that are not used by other declarations
-/

open Lean Elab Command

elab "#tips" : command => do
  let env ← getEnv
  let mut tips : NameSet := ← env.constants.map₁.foldM (init := {}) fun map n _ => do
    if ← n.isBlackListed then return map else return map.insert n
  --let mut seen : NameSet := {}
  for (_declName, cinfo) in env.constants do --.map₁.fold (init := {}) fun map name cinfo =>
    --if !seen.contains declName then
      let csts := cinfo.getUsedConstantsAsSet
      --seen := seen.append csts
      tips := tips.diff csts
  dbg_trace tips.toArray

set_option trace.profiler true
#tips
