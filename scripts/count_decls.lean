/-
Copyright (c) 2024 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Damiano Testa
-/
import Mathlib

/-!
# `count_decls` -- a tally of declarations in `Mathlib`

This file is used by the `Periodic reports` script to generate a tally of declarations
in `Mathlib`.

Source: https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Metamathematics.3A.20Theorems.20by.20Domain.20Areas/near/374090639
-/

namespace PeriodicReports
open Lean Elab Meta

/-- A structure to tally declaration types:
* `thms` are theorems;
* `typesPreds` are types/predicates;
* `other` is everything else.
-/
structure Tally where
  thms : Nat := 0
  typesPreds : Nat := 0
  other : Nat := 0
  deriving Repr

/-- `MathlibModIdxs env` returns the `ModuleIdx`s corresponding to `Mathlib` files
that are in the provided environment. -/
def MathlibModIdxs (env : Environment) : IO (HashSet Nat) := do
  let mut modIdx : HashSet Nat := .empty
  for imp in ← IO.FS.lines "Mathlib.lean" do
    if let some nm := env.getModuleIdx? (imp.drop 7).toName then
      modIdx := modIdx.insert nm
  return modIdx

/-- extend a `Tally` by the ConstantInfo `c`.  It is written to work with `Lean.SMap.foldM`,
hence the unused `Name`. -/
def updateTally (mods : HashSet Nat) (env : Environment) (s : Tally) (_ : Name) (c : ConstantInfo) :
    MetaM Tally := do
  let mod := env.getModuleIdxFor? c.name
  if !mods.contains (mod.getD default) then return s else
  if c.isUnsafe then return s else
  let typ := c.type
  if (← isProp typ) then
    return {s with thms := s.thms + 1}
  else
    if ← forallTelescopeReducing c.type fun _ e => return e.isSort then
      return {s with typesPreds := s.typesPreds + 1}
    else
      return {s with other := s.other + 1}

/-- extends a `Tally` all the ConstantInfos in the environment. -/
def mkTally (s : Tally) : MetaM Tally := do
  let env ← getEnv
  let maths ← MathlibModIdxs env
  let consts := env.constants
  consts.foldM (updateTally maths env) s

/-- `count_decls` prints a tally of theorems, types/predicates and everything else in `Mathlib`. -/
elab "count_decls" : command => do
  let (s, _) := ← Command.liftCoreM do Meta.MetaM.run do (mkTally {})
  logInfo s!"Theorems {s.thms}\nTypes/predicates {s.typesPreds}\nOther {s.other}"

--count_decls

end PeriodicReports
