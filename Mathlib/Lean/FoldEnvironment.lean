/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Lean.Meta.Basic
public import Mathlib.Init

/-!
# Folding through the environment efficiently

This file defines `foldImportedDecls`, a function for efficiently folding through the environment.
It splits the environment into parts, each of which is folded over in a separate thread.

We also provide `foldCurrFileDecls` which loops through the declarations of the current module,
without any parallelism.
-/

variable {α : Type}

open Lean Meta

namespace Lean.Meta

/-- An `IO.Ref` that keeps track of any errors that could have been thrown by `act`
when folding over the constants in the environment. -/
public abbrev FoldDeclErrorRef := IO.Ref (List MessageData)

/-- Run `act env name constInfo`, catching potential errors. -/
@[inline]
def visitConst (modName : Name) (errorRef : FoldDeclErrorRef)
    (act : α → Name → ConstantInfo → MetaM α)
    (a : α) (name : Name) (constInfo : ConstantInfo) : MetaM α := do
  try
    act a name constInfo
  catch e =>
    let msg := m!"Processing failure with {name} in {modName}:\n  {e.toMessageData}"
    errorRef.modify (msg :: ·)
    return a

/-- Loop through all constants in modules with module index from `start` to `stop - 1`. -/
@[specialize]
def foldModules (ngen : NameGenerator) (errorRef : FoldDeclErrorRef)
    (env : Environment) (init : α) (act : α → Name → ConstantInfo → MetaM α)
    (mctx : Meta.Context) (cctx : Core.Context)
    (start stop : Nat) : EIO Exception α := do
  let cctx := { cctx with initHeartbeats := ← IO.getNumHeartbeats }
  let go : MetaM α := do
    let mut a := init
    for i in start...stop do
      Core.checkInterrupted
      let modName := env.header.moduleNames[i]!
      let { constNames, constants, .. } := env.header.moduleData[i]!
      for h : i in *...constNames.size do
        let name := constNames[i]
        let constInfo := constants[i]!
        a ← visitConst modName errorRef act a name constInfo
    return a
  go.run' mctx {} |>.run' cctx { env, ngen }

/-- Fold through all imported constants using `act`.
This uses parallelism, with each thread independently folding over a subset of modules.
The array of tasks is returned, so this function typically returns before all tasks have finished.
The results can then be combined using `Array.foldl`. -/
@[specialize]
public def foldImportedDecls (init : α) (cfg : Config)
    (act : α → Name → ConstantInfo → MetaM α) (constantsPerTask : Nat := 5000) :
    CoreM (Array (Task (Except Exception α)) × FoldDeclErrorRef) := do
  let env ← getEnv
  let numModules := env.header.moduleData.size
  let mctx := { keyedConfig := cfg.toConfigWithKey }
  let cctx ← read
  let errorRef ← IO.mkRef {}
  let mut tasks := #[]
  let mut start := 0
  let mut count := 0
  for h : idx in *...numModules do
    count := count + env.header.moduleData[idx].constants.size
    if count > constantsPerTask then
      let (childNGen, parentNGen) := (← getNGen).mkChild
      setNGen parentNGen
      let t ← (foldModules childNGen errorRef env init act mctx cctx start (idx + 1)).asTask
      tasks := tasks.push t
      count := 0
      start := idx + 1
  if start < numModules then
    let (childNGen, parentNGen) := (← getNGen).mkChild
    setNGen parentNGen
    let t ← (foldModules childNGen errorRef env init act mctx cctx start numModules).asTask
    tasks := tasks.push t
  return (tasks, errorRef)

/-- Fold through all constants of the current file using `act`. -/
@[specialize]
public def foldCurrFileDecls (init : α) (cfg : Config)
    (act : α → Name → ConstantInfo → MetaM α) : CoreM (α × FoldDeclErrorRef) := do
  let env ← getEnv
  let modName := env.header.mainModule
  let errorRef ← IO.mkRef {}
  let (childNGen, parentNGen) := (← getNGen).mkChild
  setNGen parentNGen
  let go : MetaM α := env.constants.map₂.foldlM (visitConst modName errorRef act) init
  let result ← go.run' { keyedConfig := cfg.toConfigWithKey } {}
    |>.run' (← read) { env, ngen := childNGen }
  return (result, errorRef)

end Lean.Meta
