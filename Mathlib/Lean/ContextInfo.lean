/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public meta import Mathlib.Lean.Elab.Tactic.Meta
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public import Mathlib.Tactic.Linter.Header  -- shake: keep

/-! # Executing actions using the infotree

This file contains helper functions for running `CoreM`, `MetaM` and tactic actions
in the context of an infotree node.
-/

@[expose] public meta section

open Lean Elab Term Command Linter

namespace Lean.Elab.ContextInfo

variable {α}

/-- Embeds a `CoreM` action in `CommandElabM` by supplying the information stored in `info`.

Copy of `ContextInfo.runCoreM` that makes use of the `CommandElabM` context for:
* logging messages produced by the `CoreM` action,
* metavariable generation,
* auxiliary declaration generation.
-/
def runCoreMWithMessages (info : ContextInfo) (x : CoreM α) : CommandElabM α := do
  -- We assume that this function is used only outside elaboration, mostly in the language server,
  -- and so we can and should provide access to information regardless whether it is exported.
  let env := info.env.setExporting false
  let ctx ← read
  /-
    We must execute `x` using the `ngen` stored in `info`. Otherwise, we may create `MVarId`s and
    `FVarId`s that have been used in `lctx` and `info.mctx`.
    Similarly, we need to pass in a `namePrefix` because otherwise we can't create auxiliary
    definitions.
  -/
  let (x, newState) ←
    (withOptions (fun _ => info.options) x).toIO
      { currNamespace := info.currNamespace, openDecls := info.openDecls
        fileName := ctx.fileName, fileMap := ctx.fileMap }
      { env, ngen := info.ngen, auxDeclNGen := { namePrefix := info.parentDecl?.getD .anonymous } }
  -- Migrate logs back to the main context.
  modify fun state => { state with
    messages := state.messages ++ newState.messages,
    traceState.traces := state.traceState.traces ++ newState.traceState.traces }
  return x

/-- Embeds a `MetaM` action in `CommandElabM` by supplying the information stored in `info`.

Copy of `ContextInfo.runMetaM` that makes use of the `CommandElabM` context for:
* message logging (messages produced by the `CoreM` action are migrated back),
* metavariable generation,
* auxiliary declaration generation,
* local instances.
-/
def runMetaMWithMessages (info : ContextInfo) (lctx : LocalContext) (x : MetaM α) : CommandElabM α := do
  (·.1) <$> info.runCoreMWithMessages (Lean.Meta.MetaM.run
      (ctx := { lctx := lctx }) (s := { mctx := info.mctx }) <|
    -- Update the local instances, otherwise typeclass search would fail to see anything in the
    -- local context.
    Meta.withLocalInstances (lctx.decls.toList.filterMap id) <| x)

/-- Run a tactic computation in the context of an infotree node. -/
def runTactic (ctx : ContextInfo) (i : TacticInfo) (goal : MVarId) (x : MVarId → MetaM α) :
    CommandElabM α := do
  if !i.goalsBefore.contains goal then
    panic!"ContextInfo.runTactic: `goal` must be an element of `i.goalsBefore`"
  let mctx := i.mctxBefore
  let lctx := (mctx.decls.find! goal).2
  ctx.runMetaMWithMessages lctx do
    -- Make a fresh metavariable because the original goal is already assigned.
    let type ← goal.getType
    let goal ← Meta.mkFreshExprSyntheticOpaqueMVar type
    x goal.mvarId!

/-- Run tactic code, given by a piece of syntax, in the context of an infotree node.
The optional `MetaM` argument `m` performs postprocessing on the goals produced. -/
def runTacticCode (ctx : ContextInfo) (i : TacticInfo) (goal : MVarId) (code : Syntax)
    (m : Σ α : Type, MVarId → MetaM α := ⟨MVarId, pure⟩) :
    CommandElabM (List m.1) := do
  let termCtx ← liftTermElabM read
  let termState ← liftTermElabM get
  ctx.runTactic i goal fun goal => do
    let newGoals ← Lean.Elab.runTactic' (ctx := termCtx) (s := termState) goal code
    newGoals.mapM m.2

/-- Embeds a `CoreM` action in `CommandElabM`, returning both the result and the InfoTrees produced.

Similar to `runCoreMWithMessages` but also captures InfoTrees for extracting "Try this:" suggestions. -/
def runCoreMCapturingInfoTree (info : ContextInfo) (x : CoreM α) :
    CommandElabM (α × PersistentArray InfoTree) := do
  let env := info.env.setExporting false
  let ctx ← read
  let (result, newState) ←
    (withOptions (fun _ => info.options) x).toIO
      { currNamespace := info.currNamespace, openDecls := info.openDecls
        fileName := ctx.fileName, fileMap := ctx.fileMap }
      { env, ngen := info.ngen, auxDeclNGen := { namePrefix := info.parentDecl?.getD .anonymous } }
  -- Migrate logs back to the main context
  modify fun state => { state with
    messages := state.messages ++ newState.messages,
    traceState.traces := state.traceState.traces ++ newState.traceState.traces }
  return (result, newState.infoState.trees)

/-- Embeds a `MetaM` action in `CommandElabM`, returning both the result and InfoTrees produced. -/
def runMetaMCapturingInfoTree (info : ContextInfo) (lctx : LocalContext) (x : MetaM α) :
    CommandElabM (α × PersistentArray InfoTree) := do
  let (result, trees) ← info.runCoreMCapturingInfoTree (Lean.Meta.MetaM.run
      (ctx := { lctx := lctx }) (s := { mctx := info.mctx }) <|
    Meta.withLocalInstances (lctx.decls.toList.filterMap id) <| x)
  return (result.1, trees)

/-- Run a tactic computation in the context of an infotree node, capturing InfoTrees produced. -/
def runTacticCapturingInfoTree (ctx : ContextInfo) (i : TacticInfo) (goal : MVarId)
    (x : MVarId → MetaM α) : CommandElabM (α × PersistentArray InfoTree) := do
  if !i.goalsBefore.contains goal then
    panic!"ContextInfo.runTacticCapturingInfoTree: `goal` must be an element of `i.goalsBefore`"
  let mctx := i.mctxBefore
  let lctx := (mctx.decls.find! goal).2
  ctx.runMetaMCapturingInfoTree lctx do
    let type ← goal.getType
    let goal ← Meta.mkFreshExprSyntheticOpaqueMVar type
    x goal.mvarId!

/-- Run tactic code in the context of an infotree node, capturing InfoTrees for suggestion extraction.

Returns both the resulting goals and the InfoTrees produced during tactic execution.
Use `collectTryThisSuggestions` from `Mathlib.Lean.Elab.InfoTree` to extract suggestions. -/
def runTacticCodeCapturingInfoTree (ctx : ContextInfo) (i : TacticInfo) (goal : MVarId)
    (code : Syntax) : CommandElabM (List MVarId × PersistentArray InfoTree) := do
  let termCtx ← liftTermElabM read
  let termState ← liftTermElabM get
  ctx.runTacticCapturingInfoTree i goal fun goal => do
    Lean.Elab.runTactic' (ctx := termCtx) (s := termState) goal code

end Lean.Elab.ContextInfo
