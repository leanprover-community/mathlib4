/-
Copyright (c) 2026 Jovan Gerbscheid and Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills, Jovan Gerbscheid
-/
module

public meta import Lean.Elab.InfoTree.Util
public meta import Lean.Elab.Command
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
import Mathlib.Tactic.Linter.Header -- shake: keep

/-!
# `InfoTree` linting framework

This module defines `InfoLinter`s, which have access to `Array`s of `Elab.Info`s that have been
collected through a single efficient traversal of the infotrees and are shared among all
`InfoLinter`s.

To add an `InfoLinter`, use
```
def myInfoLinter : InfoLinter where
  run infos stx := do ...

initialize addInfoLinter myInfoLinter
```
where each `InfoLinter` has a `run` that behaves like an ordinary `Linter`'s `run`, but is provided
with `infos : Infos`.

`Infos` contains the `Array`s of infos collected from the info trees, organized by kind (as well as
the `ContextInfo` seen by the associated info node). Currently, this just includes `TermInfo`s and
`TacticInfo`s, but this may be expanded in the future.

Note that the tree structure among infos is not preserved, but this can likely be recovered from
the syntax if necessary.
-/

public meta section

open Lean Elab Command

namespace Mathlib.Linter

/-- The information that we extract from the info trees and pass to the `InfoLinter`s. -/
structure Infos where
  /-- All of the `TacticInfo` nodes from the info trees. -/
  tacticInfos : Array (ContextInfo × TacticInfo) := #[]
  /-- All of the `TermInfo` nodes from the info trees, indexed by their elaborator name. -/
  termInfos : NameMap (AssocList TermInfo ContextInfo) := {}

/-- A linter that has also been provided with `Infos`, which contains arrays of `Elab.Info`s that
have been collected through a single efficient traversal of the infotrees and then shared among all
`InfoLinter`s. -/
structure InfoLinter where
  /-- The name of the `InfoLinter`. This is by default the declaration name. -/
  name : Name := by exact decl_name%
  /-- `InfoLinter.run` is like `Linter.run`, but also takes in `Infos`, which contains flat arrays
  of `Elab.Info`s collected from the info trees. Generally, `run` should obtain `Elab.Info`s from
  these arrays instead of traversing the info trees itself. -/
  run : Infos → Syntax → CommandElabM Unit

/-- An `IO.Ref` akin to `lintersRef`, used to implement info linters. -/
initialize infoLintersRef : IO.Ref (Array InfoLinter) ← IO.mkRef #[]

/-- Add an `InfoLinter`. Like `addLinter`, this should be used under `initialize`. -/
@[inline] def addInfoLinter (l : InfoLinter) : IO Unit :=
  infoLintersRef.modify fun ls => ls.push l

/-- Efficiently traverses the `InfoTrees` to gather `Elab.Info`s and store them in the appropriate
field of `Infos`. -/
def getInfos : CommandElabM Infos :=
  withTraceNode `Elab.lint.infotree.get (fun _ => return m!"getting info nodes") do
    let trees ← getInfoTrees
    return trees.foldl (init := {}) <| InfoTree.foldInfo fun ctx info infos =>
      match info with
      -- | .ofTacticInfo i =>
      --   { infos with tacticInfos := infos.tacticInfos.push (ctx, i) }
      | .ofTermInfo i =>
        let entries := (infos.termInfos.find? i.elaborator).getD .nil
        { infos with termInfos := infos.termInfos.insert i.elaborator (.cons i ctx entries) }
      | _ => infos

/--
This function "runs" a series of "linter-likes" (for any provided meaning of "run" and
"linter-like") in the same way that core runs linters, handling state backtracking and infotree
collection appropriately. See `Lean.Elab.Command.runLinters` for reference.

Each linter-like is run under a trace node, with trace class given by `traceCls` and message given
by `traceMsg`. The `failureMsgHeader` is prepended (with two newlines) to any exception thrown by
the linter-like.

Unlike `runLinters`, this appends any new messages, infotrees, and code quality metrics to the
final `CommandElabM` state. If running this from inside another (standard) linter, Lean will
collect these from the resulting state. Otherwise, these may be extracted by keeping track of the
number of trees and code quality metrics from before, and comparing to after.
-/
def runLinterLikes {α} (traceCls : Name) (linterLikes : Array α) (run : α → CommandElabM Unit)
    (traceMsg : α → CommandElabM MessageData) (failureMsgHeader : α → MessageData) :
    CommandElabM Unit := do
  let producedInfoTrees ← IO.mkRef ({} : PersistentArray InfoTree)
  let producedCodeQualityEntries ← IO.mkRef (#[] : Array Linter.CodeQualityLogEntry)
  for linter in linterLikes do
    withTraceNode traceCls (fun _ => traceMsg linter) do
      let savedState ← get
      let originalSize := savedState.infoState.trees.size
      try
        run linter
      catch
        | Exception.error ref msg =>
          logException (.error ref m!"{failureMsgHeader linter}\n\n{msg}")
        | ex@(Exception.internal ..) =>
          logException ex
      finally
        /- Capture and record new additions to the infotrees and code quality metrics recorded by
        the linter itself -/
        let newInfoState ← getInfoState
        let newState := Linter.codeQualityLogExt.getState (← get).env
        if newInfoState.enabled then
          producedInfoTrees.modify fun old =>
            (newInfoState.trees.foldl (·.push ·) old (start := originalSize))
        let oldStateSize := (Linter.codeQualityLogExt.getState (env := savedState.env)).size
        producedCodeQualityEntries.modify (· ++ newState.extract oldStateSize)
        -- Pass along messages and traces
        modify fun s => { savedState with messages := s.messages, traceState := s.traceState }
  /- Record the aggregated new infotrees and code quality metrics (produced by the linters) in the
  final command state -/
  let producedInfoTrees ← producedInfoTrees.get
  let producedCodeQualityEntries ← producedCodeQualityEntries.get
  modifyEnv fun env =>
    Linter.codeQualityLogExt.modifyState env (· ++ producedCodeQualityEntries)
  modifyInfoState fun s => { s with trees := s.trees ++ producedInfoTrees }

/-- Runs all infotree linters. -/
def infoLinterRunner : Linter where
  run stx := do
    profileitM Exception "infotree linting" (← getOptions) do
    withTraceNode `Elab.lint.infotree (fun _ => return m!"infotree linting") do
    let infos ← getInfos
    runLinterLikes `Elab.lint.infotree.run (← infoLintersRef.get)
      (·.run infos stx)
      (fun linter => return m!"running infotree linter {.ofConstName linter.name}")
      (fun linter => m!"infotree linter {.ofConstName linter.name} failed:")

initialize addLinter infoLinterRunner

initialize registerTraceClass `Elab.lint.infotree (inherited := true)
initialize registerTraceClass `Elab.lint.infotree.get (inherited := true)
initialize registerTraceClass `Elab.lint.infotree.run (inherited := true)

end Mathlib.Linter
