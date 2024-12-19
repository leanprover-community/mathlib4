/-
Copyright (c) 2024 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Util.Paths
import Lean.Elab.Frontend

/-! # `lake exe refactor` command

This command will run a refactoring task over mathlib (or the specified modules) and all their
dependencies. The task itself must be edited into this file (see `runRefactoring` below).

-/

def help : String := "Mathlib4 refactoring tool
Usage: lake exe refactor <MODULE>..

Arguments:
  <MODULE>
    A module path like `Mathlib`. All files transitively reachable from the
    provided module(s) will be checked.

Note that this tool will not work on its own. Edit `runRefactoring` in
`Refactor/Main.lean` to add the refactoring to apply before running this command.
"

open Lean Elab Command Frontend

instance : ToJson String.Pos := ⟨fun p => toJson p.1⟩
instance : FromJson String.Pos := ⟨fun p => String.Pos.mk <$> fromJson? p⟩
deriving instance ToJson for String.Range
deriving instance FromJson for String.Range

structure Edit where
  replacement : String
  range : String.Range
  deriving ToJson, FromJson

def runRefactoring (_cmd : TSyntax `command) : CommandElabM (List Edit) := do
  -- INSERT LEAN CODE HERE
  panic! "no refactoring active, edit Refactor/Main.lean to add one"
  -- let `(command| #align $_ $_) := cmd | return []
  -- let some range := cmd.raw.getRange? | return []
  -- pure [⟨"", range⟩]

open System (FilePath)
variable (srcSearchPath : SearchPath) (pkg : Name) in
partial def visit (mod : Name) :
    StateT (HashMap Name (FilePath × Task (Except IO.Error (Array Edit)))) IO Unit := do
  if !pkg.isPrefixOf mod || (← get).contains mod then return
  let some fileName ← srcSearchPath.findModuleWithExt "lean" mod
      | throw <| .userError s!"{mod} not found"
  let (deps, _, _) ← parseImports (← IO.FS.readFile fileName) (some fileName.1)
  for dep in deps do
    visit dep.module
  let task ← IO.asTask do
    let out ← IO.Process.output {
      cmd := (← IO.appPath).toString
      args := #["--one", mod.toString]
    }
    if out.exitCode ≠ 0 then
      throw <| IO.userError
        s!"failure processing {mod} with exit code {out.exitCode}:\n{out.stderr}"
    let .ok edits := Json.parse out.stdout >>= fromJson?
      | throw <| IO.userError s!"{mod}: parse failure"
    pure edits
  modify fun s => s.insert mod (fileName, task)

/-- The main entry point. See `help` for more information on arguments. -/
unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let srcSearchPath ← initSrcSearchPath
  match args with
  | ["--one", mainModuleName] =>
    let mainModuleName := String.toName mainModuleName
    enableInitializersExecution
    let some fileName ← srcSearchPath.findModuleWithExt "lean" mainModuleName
      | throw <| .userError s!"{mainModuleName} not found"
    let input ← IO.FS.readFile fileName
    let inputCtx := Parser.mkInputContext input fileName.toString
    let (header, parserState, messages) ← Parser.parseHeader inputCtx
    -- allow `env` to be leaked, which would live until the end of the process anyway
    let opts := {}
    let (env, messages) ← processHeader (leakEnv := true) header opts messages inputCtx
    let env := env.setMainModule mainModuleName
    let mut commandState := Command.mkState env messages opts
    commandState := { commandState with infoState.enabled := true }
    let rec processCommands (edits : Array Edit) : FrontendM (Array Edit) := do
      updateCmdPos
      let cmdState ← getCommandState
      let ictx ← getInputContext
      let pstate ← getParserState
      let scope := cmdState.scopes.head!
      let pmctx := {
        env := cmdState.env, options := scope.opts
        currNamespace := scope.currNamespace, openDecls := scope.openDecls }
      let (cmd, ps, messages) := profileit "parsing" scope.opts fun _ =>
        Parser.parseCommand ictx pmctx pstate cmdState.messages
      modify fun s => { s with commands := s.commands.push cmd }
      setParserState ps
      setMessages messages
      let edits ← runCommandElabM do
        let initMsgs ← modifyGet fun st => (st.messages, { st with messages := {} })
        Command.elabCommandTopLevel cmd
        let edits' ← runRefactoring ⟨cmd⟩
        let mut msgs := (← get).messages
        modify ({ · with messages := initMsgs ++ msgs })
        pure <| edits.appendList edits'
      if Parser.isTerminalCommand cmd then return edits
      processCommands edits
    let (edits, _) ← (processCommands #[]).run { inputCtx := inputCtx }
      |>.run { commandState, parserState, cmdPos := parserState.pos }
    IO.println (toJson edits).pretty
  | mods =>
    let mods := if mods.isEmpty then [`Mathlib] else mods.map String.toName
    -- Only submodules of `pkg` will be edited or have info reported on them
    let pkg := mods[0]!.components.head!
    let (_, mods) ← (mods.mapM (visit srcSearchPath pkg)).run {}
    let out ← mods.foldM (init := #[]) fun r _ (file, task) =>
      match task.get with
      | .error e => throw e
      | .ok edits => pure <| if edits.isEmpty then r else r.push (file, edits)
    for (path, edits) in out do
      IO.println s!"writing {edits.size} edits to {path}"
      let text ← IO.FS.readFile path
      let mut pos : String.Pos := 0
      let mut out : String := ""
      for edit in edits.qsort (·.range.start < ·.range.start) do
        if pos ≤ edit.range.start then
          out := out ++ text.extract pos edit.range.start ++ edit.replacement
          pos := edit.range.stop
      out := out ++ text.extract pos text.endPos
      IO.FS.writeFile path out
