/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.Elab.Frontend

open Lean Elab

namespace Lean.Elab.IO

/--
Wrapper for `IO.processCommands` that enables info states, and returns
* the new environment
* messages
* info trees
-/
def processCommandsWithInfoTrees
    (inputCtx : Parser.InputContext) (parserState : Parser.ModuleParserState)
    (commandState : Command.State) : IO (Environment × List Message × List InfoTree) := do
  let commandState := { commandState with infoState.enabled := true }
  let s ← IO.processCommands inputCtx parserState commandState <&> Frontend.State.commandState
  pure (s.env, s.messages.msgs.toList, s.infoState.trees.toList)

/--
Process some text input, with or without an existing environment.
If there is no existing environment, we parse the input for headers (e.g. import statements),
and create a new environment.
Otherwise, we add to the existing environment.
Returns the resulting environment, along with a list of messages and info trees.
-/
unsafe def processInput (input : String) (initializers := false) (env? : Option Environment)
    (opts : Options) (fileName : Option String := none) :
    IO (Environment × List Message × List InfoTree) := do
  let fileName   := fileName.getD "<input>"
  let inputCtx   := Parser.mkInputContext input fileName
  let (parserState, commandState) ← match env? with
  | none => do
    if initializers then enableInitializersExecution
    let (header, parserState, messages) ← Parser.parseHeader inputCtx
    let (env, messages) ← processHeader header opts messages inputCtx
    pure (parserState, (Command.mkState env messages opts))
  | some env => do
    pure ({ : Parser.ModuleParserState }, Command.mkState env {} opts)
  processCommandsWithInfoTrees inputCtx parserState commandState

open System in
def findLean (mod : Name) : IO FilePath := do
  return FilePath.mk ((← findOLean mod).toString.replace "build/lib/" "") |>.withExtension "lean"

/-- Read the source code of the named module. -/
def moduleSource (mod : Name) : IO String := do
  IO.FS.readFile (← findLean mod)

unsafe def compileModule (mod : Name) (initializers := false) :
    IO (Environment × List Message × List InfoTree) := do
  Lean.Elab.IO.processInput (← moduleSource mod) initializers none {}

unsafe def compileModules (mods : List Name) (initializers := false) : IO Unit := do
  for mod in mods do
    let (_, msgs, trees) ← compileModule mod initializers
    IO.println s!"{mod} has {msgs.length} messages and {trees.length} info trees"
    for m in msgs do IO.println (← m.toString)

unsafe def main (args : List String) : IO UInt32 := do
  let initializers := (← IO.getEnv "INITIALIZERS").isSome
  compileModules (args.map String.toName) initializers
  return 0

#eval compileModules ["Mathlib"] (initializers := false)
-- Mathlib has 0 messages and 1 info trees

#eval compileModules ["Mathlib", "Mathlib"] (initializers := false)
-- Mathlib has 0 messages and 1 info trees
-- Mathlib has 0 messages and 1 info trees

#eval compileModules ["Mathlib"] (initializers := true)
-- Mathlib has 0 messages and 1 info trees

#eval compileModules ["Mathlib"] (initializers := true)
-- Lean server printed an error: PANIC at Lean.PersistentHashMap.find! Lean.Data.PersistentHashMap:160:14: key is not in the map
-- Mathlib has 1 messages and 1 info trees
-- <input>:1:0: error: invalid option declaration 'linter.uppercaseLean3', option already exists
