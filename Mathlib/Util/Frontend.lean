/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.Elab.Frontend
import Std.Util.TermUnsafe

open Lean Elab Frontend

namespace Lean.Elab.IO

/--
Results from processing a command.

Contains the `Environment` before and after, the `src : String` and `stx : Syntax` of the command,
and any `Message`s and `InfoTree`s produced while processing.
-/
structure ProcessedCommand where
  src : String
  stx : Syntax
  before : Environment
  after : Environment
  msgs : List Message
  trees : List InfoTree

/--
Process one command, returning a `ProcessedCommand` and
`done : Bool`, indicating whether this was the last command.
-/
def ProcessedCommand.one : FrontendM (ProcessedCommand × Bool) := do
  let s := (← get).commandState
  let before := s.env
  let done ← processCommand
  let stx := (← get).commands.back
  let s' := (← get).commandState
  let after := s'.env
  let msgs := s'.messages.msgs.toList.drop s.messages.msgs.size
  let trees := s'.infoState.trees.toList.drop s.infoState.trees.size
  return ({ src := "", stx, before, after, msgs, trees }, done)

/-- Process all commands in the input. -/
partial def ProcessedCommand.all : FrontendM (List ProcessedCommand) := do
  let (cmd, done) ← ProcessedCommand.one
  if done then
    return [cmd]
  else
    return cmd :: (← all)

def processCommands' (inputCtx : Parser.InputContext) (parserState : Parser.ModuleParserState)
    (commandState : Command.State) : IO (List ProcessedCommand) := do
  let commandState := { commandState with infoState.enabled := true }
  (ProcessedCommand.all.run { inputCtx := inputCtx }).run'
    { commandState := commandState, parserState := parserState, cmdPos := parserState.pos }

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
def processInput (input : String) (env? : Option Environment)
    (opts : Options) (fileName : Option String := none) :
    IO (Environment × List Message × List InfoTree) := unsafe do
  let fileName   := fileName.getD "<input>"
  let inputCtx   := Parser.mkInputContext input fileName
  let (parserState, commandState) ← match env? with
  | none => do
    enableInitializersExecution
    let (header, parserState, messages) ← Parser.parseHeader inputCtx
    let (env, messages) ← processHeader header opts messages inputCtx
    pure (parserState, (Command.mkState env messages opts))
  | some env => do
    pure ({ : Parser.ModuleParserState }, Command.mkState env {} opts)
  processCommandsWithInfoTrees inputCtx parserState commandState
