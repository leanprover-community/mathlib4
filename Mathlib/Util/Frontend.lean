/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.Elab.Frontend
import Std.Util.TermUnsafe

open Lean Elab Frontend

namespace Lean.PersistentArray

def drop [Inhabited α] (t : PersistentArray α) (n : Nat) : List α :=
  List.range (t.size - n) |>.map fun i => t.get! (n + i)

end Lean.PersistentArray

namespace Lean.Elab.IO

/--
Results from processing a command.

Contains the `Environment` before and after,
the `src : Substring` and `stx : Syntax` of the command,
and any `Message`s and `InfoTree`s produced while processing.
-/
structure ProcessedCommand where
  src : Substring
  stx : Syntax
  before : Environment
  after : Environment
  msgs : List Message
  trees : List InfoTree

namespace ProcessedCommand

/--
Process one command, returning a `ProcessedCommand` and
`done : Bool`, indicating whether this was the last command.
-/
def one : FrontendM (ProcessedCommand × Bool) := do
  let s := (← get).commandState
  let beforePos := (← get).cmdPos
  let before := s.env
  let done ← processCommand
  let stx := (← get).commands.back
  let src := ⟨(← read).inputCtx.input, beforePos, (← get).cmdPos⟩ -- FIXME this is incorrect
  let s' := (← get).commandState
  let after := s'.env
  let msgs := s'.messages.msgs.drop s.messages.msgs.size
  let trees := s'.infoState.trees.drop s.infoState.trees.size
  return ({ src, stx, before, after, msgs, trees }, done)

/-- Process all commands in the input. -/
partial def all : FrontendM (List ProcessedCommand) := do
  let (cmd, done) ← ProcessedCommand.one
  if done then
    return [cmd]
  else
    return cmd :: (← all)

/-- Return all new `ConstantInfo`s added during the processed command. -/
def diff (cmd : ProcessedCommand) : List ConstantInfo :=
  cmd.after.constants.map₂.toList.filterMap
    fun (c, i) => if cmd.before.constants.map₂.contains c then none else some i

end ProcessedCommand

/--
Variant of `processCommands` that returns information for each command in the input.
-/
def processCommands' (inputCtx : Parser.InputContext) (parserState : Parser.ModuleParserState)
    (commandState : Command.State) : IO (List ProcessedCommand) := do
  let commandState := { commandState with infoState.enabled := true }
  (ProcessedCommand.all.run { inputCtx := inputCtx }).run'
    { commandState := commandState, parserState := parserState, cmdPos := parserState.pos }

/--
Process some text input, with or without an existing environment.
If there is no existing environment, we parse the input for headers (e.g. import statements),
and create a new environment.
Otherwise, we add to the existing environment.
Returns a list containing data about each processed command.

Be aware of https://github.com/leanprover/lean4/issues/2408 when using the frontend.
-/
def processInput' (input : String) (env? : Option Environment)
    (opts : Options) (fileName : Option String := none) :
    IO (List ProcessedCommand) := unsafe do
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
  processCommands' inputCtx parserState commandState

/--
Wrapper for `IO.processCommands` that returns
* the new environment
* messages
-/
def processCommandsWithMessages
    (inputCtx : Parser.InputContext) (parserState : Parser.ModuleParserState)
    (commandState : Command.State) : IO (Environment × List Message) := do
  let s ← IO.processCommands inputCtx parserState commandState <&> Frontend.State.commandState
  pure (s.env, s.messages.msgs.toList)

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

Be aware of https://github.com/leanprover/lean4/issues/2408 when using the frontend.
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

open System

-- TODO allow finding Lean 4 sources from the toolchain.
def findLean (mod : Name) : IO FilePath := do
  return FilePath.mk ((← findOLean mod).toString.replace "build/lib/" "") |>.withExtension "lean"

/-- Implementation of `moduleSource`, which is the cached version of this function. -/
def moduleSource' (mod : Name) : IO String := do
  IO.FS.readFile (← findLean mod)

initialize sourceCache : IO.Ref <| HashMap Name String ←
  IO.mkRef .empty

/-- Read the source code of the named module. The results are cached. -/
def moduleSource (mod : Name) : IO String := do
  let m ← sourceCache.get
  match m.find? mod with
  | some r => return r
  | none => do
    let v ← moduleSource' mod
    sourceCache.set (m.insert mod v)
    return v

-- Building a cache is a bit ridiculous when
-- https://github.com/leanprover/lean4/issues/2408
-- prevents compiling multiple modules at all.
-- However, it does avoid error messages from attempting to recompile the same
-- module twice.

/-- Implementation of `compileModule`, which is the cached version of this function. -/
def compileModule' (mod : Name) : IO (List ProcessedCommand) := do
  Lean.Elab.IO.processInput' (← moduleSource mod) none {}

initialize compilationCache : IO.Ref <| HashMap Name (List ProcessedCommand) ←
  IO.mkRef .empty

/--
Compile the source file for the named module, returning the
resulting environment, any generated messages, and all info trees.

The results are cached.
-/
def compileModule (mod : Name) : IO (List ProcessedCommand) := do
  let m ← compilationCache.get
  match m.find? mod with
  | some r => return r
  | none => do
    let v ← compileModule' mod
    compilationCache.set (m.insert mod v)
    return v

/-- Compile the source file for the named module, returning all info trees. -/
def moduleInfoTrees (mod : Name) : IO (List InfoTree) := do
  let steps ← compileModule mod
  return steps.bind (fun c => c.trees)
