/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Tactic.GPT.Lean
import Std.Util.TermUnsafe

open Lean Elab Meta

namespace Mathlib.Tactic.GPT.Sagredo

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
    IO (Environment × List Message × List InfoTree) := do
  let fileName   := fileName.getD "<input>"
  let inputCtx   := Parser.mkInputContext input fileName
  let (parserState, commandState) ← match env? with
  | none => unsafe do
    -- enableInitializersExecution
    let (header, parserState, messages) ← Parser.parseHeader inputCtx
    let (env, messages) ← processHeader header opts messages inputCtx
    pure (parserState, (Command.mkState env messages opts))
  | some env => do
    pure ({ : Parser.ModuleParserState }, Command.mkState env {} opts)
  processCommandsWithInfoTrees inputCtx parserState commandState

/--
Given a token (e.g. a tactic invocation), we read the current source file,
and find the first blank line before that token, and the first blank line after that token.
We then return everything up to the earlier blank line,
along with everything between the two blank lines.

That is, modulo some assumptions about there being blank lines before and after declarations,
we return everything up to the current declaration, and the current declaration.
-/
def getSourceUpTo (s : Syntax) : CoreM (String × String) := do
  let fileMap := (← readThe Core.Context).fileMap
  let ({ line := line, column := _ }, _) := stxRange fileMap s
  let lines := fileMap.source.splitOn "\n"
  let blanks : List Nat := lines.enum.filterMap fun ⟨n, l⟩ =>
    if l.trim = "" then some (n + 1) else none
  let before := blanks.takeWhile (· < line) |>.maximum? |>.getD 0
  let after := blanks.dropWhile (· ≤ line) |>.minimum? |>.getD lines.length
  pure (String.intercalate "\n" <| lines.take before,
    String.intercalate "\n" <| lines.take after |>.drop before)

def getFileName : CoreM String := do
  pure (← readThe Core.Context).fileName
