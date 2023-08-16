import Lean

import Std.Tactic.Lint.Basic


open Lean Core Elab IO Meta Term Tactic -- All the monads!


/--
Process some text input, with or without an existing environment.
If there is no existing environment, we parse the input for headers (e.g. import statements),
and create a new environment.
Otherwise, we add to the existing environment.
Returns the resulting environment, along with a list of messages and info trees.

Be aware of https://github.com/leanprover/lean4/issues/2408 when using the frontend.
-/
unsafe def processInput (input : String) (env? : Option Environment)
    (opts : Options) (fileName : Option String := none) :
    IO (Environment × List Message) := do
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
  let s ← IO.processCommands inputCtx parserState commandState <&> Frontend.State.commandState
  pure (s.env, s.messages.msgs.toList)

open System in
-- TODO allow finding Lean 4 sources from the toolchain.
def findLean (mod : Name) : IO FilePath := do
  return FilePath.mk ((← findOLean mod).toString.replace "build/lib/" "") |>.withExtension "lean"

def moduleSource (mod : Name) : IO String := do
  IO.FS.readFile (← findLean mod)

open System
-- Next two declarations borrowed from `runLinter.lean`.
instance : ToExpr FilePath where
  toTypeExpr := mkConst ``FilePath
  toExpr path := mkApp (mkConst ``FilePath.mk) (toExpr path.1)

elab "compileTimeSearchPath%" : term =>
  return toExpr (← searchPathRef.get)

unsafe def main : IO Unit := do
  searchPathRef.set compileTimeSearchPath%
  let (e, _) ← processInput (← moduleSource `Mathlib.Init.ZeroOne) none {}
  IO.println s!"contants.map₁.size: {e.constants.map₁.toList.length}"
  IO.println "contants.map₂:"
  for (n, _) in e.constants.map₂.toList do
    IO.println n

#eval main
