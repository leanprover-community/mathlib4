/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

/-!
# Running external commands.
-/

namespace IO.Process

open System (FilePath)

/--
Pipe `input` into stdin of the spawned process,
then return `(exitCode, stdout, stdErr)` upon completion.
-/
-- TODO We could reduce some code duplication by centralising some functions like this,
-- which are used here, in `cache`, and in https://github.com/leanprover-community/llm.
def runCmdWithInput' (cmd : String) (args : Array String)
    (input : String := "") (throwFailure := true) : IO (UInt32 × String × String) := do
  let child ← spawn
    { cmd := cmd, args := args, stdin := .piped, stdout := .piped, stderr := .piped }
  let (stdin, child) ← child.takeStdin
  stdin.putStr input
  stdin.flush
  let stdout ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let err ← child.stderr.readToEnd
  let exitCode ← child.wait
  if exitCode != 0 && throwFailure then
    throw $ IO.userError err
  else
    let out ← IO.ofExcept stdout.get
    return (exitCode, out, err)

/--
Pipe `input` into stdin of the spawned process,
then return the entire content of stdout as a `String` upon completion.
-/
def runCmdWithInput (cmd : String) (args : Array String)
    (input : String := "") (throwFailure := true) : IO String := do
  return (← runCmdWithInput' cmd args input throwFailure).2.1
