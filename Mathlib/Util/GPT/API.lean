/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.Util.Trace

/-!
# Minimal interface to the ChatGPT API, without any parsing.

See `Mathlib.Util.GPT.Json` for parsing.
-/

open System (FilePath)

open IO.Process in
/-- Pipe input into stdin of the spawned process, then return stdout upon completion. -/
-- TODO Put this somewhere central / share with `cache` executable.
def runCmd (cmd : String) (args : Array String) (throwFailure := true) (input : String := "") :
    IO String := do
  let child ← spawn
    { cmd := cmd, args := args, stdin := .piped, stdout := .piped, stderr := .piped }
  let (stdin, child) ← child.takeStdin
  stdin.putStr input
  stdin.flush
  let stdout ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let stderr ← child.stderr.readToEnd
  let exitCode ← child.wait
  if exitCode != 0 && throwFailure then
    throw $ IO.userError stderr
  else
    IO.ofExcept stdout.get

namespace GPT

/-- Retrieve the API key from the OPENAI_API_KEY environment variable. -/
def OPENAI_API_KEY : IO String := do match (← IO.getEnv "OPENAI_API_KEY") with
  | none => throw $ IO.userError "No API key found in environment variable OPENAI_API_KEY"
  | some k => pure k

/-- Send a JSON message to the OpenAI chat endpoint, and return the response. -/
def chat (msg : String) (trace : Bool := false) : IO String := do
  if trace then IO.println msg
  let r ← runCmd "curl"
      #["https://api.openai.com/v1/chat/completions", "-H", "Content-Type: application/json",
        "-H", "Authorization: Bearer " ++ (← OPENAI_API_KEY), "--data-binary", "@-"] false msg
  if trace then IO.print r
  return r
