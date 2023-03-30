/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

open IO.Process in
/-- Pipe input into stdin of the spawned process, then return output upon completion. -/
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

/-- Retrieve the API key from the OPENAI_API_KEY environment variable. -/
def APIKey : IO String := do match (← IO.getEnv "OPENAI_API_KEY") with
  | none => throw $ IO.userError "No API key found in environment variable OPENAI_API_KEY"
  | some k => pure k

/-- Send a JSON message to the OpenAI chat endpoint, and return the response. -/
def chat (msg : String) : IO String := do
  runCmd "curl"
      #["https://api.openai.com/v1/chat/completions", "-H", "Content-Type: application/json",
        "-H", "Authorization: Bearer " ++ (← APIKey), "--data-binary", "@-"] false msg
