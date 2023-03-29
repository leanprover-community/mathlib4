/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean

-- Taken from Cache.lean: this needs a central home.
/-- Runs a terminal command and retrieves its output -/
def runCmd (cmd : String) (args : Array String) (throwFailure := true) : IO String := do
  let out ← IO.Process.output { cmd := cmd, args := args }
  if out.exitCode != 0 && throwFailure then throw $ IO.userError out.stderr
  else return out.stdout

-- FIXME, customise where the JSON gets written? Or just pass it via stdin?
def jsonFile (payload : String ):= s!"chatgpt.{hash payload}.json"

open System (FilePath)

-- FIXME allow overriding this.
def defaultAPIKeyLocation : IO FilePath := do pure <| (← IO.getEnv "HOME").getD "." / ".openai"

def curl (payload : String) : IO String := do
  -- FIXME give a useful error message if the key isn't found.
  let key ← IO.FS.readFile (← defaultAPIKeyLocation)
  let jsonFile := jsonFile payload
  IO.FS.writeFile jsonFile payload
  let out ← runCmd "curl"
      #["https://api.openai.com/v1/chat/completions", "-H", "Content-Type: application/json",
        "-H", "Authorization: Bearer " ++ key.trim,
        "-d", s!"@{jsonFile}"] false
  IO.FS.removeFile jsonFile
  pure out
