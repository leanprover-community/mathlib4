/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Tactic.GPT.Monad

/-!
# A command line interace for ChatGPT

Relies on an OpenAI key (with access to GPT4) stored in `~/.openai`.
-/

open Mathlib.Tactic.GPT

/-- Get lines from stdin until a blank line is entered. -/
unsafe def getLines : IO String := do
  match (← (← IO.getStdin).getLine) with
  | "\n" => pure "\n"
  | line => pure <| line ++ (← getLines)

/-- Read-eval-print loop for the GPT monad. -/
unsafe def repl : IO Unit :=
  StateT.run' loop ⟨[]⟩
where loop : M IO Unit := do
  IO.println "---"
  let query ← getLines
  IO.println "---"
  IO.println (← sendMessage query)
  loop

/-- Main executable function, run as `lake env lean --run Mathlib/Tactic/GPT/REPL.lean`. -/
unsafe def main (_ : List String) : IO Unit := do
  IO.println "This is GPT4. Enter a blank line at the end of your query."
  repl
