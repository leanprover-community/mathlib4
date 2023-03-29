/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Tactic.GPT.Monad

open Mathlib.Tactic.GPT

unsafe def getLines : IO String := do
  match (← (← IO.getStdin).getLine) with
  | "\n" => pure "\n"
  | line => pure <| line ++ (← getLines)

unsafe def repl' : M IO Unit := do
  IO.println "---"
  let query ← getLines
  IO.println "---"
  IO.println (← sendMessage query)
  repl'

unsafe def repl : IO Unit :=
  StateT.run' repl' ⟨[]⟩

unsafe def main (_ : List String) : IO Unit := repl
