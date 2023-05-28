import Lean
import Lean.Data.Json
import Mathlib.Data.String.Defs

open System IO.FS
open Lean (ToJson FromJson Json fromJson?)

structure MiniF2F where
  id : String
  split : String
  formal_statement : String
  header : String
  informal_stmt : String
  informal_proof : String
deriving FromJson

def main : IO Unit := do
  let h ← Handle.mk (".." / "minif2f-lean4" / "valid.jsonl") .read
  while true do
    let l ← h.getLine
    if l = "" then return
    let .ok j := Json.parse l | throw <| IO.userError "invalid JSON"
    let .ok (p : MiniF2F) := fromJson? j | throw <| IO.userError "invalid JSON"

    IO.FS.writeFile ("test" / "Sagredo" / "MiniF2F" / (p.id ++ ".lean"))
      ("import Mathlib.Tactic.GPT.Sagredo.Widget\n" ++ p.header ++ "\n\n" ++
        -- "/-- " ++ p.informal_stmt ++ "-/\n" ++
        p.formal_statement.stripSuffix "sorry" ++ "by sagredo")

    IO.println l
