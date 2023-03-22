import Mathlib.Tactic.ChatGPT.Curl
import Mathlib.Tactic.ChatGPT.JSON

open Lean

namespace Mathlib.Tactic.ChatGPT

def sendMessages (messages : List Message) : IO Response := do
  let jsonResponse : String ← curl <| toString <| toJson <| ({ messages := messages } : Request)
  match parseResponse jsonResponse with
  | .error e => throw <| IO.userError e
  | .ok r => pure r

def send (request : String) : IO String := do
  let r ← sendMessages [⟨.user, request⟩]
  match r.content with
  | none => throw <| IO.userError "ChatGPT response did not contain content."
  | some r => pure r
