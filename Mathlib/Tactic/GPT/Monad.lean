import Mathlib.Tactic.GPT.Send

open Lean Meta Elab

namespace Mathlib.Tactic.GPT

structure State : Type where
  log : List Message := []

variable {m : Type → Type} [Monad m]
abbrev M := StateT State

def lastResponse : M m String := do
  pure <| (← get).log.find? (·.role == .assistant) |>.map (·.content) |>.getD ""

def recordMessage (msg : Message) : M m Unit :=
  modify fun σ : State => { σ with log := msg :: σ.log }

def getLog : M m (List Message) := do
  pure (← get).log

/--
Send a system message.
Since we don't get a response, there's no need to actually send it yet!
-/
def sendSystemMessage (prompt : String) : M IO Unit := do
  recordMessage ⟨.system, prompt⟩

/--
Send a user message, and return GPT's response.
-/
def sendMessage (prompt : String) : M IO String := do
  recordMessage ⟨.user, prompt⟩
  let some response ← sendMessages (← getLog).reverse <&> Response.content |
    throw <| IO.userError "Response did not contain content"
  recordMessage ⟨.assistant, response⟩
  pure response
