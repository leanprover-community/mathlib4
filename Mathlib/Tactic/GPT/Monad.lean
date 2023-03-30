/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Tactic.GPT.Send

/-!
# State monad for GPT session

Note that the `sagredo` tactic uses a more complicated state instead of this one;
it would be possible to nest them, but I haven't bothered.
-/

namespace Mathlib.Tactic.GPT

/-- The state of a GPT session is a list of messages. We store them most-recent-first. -/
structure State : Type where
  log : List Message := []

variable {m : Type → Type} [Monad m]

/-- The state monad for a GPT session. -/
abbrev M := StateT State

/-- Retrieve the last response from GPT. -/
def lastResponse : M m String := do
  pure <| (← get).log.find? (·.role == .assistant) |>.map (·.content) |>.getD ""

/-- Record a message in the log. -/
def recordMessage (msg : Message) : M m Unit :=
  modify fun σ : State => { σ with log := msg :: σ.log }

/-- Retrieve the message log. -/
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
