/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Data.Option.Basic
import Mathlib.Util.GPT.API
import Mathlib.Util.GPT.Json

/-
# Interace for ChatGPT.

We provide two functions
* `sendMessages` which sends a conversation log (including the new query) of `List Message`
  to ChatGPT, retrieving a `Response`.
* `send` which sends a single message (and optional system message), retrieving a `String`.

We'll later add a monadic API that keeps track of the conversation for you.
-/

open Lean

namespace GPT

/-- See https://platform.openai.com/docs/models/model-endpoint-compatibility for
the list of models. -/
inductive Model
| gpt_4 | gpt_4_32k | gpt_35_turbo
deriving BEq, Hashable

instance : ToString Model where
  toString m := match m with
    | .gpt_4 => "gpt-4" | .gpt_4_32k => "gpt-4-32k" | .gpt_35_turbo => "gpt-3.5-turbo"

initialize unavailableModels : IO.Ref (HashSet Model) ← IO.mkRef {}

/-- Mark a model as unavailable. -/
def disableModel (m : Model) : IO Unit := unavailableModels.modify (·.insert m)

structure ChatConfig where
  /-- Model temperature.
  0 is close to deterministic, selecting the most probably token,
  while 1 samples from the predicted probability density on tokens. -/
  temperature : Float := 0.7
  /-- Specify a list of models to use.
  Within each file, if one model fails with an access denied message,
  subsequent attempts will ignore that model. -/
  models : List Model := [.gpt_4, .gpt_35_turbo]
  /-- Retry after server errors. -/
  attempts : Nat := 3
  /-- Log JSON messages to and from https://api.openai.com/ on stdout. -/
  trace : Bool := false

namespace ChatConfig

/-- Select the first model from a list of models, which has not been marked as unavailable. -/
def selectModel (cfg : ChatConfig) : IO (Option Model) := do
  let unavailable ← unavailableModels.get
  return cfg.models.filter (fun m => ¬ unavailable.contains m) |>.head?

end ChatConfig

/-- Send a list of messages representing a chat session to GPT, making retries as needed. -/
def sendMessages (messages : List Message) (cfg : ChatConfig := {}) : IO Response := do
  aux none none (← selectModel) cfg.attempts
where
  selectModel : IO Model := do match ← cfg.selectModel with
    | none => throw <| IO.userError "No available models."
    | some m => return m
  constructMessage (m : Model) : IO String := do
    let request : Request :=
      { model := toString m, temperature := cfg.temperature, messages := messages }
    return toString <| toJson <| request
  aux (error lastJSON : Option String) (model : Model) : Nat → IO Response
  | 0 => throw <| IO.userError <|
      s!"Failed after {cfg.attempts} attempts.\n" ++ error.getD "" ++ "\n" ++ lastJSON.getD ""
  | i+1 => do
    let jsonResponse ← chat (← constructMessage model) cfg.trace
    match parseResponse jsonResponse with
    | .error e =>
        -- We couldn't even parse the response:
        throw <| IO.userError <| e ++ "\n" ++ jsonResponse
    | .ok (.error e) =>
      -- An error message from OpenAI
      if e.isModelNotFound then
        -- Disable this model and try again.
        disableModel model
        aux (toString e) jsonResponse (← selectModel) i
      else if e.isServerError then
        -- Just retry!
        aux (toString e) jsonResponse model i
      else
        throw <| IO.userError <| jsonResponse
    | .ok (.ok r) => pure r

/-- Send a one-off query to GPT. -/
def send (request : String) (systemMessage : Option String := none) (cfg : ChatConfig := {}) :
    IO String := do
  let messages := (systemMessage.map fun s => ⟨.system, s⟩).toList ++ [⟨.user, request⟩]
  match (← sendMessages messages cfg).content with
  | none => throw <| IO.userError "ChatGPT response did not contain content."
  | some r => pure r
