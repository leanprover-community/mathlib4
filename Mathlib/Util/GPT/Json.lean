/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.Data.Json

/-!
# OpenAI JSON messages.
-/

open Lean (ToJson FromJson Json fromJson?)

namespace GPT

/-- A GPT role,
either `.system` for system messages, `.user` for queries, or `.assistant` for responses. -/
inductive Role
| system | assistant | user
deriving ToJson, FromJson, BEq

instance : ToString Role where
  toString r := match r with | .system => "system" | .assistant => "assistant" | .user => "user"

/-- A message consists of a role and the contents of the message. -/
structure Message where
  role : Role
  content : String
deriving ToJson, FromJson

/-- A request consists of the desired model and temperature, and a list of messages so far. -/
structure Request where
  model : String := "gpt-4"
  messages : List Message
  temperature : Float := 0.7
  stream : Option Bool := none
deriving ToJson, FromJson

/-- GPT may return multiple choices, if instructed. -/
structure Choice where
  message : Message
  finish_reason : String
  index : Nat
deriving ToJson, FromJson

/-- Usage information about a GPT query. -/
structure Usage where
  prompt_tokens : Nat
  completion_tokens : Nat
  total_tokens : Nat
deriving ToJson, FromJson

/-- Parent of `Response` and `StreamData`, extracting common fields. Not used directly for JSON. -/
structure GenericResponse where
  id : String
  object : String
  created : Nat
  model : String

/-- A response from GPT records some basic information,
along with usage information and a choice of results. -/
structure Response extends GenericResponse where
  usage : Usage
  choices : List Choice
deriving ToJson, FromJson

/-- A 'delta' appearing in streamed data. -/
structure Delta where
  content : String
deriving ToJson, FromJson

/-- A choice node in streamed data.-/
structure StreamChoice where
  delta : Delta
  index : Nat
  finish_reason : Option String
deriving ToJson, FromJson

/-- JSON data received in streaming mode. -/
structure StreamData extends GenericResponse where
  choices : List StreamChoice
deriving ToJson, FromJson

/-- An error message from GPT. -/
structure ErrorMessage where
  message : String
  type : String
  param : Option Nat := none
  code : Option String := none
deriving ToJson, FromJson

instance : ToString ErrorMessage where
  toString e := e.type ++ ": " ++ e.message

/-- Check if the error message is "model_not_found". -/
def ErrorMessage.isModelNotFound (e : ErrorMessage) : Bool := e.code = some "model_not_found"

/-- Check for server errors. -/
def ErrorMessage.isServerError (e : ErrorMessage) : Bool := e.type = "server error"

/-- An error response from GPT. -/
structure Error where
  error : ErrorMessage
deriving ToJson, FromJson

/-- Parse a raw JSON string to a `Response` term,
returning both JSON parsing errors or OpenAI API errors via `Except.error`. -/
def parseResponse (response : String) : Except String (Except ErrorMessage Response) :=
match Json.parse response with
| .ok r => match fromJson? r with
  | .ok r => .ok (.ok r)
  | .error e₁ => match (fromJson? r : Except String Error) with
    | .ok { error := e₂ } => .ok (.error e₂)
    | .error e₂ => .error (e₁ ++ "\n" ++ e₂)
| .error e => .error e

/--
Extract the content of ChatGPT's reply.
This assumes that there is only one `choice`, discarding others.
-/
def Response.content (r : Response) : Option String :=
r.choices.head?.map (·.message.content)

/--
Parse a JSON response from ChatGPT, returning error messages from JSON parsing,
from the OpenAI API, or if the response contains no choice node.
-/
def parse (response : String) : Except String String :=
match parseResponse response with
  | .ok (.ok r) => match r.content with
    | some r' => .ok r'
    | none => .error "ChatGPT response contained no choice nodes."
  | .ok (.error e) => .error (toString e ++ "\n" ++ response)
  | .error e => .error e
