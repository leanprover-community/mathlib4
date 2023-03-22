import Lean.Data.Json

/-!
# OpenAI JSON messages.
-/

open Lean

namespace Mathlib.Tactic.ChatGPT

inductive Role
| system | assistant | user
deriving ToJson, FromJson, BEq

structure Message where
  role : Role
  content : String
deriving ToJson, FromJson

structure Request where
  model : String := "gpt-3.5-turbo"
  messages : List Message
  temperature : Float := 0.7
deriving ToJson, FromJson

structure Choice where
  message : Message
  finish_reason : String
  index : Nat
deriving ToJson, FromJson

structure Usage where
  prompt_tokens : Nat
  completion_tokens : Nat
  total_tokens : Nat
deriving ToJson, FromJson

structure Response where
  id : String
  object : String
  created : Nat
  model : String
  usage : Usage
  choices : List Choice
deriving ToJson, FromJson

/--
Extract the content of ChatGPT's reply.
This assumes that there is only one `choice`, discarding others.

It also discards all usage information,
so in large scale use it may be better to use `parseResponse` instead.
-/
def Response.content (r : Response) : Option String :=
r.choices.head?.map (·.message.content)

/-- Parse a raw JSON string to a `Response` term. -/
-- FIXME handle error responses
def parseResponse (response : String) : Except String Response :=
Json.parse response |>.bind fromJson?

-- Err, this must exist already!
def _root_.List.everySecond : List α → List α
| [] => []
| _ :: [] => []
| _ :: b :: t => b :: t.everySecond

/-- Process some markdown text, extracting the contents of any code blocks. -/
-- FIXME Sometimes ChatGPT uses ```lean to begin a code block. Better strip that off.
def codeBlocks (text : String) : List String :=
(text.splitOn "```").everySecond.map String.trim

end Mathlib.Tactic.ChatGPT
