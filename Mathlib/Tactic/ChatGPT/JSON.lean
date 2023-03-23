import Lean.Data.Json

/-!
# OpenAI JSON messages.
-/

open Lean

namespace Mathlib.Tactic.ChatGPT

inductive Role
| system | assistant | user
deriving ToJson, FromJson, BEq

instance : ToString Role where
  toString r := match r with | .system => "system" | .assistant => "assistant" | .user => "user"

structure Message where
  role : Role
  content : String
deriving ToJson, FromJson

structure Request where
  model : String := "gpt-4"
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

def _root_.String.stripPrefix (s p : String) :=
if s.startsWith p then
  s.drop p.length
else
  s

def _root_.String.partitionLines (p : String → Bool) (s : String) : String × String :=
s.splitOn "\n" |>.partition p |>.map (String.intercalate "\n") (String.intercalate "\n")

def _root_.String.fence (s : String) := s!"```\n{s}\n```\n"
def _root_.Std.Format.fence (f : Format) := s!"{f}".trim.fence

-- TODO: we could actually check the imports and opens from the environment,
-- and verify that they contain what GPT wants!

structure CodeBlock where
  text : String
  imports := text.partitionLines (·.startsWith "import") |>.1 |>.trim
  opens := text.partitionLines (·.startsWith "import") |>.2 |>.trim
    |>.partitionLines (·.startsWith "open") |>.1 |>.trim
  body := text.partitionLines (·.startsWith "import") |>.2 |>.trim
  |>.partitionLines (·.startsWith "open") |>.2 |>.trim
deriving Inhabited, Repr

namespace CodeBlock

def markdownBody (c : CodeBlock) :=
c.body.fence

end CodeBlock

/-- Process some markdown text, extracting the contents of any code blocks. -/
def codeBlocks (text : String) : List CodeBlock :=
(text.splitOn "```").everySecond.map fun c => { text := c.trim.stripPrefix "lean" |>.trim }

end Mathlib.Tactic.ChatGPT
