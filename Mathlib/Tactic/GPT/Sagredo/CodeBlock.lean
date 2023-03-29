import Lean.Data.Json
import Mathlib.Tactic.GPT.String

open Lean

-- Err, this must exist already!
def _root_.List.everySecond : List α → List α
| [] => []
| _ :: [] => []
| _ :: b :: t => b :: t.everySecond

def _root_.String.fence (s : String) := s!"```\n{s}\n```\n"
def _root_.Std.Format.fence (f : Format) := s!"{f}".trim.fence

namespace Mathlib.Tactic.GPT.Sagredo

-- TODO: we could actually check the imports and opens from the environment,
-- and verify that they contain what GPT wants!

structure CodeBlock where
  text : String
  language : Option String := none
  -- FIXME This doesn't care about order, yuck!
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
(text.splitOn "```").everySecond.map fun c =>
  { text := c.trim.stripPrefix "lean" |>.trim,
    language := if c.trim.startsWith "lean" then some "lean" else "" }
