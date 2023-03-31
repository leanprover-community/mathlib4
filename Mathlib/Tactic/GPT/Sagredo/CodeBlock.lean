/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.Data.Json
import Mathlib.Tactic.GPT.String
import Mathlib.Data.List.Basic

open Lean

/-- Filter list elements according to a predicate on the index. -/
def List.filterIdx (p : Nat → Bool) : List α → List α :=
  aux 0
where aux (n : Nat) (L : List α) := match L with
| [] => []
| h :: t => if p n then h :: aux (n + 1) t else aux (n + 1) t

def _root_.String.fence (s : String) := "```\n" ++ s ++ "\n```\n"
def _root_.Std.Format.fence (f : Format) := toString f |>.trim.fence

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
(text.splitOn "```").filterIdx (· % 2 = 1) |>.map fun c =>
  { text := c.trim.stripPrefix "lean" |>.trim,
    language := if c.trim.startsWith "lean" then some "lean" else "" }
