import Lean
import Mathlib.Tactic.GPT.Sagredo.Frontend

open Lean Elab

namespace REPL

section Json

structure Run where
  env : Option Nat
  body : String
deriving ToJson, FromJson

structure Pos where
  line : Nat
  column : Nat
deriving ToJson, FromJson

inductive Severity
  | info | warning | error
deriving ToJson, FromJson

structure Message where
  pos : Pos
  endPos : Option Pos
  severity : Severity
  data : String
deriving ToJson, FromJson

def Message.of (m : Lean.Message) : IO Message := do pure <|
{ pos := ⟨m.pos.line, m.pos.column⟩,
  endPos := m.endPos.map fun p => ⟨p.line, p.column⟩,
  severity := match m.severity with
  | .information => .info
  | .warning => .warning
  | .error => .warning,
  data := (← m.data.toString) }

structure Sorry where
  pos : Pos
  endPos : Pos
  goal : String
deriving ToJson, FromJson

def Sorry.of (ctx : ContextInfo) (g : MVarId) (pos endPos : Lean.Position) :
    IO Sorry := do pure <|
{ pos := ⟨pos.line, pos.column⟩,
  endPos := ⟨endPos.line, endPos.column⟩,
  goal := s!"{(← ctx.ppGoals [g])}" }

structure Response where
  id : Nat
  messages : List Message
  sorries : List Sorry
deriving ToJson, FromJson

structure Error where
  message : String
deriving ToJson, FromJson

end Json


open Mathlib.Tactic.GPT.Sagredo

structure State where
  environments : Array Environment
  lines : Array Nat

abbrev M (m : Type → Type) := StateT State m

variable [Monad m]
variable [MonadLiftT IO m] [MonadLiftT CoreM m]

def nextId : M m Nat := do pure (← get).environments.size

def run (s : Run) : M IO Response := do
  let env? := s.env.bind ((← get).environments[·]?)
  let (env, messages, trees) ← processInput s.body env? {} ""
  let messages ← messages.mapM fun m => Message.of m
  let sorries ← trees.bind InfoTree.sorries |>.mapM
    fun ⟨ctx, g, pos, endPos⟩ => Sorry.of ctx g pos endPos
  let lines := s.body.splitOn "\n" |>.length
  let id ← nextId
  modify fun s => { environments := s.environments.push env, lines := s.lines.push lines }
  pure ⟨id, messages, sorries⟩

end REPL

open REPL

/-- Get lines from stdin until a blank line is entered. -/
unsafe def getLines : IO String := do
  match (← (← IO.getStdin).getLine) with
  | "\n" => pure "\n"
  | line => pure <| line ++ (← getLines)

/-- Read-eval-print loop for the GPT monad. -/
unsafe def repl : IO Unit :=
  StateT.run' loop ⟨#[], #[]⟩
where loop : M IO Unit := do
  let query ← getLines
  let json := Json.parse query
  match json with
  | .error e => IO.println <| toString <| toJson (⟨e⟩ : Error)
  | .ok j => match fromJson? j with
    | .error e => IO.println <| toString <| toJson (⟨e⟩ : Error)
    | .ok (r : Run) => IO.println <| toString <| toJson (← run r)
  loop

/-- Main executable function, run as `lake env lean --run Mathlib/Util/REPL.lean`. -/
unsafe def main (_ : List String) : IO Unit := do
  repl
