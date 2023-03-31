/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Zhangir Azerbayev
-/
import Mathlib.Tactic.GPT.Send
import Mathlib.Tactic.GPT.Monad
import Mathlib.Tactic.GPT.Sagredo.Frontend
import Mathlib.Tactic.GPT.Sagredo.CodeBlock

open Lean Meta Elab

namespace Mathlib.Tactic.GPT.Sagredo

structure Analysis : Type where
  env : Environment
  errors : List Lean.Message
  sorries : List (ContextInfo × MVarId × Position × Position)

def linesBeforeError (block : CodeBlock) (analysis : Analysis) : IO Nat := do
  let errors ← analysis.errors.filterM fun e => do
    let firstLine := (← e.toString).splitOn "\n" |>.head!
    pure <| !firstLine.endsWith "unsolved goals" && !firstLine.endsWith "declaration uses 'sorry'"
  let errorLines : List Nat := errors.map (·.pos.line - 1)
  let sorryLines : List Nat := analysis.sorries.map (·.2.2.1.line - 1)
  let totalLines := block.body.splitOn "\n" |>.length
  pure <| (errorLines ++ sorryLines).foldl min totalLines

structure State extends GPT.State where
  preamble : String
  preambleAnalysis : Analysis
  solutions : List (CodeBlock × Analysis) := []

variable {m : Type → Type} [Monad m]
abbrev M := StateT State

def analyzeCode (env? : Option Environment) (code : String) :
    IO Analysis := do
  let (env, errors, trees) ← processInput code env? {} ""
  pure ⟨env, errors, trees.bind InfoTree.sorries⟩

def recordSolution (sol : CodeBlock) : M IO Unit := do
  let σ ← get
  let a ← analyzeCode σ.preambleAnalysis.env sol.body
  set { σ with solutions := (sol, a) :: σ.solutions }

def latestCodeBlock : M m CodeBlock := do
  match (← get).solutions.head? with
  | none => pure { text := "" }
  | some ⟨c, _⟩ => pure c

def latestSolution : M m String := do
  pure (← latestCodeBlock).body

def errors : M m (List Lean.Message) := do
  pure <| (← get).solutions.head? |>.map (·.2) |>.toList.bind Analysis.errors

def sorries : M m (List (ContextInfo × MVarId × Position × Position)) := do
  pure <| (← get).solutions.head? |>.map (·.2) |>.toList.bind Analysis.sorries

def isDone : M m Bool := do
  pure <| (← errors).isEmpty && (← sorries).isEmpty

/--
Was the longest solution (measured in lines before the first error)
first achieved during the last k steps?
-/
def recentProgress (k : Nat) : M IO Bool := do
  let lines ← (← get).solutions |>.mapM fun ⟨c, a⟩ => linesBeforeError c a
  pure <| lines.drop k |>.all fun a => lines.take k |>.any fun b => b > a

def lastResponse : M m String := do
  pure <| (← get).log.find? (·.role == .assistant) |>.map (·.content) |>.getD ""

def recordMessage (msg : Message) : M m Unit :=
  modify fun σ : State => { σ with log := msg :: σ.log }

def getLog : M m (List Message) := do
  pure (← get).log

def getCodeBlock (response : String) : M IO CodeBlock := do
  match codeBlocks response with
  | [] =>
    -- No code blocks in the response.
    -- Sometimes ChatGPT answers just with the declaration, so check for that.
    if (← latestSolution).take 25 = response.take 25 then
      pure { text := response }
    else
      throw <| IO.userError s!"No code blocks found in ChatGPT's response:\n{response}"
  | [block] => pure block
  | blocks =>
    -- There are multiple code blocks.
    -- This may because ChatGPT is trying to describe the goal to us.
    let sol ← latestSolution
    -- If there's a unique code block with prefix agreeing with the last solution, take that.
    match blocks.filter (fun b => sol.take 25 = b.body.take 25) with
    | [block] => pure block
    -- Otherwise, if there are multiple blocks with langauge `lean`, just take the last one.
    | _ => match blocks.reverse.filter (fun b => b.language = some "lean") with
      | [] => throw <| IO.userError s!"Expected a single code block in ChatGPT's response:\n{response}"
      | block :: _ => pure block

/-- Send a system message. -/
def sendSystemMessage (prompt : String) : M IO Unit := do
  recordMessage ⟨.system, prompt⟩

def askForAssistance (prompt : String) : M IO Unit := do
  recordMessage ⟨.user, prompt⟩
  let response ← sendMessages <| (← getLog).reverse
  let some response ← pure response.content | throw <| IO.userError "Response did not contain content"
  recordMessage ⟨.assistant, response⟩
  recordSolution (← getCodeBlock response)

variable [MonadLog m] [AddMessageContext m] [MonadOptions m]

variable [MonadLiftT IO m] [MonadLiftT CoreM m]

def versionNumber := 0.1

def runAndLog (stx : Syntax) (driver : M m α) : M m (String × α) := do
  let a ← driver

  let logFile := ((← getFileName).stripPrefix ".lean") ++ s!".v{versionNumber}.gpt.log"
  let success := if (← isDone) then "Success" else "Failure"
  let log := (← get).log
  let logContents := success ++ s!": {log.length} messages\n=====\n" ++ (String.intercalate "\n=====\n" <| (← get).log.map fun msg => s!"{msg.role}:\n" ++ msg.content)
  IO.FS.writeFile logFile logContents

  logInfoAt stx "Message log follows:"
  for msg in (← get).log do
    logInfoAt stx m!"{← (← get).solutions |>.mapM fun ⟨c, a⟩ => linesBeforeError c a}"
    logInfoAt stx (s!"{msg.role}:\n" ++ msg.content)
  pure (← latestSolution, a)

def discussDeclContaining (stx : Syntax) (preEdit : String → String) (driver : M m α) :
    m (String × α) := do
  let (preamble, decl) ← getSourceUpTo stx
  let preambleAnalysis ← analyzeCode none preamble
  let editedDecl := preEdit decl
  let analysis ← liftM <| analyzeCode preambleAnalysis.env editedDecl
  StateT.run' (runAndLog stx driver)
    ⟨⟨[]⟩, preamble, preambleAnalysis, [({ text := editedDecl }, analysis)]⟩
