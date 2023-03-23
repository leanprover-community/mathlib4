import Mathlib.Tactic.ChatGPT.Frontend
import Mathlib.Tactic.ChatGPT.Send

open Lean Meta Elab

namespace Mathlib.Tactic.ChatGPT

structure Analysis : Type where
  env : Environment
  errors : List Lean.Message
  sorries : List (ContextInfo × MVarId × Position × Position)

def Analysis.subtractLineNumbers (a : Analysis) (n : Nat) : Analysis :=
{ a with
  errors := a.errors.map
    fun e => { e with
      pos := ⟨e.pos.line - n, e.pos.column⟩,
      endPos := e.endPos.map fun p => ⟨p.line - n, p.column⟩ }
  sorries := a.sorries.map
    fun ⟨ctx, g, s, t⟩ => ⟨ctx, g, ⟨s.line - n, s.column⟩, ⟨t.line - n, t.column⟩⟩ }

structure State : Type where
  preamble : String
  preambleAnalysis : Option Analysis := none
  log : List Message := []
  solutions : List (CodeBlock × Option Analysis) := []

variable {m : Type → Type} [Monad m]
abbrev M := StateT State

def _root_.String.count (s : String) (c : Char) : Nat :=
s.foldl (fun n d => if d = c then n + 1 else n) 0

-- FIXME ideally we would be able to use an existing `preambleEnv`
-- and avoid recompiling the whole file from scratch.
def analyzeSolution (preamble : String) (_preambleEnv : Option Environment) (sol : String) :
    IO Analysis := do
  let (env, errors, trees) ← runFrontend (preamble ++ "\n\n" ++ sol) {} "" default
  pure <| Analysis.subtractLineNumbers ⟨env, errors, trees.bind InfoTree.sorries⟩ (preamble.count '\n' + 2)

def recordSolution (sol : CodeBlock) : M IO Unit := do
  let σ ← get
  let a ← analyzeSolution σ.preamble (σ.preambleAnalysis.map (·.env)) sol.body
  set { σ with solutions := (sol, a) :: σ.solutions }

def latestCodeBlock : M m CodeBlock := do
  pure <| (← get).solutions.head!.1

def latestSolution : M m String := do
  pure (← latestCodeBlock).body

def errors : M m (List Lean.Message) := do
  pure <| (← get).solutions.head!.2.toList.bind Analysis.errors

def sorries : M m (List (ContextInfo × MVarId × Position × Position)) := do
  pure <| (← get).solutions.head!.2.toList.bind Analysis.sorries

def isDone : M m Bool := do
  pure <| (← errors).isEmpty && (← sorries).isEmpty

def done [Alternative m] : M m Unit := do
  guard (← isDone)

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

def askForAssistance (prompt : String) : M IO Unit := do
  recordMessage ⟨.user, prompt⟩
  let response ← sendMessages <| (← getLog)
  let some response ← pure response.content | throw <| IO.userError "Response did not contain content"
  recordMessage ⟨.assistant, response⟩
  recordSolution (← getCodeBlock response)

variable [MonadLog m] [AddMessageContext m] [MonadOptions m]

variable [MonadLiftT IO m] [MonadLiftT CoreM m]

def versionNumber := 0

def runAndLog (stx : Syntax) (driver : M m α) : M m (String × α) := do
  let a ← driver

  let logFile := ((← getFileName).stripPrefix ".lean") ++ s!".v{versionNumber}.gpt.log"
  let success := if (← isDone) then "Success" else "Failure"
  let log := (← get).log
  let logContents := success ++ s!": {log.length} messages\n=====\n" ++ (String.intercalate "\n=====\n" <| (← get).log.map fun msg => s!"{msg.role}:\n" ++ msg.content)
  IO.FS.writeFile logFile logContents

  logInfoAt stx "Message log follows:"
  for msg in (← get).log do
    logInfoAt stx (s!"{msg.role}:\n" ++ msg.content)
  pure (← latestSolution, a)

def discussDeclContaining (stx : Syntax) (preEdit : String → String) (driver : M m α) :
    m (String × α) := do
  let (preamble, decl) ← getSourceUpTo stx
  let preambleAnalysis := none
  let editedDecl := preEdit decl
  let analysis ← liftM <| analyzeSolution preamble (preambleAnalysis.map (·.env)) editedDecl
  StateT.run' (runAndLog stx driver)
    ⟨preamble, preambleAnalysis, [], [({ text := editedDecl }, analysis)]⟩

-- Weird, why isn't this available in core?
instance [MonadLift m n] : MonadLift (StateT α m) (StateT α n) where
  monadLift := fun f s => f s
