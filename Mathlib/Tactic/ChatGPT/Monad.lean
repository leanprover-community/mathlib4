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
  solutions : List (String × Option Analysis) := []

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

def recordSolution (sol : String) : M IO Unit := do
  let σ ← get
  let a ← analyzeSolution σ.preamble (σ.preambleAnalysis.map (·.env)) sol
  set { σ with solutions := (sol, a) :: σ.solutions }

def latestSolution : M m String := do
  pure <| (← get).solutions.head!.1

def errors : M m (List Lean.Message) := do
  pure <| (← get).solutions.head!.2.toList.bind Analysis.errors

def sorries : M m (List (ContextInfo × MVarId × Position × Position)) := do
  pure <| (← get).solutions.head!.2.toList.bind Analysis.sorries

def done [Alternative m] : M m Unit := do
  guard (← errors).isEmpty
  guard (← sorries).isEmpty

def lastResponse [Monad m] : M m String := do
  pure <| (← get).log.find? (·.role == .assistant) |>.map (·.content) |>.getD ""

def lastCodeBlock [Monad m] : M m CodeBlock := do
  pure <| codeBlocks (← lastResponse) |>.head!

def recordMessage [Monad m] (msg : ChatGPT.Message) : M m Unit :=
  modify fun σ : State => { σ with log := msg :: σ.log }

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
  | _ => throw <| IO.userError s!"Expected a single code block in ChatGPT's response:\n{response}"

def askForAssistance
    (prompt : String) : M IO Unit := do
  let σ ← get
  recordMessage ⟨.user, prompt⟩
  let response ← ChatGPT.sendMessages <| ⟨.user, prompt⟩ :: σ.log
  let some response ← pure response.content | throw <| IO.userError "Response did not contain content"
  recordMessage ⟨.assistant, response⟩
  recordSolution (← getCodeBlock response).body

def discussDeclContaining {m : Type → Type} [Monad m] [MonadLiftT IO m] [MonadLiftT CoreM m]
    (stx : Syntax) (preEdit : String → String) (driver : M m α) : m (String × α) := do
  let (preamble, decl) ← getSourceUpTo stx
  let preambleAnalysis := none
  let editedDecl := preEdit decl
  let analysis ← liftM <| analyzeSolution preamble (preambleAnalysis.map (·.env)) editedDecl
  StateT.run' (do let a ← driver; pure (← latestSolution, a))
    ⟨preamble, preambleAnalysis, [], [(editedDecl, analysis)]⟩

-- Weird, why isn't this available in core?
instance [MonadLift m n] : MonadLift (StateT α m) (StateT α n) where
  monadLift := fun f s => f s
