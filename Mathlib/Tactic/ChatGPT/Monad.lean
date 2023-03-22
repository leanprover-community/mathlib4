import Mathlib.Tactic.ChatGPT.Frontend
import Mathlib.Tactic.ChatGPT.Send

open Lean Meta Elab

namespace Mathlib.Tactic.ChatGPT

structure State : Type where
  beforeDecl : String
  decl : String
  history : List ChatGPT.Message
  env : Environment
  errors : List Lean.Message
  sorries : List (ContextInfo × MVarId × Position × Position)

abbrev ChatGPTM := StateT State

def analyze (decl : String) (beforeDecl : String := "") (history : List Message := []) : IO State := do
  let (env, errors, trees) ← runFrontend (beforeDecl ++ "\n\n" ++ decl) {} "" default
  let sorries := trees.bind InfoTree.sorries
  pure <|
  { beforeDecl := beforeDecl,
    decl := decl,
    history := history,
    env := env,
    errors := errors,
    sorries := sorries }

def updateDecl (decl : String) : ChatGPTM IO Unit := do
  let σ ← get
  set (← analyze decl σ.beforeDecl σ.history)

def readDecl [Monad m] : ChatGPTM m String := do
  pure (← get).decl

def errors [Monad m] : ChatGPTM m (List Lean.Message) := do
  pure (← get).errors

def sorries [Monad m] : ChatGPTM m (List (ContextInfo × MVarId × Position × Position)) := do
  pure (← get).sorries

def done [Monad m] [Alternative m] : ChatGPTM m Unit := do
  let σ ← get
  guard σ.errors.isEmpty
  guard σ.sorries.isEmpty

def lastResponse [Monad m] : ChatGPTM m String := do
  pure <| (← get).history.find? (·.role == .assistant) |>.map (·.content) |>.getD ""

def lastCodeBlock [Monad m] : ChatGPTM m String := do
  pure <| codeBlocks (← lastResponse) |>.head!

def recordMessage [Monad m] (msg : ChatGPT.Message) : ChatGPTM m Unit :=
  modify fun σ : ChatGPT.State => { σ with history := msg :: σ.history }

def askForAssistance
    (prompt : String) : ChatGPTM IO Unit := do
  let σ ← get
  recordMessage ⟨.user, prompt⟩
  let response ← ChatGPT.sendMessages <| ⟨.user, prompt⟩ :: σ.history
  let some response ← pure response.content | throw <| IO.userError "Response did not contain content"
  recordMessage ⟨.assistant, response⟩
  let [block] ← pure <| codeBlocks response
    | throw <| IO.userError "Expected a single code block in ChatGPT's response:\nresponse"
  updateDecl block

def discussDeclContaining {m : Type → Type} [Monad m] [MonadLiftT IO m] [MonadLiftT CoreM m]
    (stx : Syntax) (preEdit : String → String) (driver : ChatGPTM m α) : m (String × α) := do
  let (beforeDecl, decl) ← getSourceUpTo stx
  let σ ← liftM <| analyze (preEdit decl) beforeDecl
  let (a, σ') ← StateT.run driver σ
  pure (σ'.decl, a)

-- Weird, why isn't this available in core?
instance [MonadLift m n] : MonadLift (StateT α m) (StateT α n) where
  monadLift := fun f s => f s

def codeBlock (s : Format) :=
let s := s!"{s}"
s!"```\n{s.trim}\n```\n"
