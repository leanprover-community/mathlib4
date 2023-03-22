import Lean
import Mathlib.Data.Option.Defs
import Mathlib.Util.Whatsnew

open Lean Elab Meta

#eval show MetaM _ from do
  let (_, true) ← runFrontend "import Lean\n#eval 2 + 2" {} "" default | failure

#eval show MetaM _ from do
  let (_, true) ← runFrontend "import Lean\n#eval 2 + 2\ndef f := 2" {} "" default | failure

def fghExample :=
"
import Lean
#eval 2 + 2
def f := 2
def g := ⟨f
def h : Nat := by sorry
"

#eval show MetaM _ from do
  let (_, false) ← runFrontend fghExample {} "" default | failure

#eval show MetaM _ from do
  let (_, true) ← runFrontend "import Lean\ndef h : Nat := by sorry" {} "" default | failure

#eval show MetaM _ from do
  let (_, false) ← runFrontend "import Lean\ndef h : Nat := by sorry" { entries := [(`warningAsError, .ofBool true)] } "" default | failure

#eval show MetaM _ from do
  let (_, false) ← runFrontend "import Lean\ndef h : Nat := by sorry" { entries := [(`warningAsError, .ofBool true)] } "" default | failure

-- However we'd like more information than runFrontend returns.
-- In particular we'd like to capture messages, and retain info trees.
-- So let's just roll our own!

/--  Modified from `Lean.Elab.Frontend`. -/
def runFrontend'
    (input : String)
    (opts : Options)
    (fileName : String)
    (mainModuleName : Name)
    (trustLevel : UInt32 := 0)
    : IO (Environment × List Message × List InfoTree) := do
  let inputCtx := Parser.mkInputContext input fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header opts messages inputCtx trustLevel
  let env := env.setMainModule mainModuleName
  let mut commandState := Command.mkState env messages opts
  commandState := { commandState with infoState.enabled := true }
  let s ← IO.processCommands inputCtx parserState commandState
  pure (s.commandState.env, s.commandState.messages.msgs.toList, s.commandState.infoState.trees.toList)

set_option trace.debug true

#eval show MetaM _ from do
  let (env, msgs, _) ← runFrontend' "import Lean\ndef h : Nat := by sorry" {} "" default
  let some ci := env.find? `h | throwError "No declaration h"
  trace[debug] "{← ppExpr ci.type}"
  guard $ toString (← ppExpr ci.type) = "Nat"
  for msg in msgs do
    trace[debug] msg.data


#eval show MetaM _ from do
  let (_, msgs, _) ← runFrontend' "def h : Nat := by\n\ndef g := 7" {} "" default
  for msg in msgs do
    trace[debug] (← msg.toString true)

#eval show MetaM _ from do
  let (_, msgs, trees) ← runFrontend' fghExample {} "" default
  for msg in msgs do
    trace[debug] (← msg.toString true)
  for tree in trees do
    trace[debug] (← tree.format)

namespace Lean.Syntax

-- TODO better implementation
def isSorry (stx : Syntax) : Bool := s!"{stx}" = "(Tactic.tacticSorry \"sorry\")"

end Lean.Syntax

namespace Lean.Elab

def stxRange (fileMap : FileMap) (stx : Syntax) : Position × Position :=
let pos    := stx.getPos?.getD 0
let endPos := stx.getTailPos?.getD pos
(fileMap.toPosition pos, fileMap.toPosition endPos)

end Lean.Elab

namespace Lean.Elab.InfoTree

partial def findAllInfo (t : InfoTree) (ctx : Option ContextInfo) (p : Info → Bool) : List (Info × Option ContextInfo) :=
match t with
| context ctx t => t.findAllInfo ctx p
| node i ts  => (if p i then [(i, ctx)] else []) ++ ts.toList.bind (fun t => t.findAllInfo ctx p)
| _ => []

partial def findSorryNodes (t : InfoTree) : List (TacticInfo × ContextInfo) :=
let infos := t.findAllInfo none fun i => match i with
  | .ofTacticInfo i => i.stx.isSorry
  | _ => false
infos.filterMap fun p => match p with
| (.ofTacticInfo i, some ctx) => (i, ctx)
| _ => none

/--
Finds all appearances of `sorry` in an `InfoTree`, reporting
* the `ContextInfo` at that point,
* the `MVarId` for the goal that was closed by `sorry`,
* and the start and end positions of the `sorry` in the file.
-/
partial def sorries (t : InfoTree) : List (ContextInfo × MVarId × Position × Position) :=
t.findSorryNodes.map fun ⟨i, ctx⟩ =>
  ({ ctx with mctx := i.mctxBefore }, i.goalsBefore.head!, stxRange ctx.fileMap i.stx)

end Lean.Elab.InfoTree

#eval show MetaM _ from do
  let (_, _, trees) ← runFrontend' fghExample {} "" default
  for (ctx, g, pos, _) in trees.bind InfoTree.sorries do
      trace[debug] "The `sorry` at {pos} has goal:\n{← ctx.ppGoals [g]}"

open Command

elab "traceCurrentFile" : command => liftTermElabM do
  trace[debug] (← readThe Core.Context).fileMap.source

traceCurrentFile

elab tk:"line_number" : tactic => do
   let (pos, _) := stxRange (← readThe Core.Context).fileMap tk
   logInfo m!"{pos.line}"

def f : Nat := by
  line_number
  exact 37

#eval String.intercalate " " ("a  b c".splitOn " ") == "a  b c"

/--
Given a token (e.g. a tactic invocation), we read the source file,
and find the first blank line before that token, and the first blank line after that token.
We then return everything up to the earlier blank line,
along with everything between the two blank lines.

That is, modulo some assumptions about there being blank lines before and after declarations,
we return everything up to the current declaration, and the current declaration.
-/
def getSourceUpToToken (s : Syntax) : CoreM (String × String) := do
  let fileMap := (← readThe Core.Context).fileMap
  let ({ line := line, column := _ }, _) := stxRange fileMap s
  let lines := fileMap.source.splitOn "\n"
  let blanks : List Nat := lines.enum.filterMap fun ⟨n, l⟩ => if l.trim = "" then some (n + 1) else none
  let before := blanks.takeWhile (· < line) |>.maximum? |>.getD 0
  let after := blanks.dropWhile (· ≤ line) |>.minimum? |>.getD lines.length
  pure (String.intercalate "\n" <| lines.take before, String.intercalate "\n" <| lines.take after |>.drop before)

elab tk:"trace_decl" : tactic => do
  let (before, decl) ← getSourceUpToToken tk
  trace[debug] before
  trace[debug] "---"
  trace[debug] decl

def g : Nat := by
  trace_decl
  exact 37

def h : Nat := 57

namespace ChatGPT

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

end ChatGPT

open ChatGPT

def exampleRequest (code : String) : Request :=
{ messages := [
    ⟨.system, "You are fixing errors in Lean 4 code. If there is a sorry in the code you should add just one tactic step, and not try to complete the proof."⟩,
    ⟨.user, s!"I'm trying to prove a mathematical statement in the Lean 4 theorem prover. Could you help me with the following code?\n```\n{code.trim}\n```"⟩ ] }

#eval toJson <| exampleRequest "def f : Nat := by sorry"

-- {
--      "model": "gpt-3.5-turbo",
--      "messages": [{"role": "user", "content": "I'm trying to prove a mathematical statement in the Lean 4 theorem prover, and would like your help suggesting the next step. Please note that I'm working in the newer Lean 4, rather than Lean 3, and the syntax is slightly different. It's okay if you want to give an informal explanation of your idea for the next step. Most importantly, I want you to repeat back the code I'm giving you, with one more proof step before the 'sorry'. Don't try to complete the whole proof immediately, because in a moment I'll use the Lean goal state to give you feedback about how your first suggestion works. The proof I have at the moment is:\n```@[simp]\ntheorem getLast_cons {a : α} {l : List α} :\n    ∀ h : l ≠ nil, getLast (a :: l) (cons_ne_nil a l) = getLast l h := by\n  induction l <;> intros\n  sorry```."}],
--      "temperature": 0.7
-- }%

-- Err, this must exist already!
def List.everySecond : List α → List α
| [] => []
| _ :: [] => []
| _ :: b :: t => b :: t.everySecond

def extractResponse (response : String) : Except String String :=
match Json.parse response |>.bind fromJson? with
| .error e => .error e
| .ok (r : Response) => match r.choices.head? with
  | none => .error "ChatGPT response should have contained at least one choice."
  | some c => .ok c.message.content

-- Sometimes ChatGPT uses ```lean to being a code block. Better strip that off.
def codeBlocks (text : String) : List String :=
(text.splitOn "```").everySecond

#eval extractResponse "{\"id\":\"chatcmpl-6wjARYT9RomI5aT9Ihk2mVrBPRLZZ\",\"object\":\"chat.completion\",\"created\":1679454667,\"model\":\"gpt-3.5-turbo-0301\",\"usage\":{\"prompt_tokens\":83,\"completion_tokens\":156,\"total_tokens\":239},\"choices\":[{\"message\":{\"role\":\"assistant\",\"content\":\"Sure! The `sorry` tactic is used as a placeholder for a proof that we don't yet know how to complete. To prove a mathematical statement, we need to give a proof term that represents the proof. \\n\\nIn the case of `def f : Nat := by sorry`, we are defining a constant `f` of type `Nat` and setting its value to `sorry`. Instead, we need to provide a term that computes to a natural number. For example, we could define `f` to be `3` like this:\\n\\n```\\ndef f : Nat := 3\\n```\\n\\nIf you have a specific mathematical statement you're trying to prove, please let me know and I can provide more guidance on how to prove it in Lean 4.\"},\"finish_reason\":\"stop\",\"index\":0}]}"

-- Next two taken from Cache.lean

/-- Runs a terminal command and retrieves its output -/
def runCmd (cmd : String) (args : Array String) (throwFailure := true) : IO String := do
  let out ← IO.Process.output { cmd := cmd, args := args }
  if out.exitCode != 0 && throwFailure then throw $ IO.userError out.stderr
  else return out.stdout

def validateCurl : IO Bool := do
  match (← runCmd "curl" #["--version"]).splitOn " " with
  | "curl" :: v :: _ => match v.splitOn "." with
    | maj :: min :: _ =>
      let (maj, min) := (maj.toNat!, min.toNat!)
      if maj > 7 then return true
      if maj == 7 && min >= 70 then
        if min < 81 then
          IO.println s!"Warning: recommended `curl` version ≥7.81. Found {v}"
        return true
      else
        IO.println s!"`curl` version is required to be ≥7.70. Found {v}. Exiting..."
        return false
    | _ => throw $ IO.userError "Invalidly formatted version of `curl`"
  | _ => throw $ IO.userError "Invalidly formatted response from `curl --version`"

-- curl https://api.openai.com/v1/chat/completions \
--   -H "Content-Type: application/json" \
--   -H "Authorization: Bearer ...api key here..." \
--   -d "@messages.json"%

def jsonFile := "chatgpt.json"
def curlcfg := "curl.cfg"

-- FIXME this is my API key... :-(

def curl (payload : String) : IO String := do
  IO.FS.writeFile jsonFile payload
  let out ← runCmd "curl"
      #["https://api.openai.com/v1/chat/completions", "-H", "Content-Type: application/json", "-H", "Authorization: Bearer <APIKEY>",
        "-d", s!"@{jsonFile}"] false
  -- IO.FS.removeFile jsonFile
  pure out

-- This is commented out, because it is a live request to ChatGPT.
-- But it works, suggesting things like `def f : Nat := 3`.
-- #eval show MetaM _ from do
--   pure <| extractResponse (← curl $ toString <| toJson <| exampleRequest "def f : Nat := by sorry") |>.map codeBlocks

-- I thought we could do this, but it apparently makes instance loops.
-- instance [Functor m] : MonadLift (ChatGPTM m) m where
--   monadLift := fun x => StateT.run' x []

elab tk:"gpt" : tactic => do
  let (_, decl) ← getSourceUpToToken tk
  let decl' := decl.replace "gpt" "sorry" -- haha this will make some fun errors
  let json ← curl $ toString <| toJson <| exampleRequest decl'
  let response := extractResponse json
  let .ok response ← pure response | throwError "Couldn't understand the response from ChatGPT:\n{json}"
  let [block] ← pure <| codeBlocks response | throwError "I was hoping there'd be a single code block in the response:\n{response}"
  logInfoAt tk block

-- example (L M : List α) : (L ++ M).length = (M ++ L).length := by
--   gpt
example (L M : List α) : (L ++ M).length = (M ++ L).length :=
  by rw [List.length_append, List.length_append, Nat.add_comm]

def ChatGPT.sendMessages (messages : List ChatGPT.Message) : IO String := do
  let jsonResponse : String ← curl <| toString <| toJson <| ({ messages := messages } : Request)
  match extractResponse jsonResponse with
  | .error e => throw <| IO.userError e
  | .ok r => pure r

def ChatGPT.send (request : String) : IO String := do
ChatGPT.sendMessages [⟨.user, request⟩]

abbrev ChatGPTM' := StateT (List ChatGPT.Message)

def send (request : String) : ChatGPTM' IO String := do
  let history ← getThe (List ChatGPT.Message)
  let response ← ChatGPT.sendMessages <| ⟨.user, request⟩ :: history
  set <| ⟨.assistant, response⟩ :: ⟨.user, request⟩ :: history
  pure response

structure ChatGPT.State where
  beforeDecl : String
  decl : String
  history : List ChatGPT.Message
  env : Environment
  errors : List Lean.Message
  sorries : List (ContextInfo × MVarId × Position × Position)

abbrev ChatGPTM := StateT ChatGPT.State

def ChatGPT.State.analyze (decl : String) (beforeDecl : String := "") (history : List ChatGPT.Message := []) : IO ChatGPT.State := do
  let (env, errors, trees) ← runFrontend' (beforeDecl ++ "\n\n" ++ decl) {} "" default
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
  set (← State.analyze decl σ.beforeDecl σ.history)

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
  recordMessage ⟨.assistant, response⟩
  let [block] ← pure <| codeBlocks response
    | throw <| IO.userError "Expected a single code block in ChatGPT's response:\nresponse"
  updateDecl block

def discussDeclContaining {m : Type → Type} [Monad m] [MonadLiftT IO m] [MonadLiftT CoreM m]
    (stx : Syntax) (preEdit : String → String) (driver : ChatGPTM m α) : m (String × α) := do
  let (beforeDecl, decl) ← getSourceUpToToken stx
  let σ ← liftM <| ChatGPT.State.analyze (preEdit decl) beforeDecl
  let (a, σ') ← StateT.run driver σ
  pure (σ'.decl, a)

-- Weird, why isn't this available in core?
instance [MonadLift m n] : MonadLift (StateT α m) (StateT α n) where
  monadLift := fun f s => f s

def codeBlock (s : Format) :=
let s := s!"{s}"
s!"```\n{s.trim}\n```\n"

-- TODO this just says what's wrong. It doesn't try to give higher level advice (e.g. backtracking)
def feedback : ChatGPTM IO String := do
  match ← errors with
  | [] => match ← sorries with
    | [] => pure "That's great, it looks like that proof works!"
    | (ctx, g, pos, _) :: _ => do
        -- TODO mention the later sorries?
        let pp ← ctx.ppGoals [g]
        -- TODO the line numbers are off (they're counting in the entire file, not the block we're discussing)
        pure s!"In the proof you just gave me:\n{codeBlock (← lastCodeBlock)} there's still a sorry at line {pos.line}, where the goal is:\n{codeBlock pp}Can you write one more step of the tactic proof there?"
  | errors => do
    let errors ← errors.mapM fun m => m.toString
    pure <| s!"In the proof you just gave me:\n{codeBlock (← lastCodeBlock)} there are some errors:\n" ++
      -- TODO decide which errors matter or deserve emphasise (or helpful advice!)
      -- TODO correct the line numbers, and mention them in prose.
      String.intercalate "\n" errors ++
      "\nPlease fix these, but don't add any more steps to the proof."

def initialPrompt (d : String) :=
s!"I'm trying to write some Lean 4 code, could you help me by writing one more step of the tactic proof, at the sorry?\n{codeBlock d}"

def justOnce : ChatGPTM MetaM String := do
  let prompt := initialPrompt (← readDecl)
  askForAssistance prompt
  try
    done
    pure "success!"
  catch _ =>
    feedback

elab tk:"gpt2" : tactic => do
  let (newDecl, msg) ← discussDeclContaining tk
    (fun decl => decl.replace "gpt2" "sorry") -- haha this will make some fun errors
    justOnce
  logInfoAt tk msg
  logInfoAt tk newDecl

def twice : ChatGPTM MetaM (List String) := do
  let prompt := initialPrompt (← readDecl)
  askForAssistance prompt
  try
    done
    pure ["success!"]
  catch _ =>
    let prompt2 ← feedback
    askForAssistance prompt2
    try
      done
      pure ["success on the second iteration!", prompt2]
    catch _ =>
      pure ["failed", prompt2, ← feedback]

elab tk:"gpt3" : tactic => do
  let (newDecl, msgs) ← discussDeclContaining tk
    (fun decl => decl.replace "gpt3" "sorry") -- haha this will make some fun errors
    twice
  for msg in msgs do
    logInfoAt tk msg
  logInfoAt tk newDecl
