import Mathlib.Tactic.ChatGPT.Monad

open Lean

namespace Mathlib.Tactic.ChatGPT

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
