import Mathlib.Tactic.ChatGPT.Monad

open Lean

namespace Mathlib.Tactic.ChatGPT

def feedback : M IO String := do
  let last := (← latestCodeBlock).markdownBody

  let errors ← (← errors).mapM fun m => do pure <| (← m.toString).splitOn "\n"
  -- We now look at the errors, and given different responses depending on what we see.
  let (unsolvedGoals, otherErrors) := errors.partition fun e => e.head! |>.endsWith "unsolved goals"
  let (_usesSorry, otherErrors) := otherErrors.partition fun e => e.head! |>.endsWith "declaration uses 'sorry'"

  match otherErrors with
  | [] => match unsolvedGoals with
    | [] => match ← sorries with
      | [] => pure "That's great, it looks like that proof works!"
      | (ctx, g, pos, _) :: _ => do
          -- TODO mention the later sorries?
          let pp ← ctx.ppGoals [g]
          pure s!"In the proof you just gave me:\n{last}there's still a sorry at line {pos.line}, where the goal is:\n{pp.fence}Write one more step of the tactic proof, replacing the work `sorry`, that will make further progress on these goals. It's important that you don't just repeat the same code block!"
    | _ =>
        let goal := String.intercalate "\n" (unsolvedGoals.map List.tail).join |>.trim
        pure s!"The proof you just gave me:\n{last}still has unsolved goals:\n{goal.fence}Add another step of the proof, after what you've already written, that will make further progress on these goals. It's important that you don't just repeat the same code block!"
  | _ =>
    pure <| s!"In the proof you just gave me:\n{last}there are some errors:\n" ++
      -- TODO decide which errors matter or deserve emphasise (or helpful advice!)
      -- TODO mention the lines numbers in prose, possibly extracting the relevant span and quoting it
      String.intercalate "\n" otherErrors.join ++
      "\nPlease fix these, but don't add any extra steps to the proof."

def initialPrompt : M IO String := do
  let prompt :=
"I'm a mathematician who is expert in the Lean 4 interactive theorem prover,
and I'd like to you help me fix or complete a proof.

I'm going to show you a declaration in Lean 4, with an incomplete or erroneous proof.
I'd like you to work step by step, and in each successive response you'll write one more step of the proof.
(That is, fixing an error, improving the last step, or adding one more step if there is a `sorry`.)

Please make sure to include a complete declaration containing your suggestion, formatted in a code block.
It's helpful to include some informal explanation of your reasoning before or after the code block.

Let's start with the following proof:\n" ++ (← latestCodeBlock).markdownBody
  match ← sorries with
  | [] => pure prompt
  | (ctx, g, _, _) :: _ => do
      let pp ← ctx.ppGoals [g]
      pure <| prompt ++ s!"\nThe remaining goal is {pp.fence}"

def justOnce : M MetaM String := do
  askForAssistance (← initialPrompt)
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

def twice : M MetaM String := do
  askForAssistance (← initialPrompt)
  try
    done
    pure "success!"
  catch _ =>
    let prompt2 ← feedback
    askForAssistance prompt2
    try
      done
      pure "success on the second iteration!"
    catch _ =>
      pure ("failed!\n" ++ (← feedback))

elab tk:"gpt3" : tactic => do
  let (newDecl, result) ← discussDeclContaining tk
    (fun decl => decl.replace "gpt3" "sorry") -- haha this will make some fun errors
    twice
  logInfoAt tk result
  logInfoAt tk newDecl
