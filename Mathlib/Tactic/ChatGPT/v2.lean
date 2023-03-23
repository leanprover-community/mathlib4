import Mathlib.Tactic.ChatGPT.Monad

open Lean

namespace Mathlib.Tactic.ChatGPT

def feedback : M IO String := do
  let last := (← lastCodeBlock).markdownBody

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
          pure s!"In the proof you just gave me:\n{last}there's still a sorry at line {pos.line}, where the goal is:\n{pp.fence}Can you write one more step of the tactic proof there?"
    | _ =>
        let goal := String.intercalate "\n" (unsolvedGoals.map List.tail).join |>.trim
        pure s!"The proof you just gave me:\n{last}looks good, but there are still unsolved goals:\n{goal.fence}"
  | _ =>
    pure <| s!"In the proof you just gave me:\n{last}there are some errors:\n" ++
      -- TODO decide which errors matter or deserve emphasise (or helpful advice!)
      -- TODO mention the lines numbers in prose, possibly extracting the relevant span and quoting it
      String.intercalate "\n" otherErrors.join ++
      "\nPlease fix these, but don't add any more steps to the proof."

def initialPrompt (d : String) :=
s!
"I'm a mathematician who is expert in the Lean 4 interactive theorem prover,
and I'd like to you help me fix or complete a proof.

I want to remind you that we're using Lean 4, not the older Lean 3,
and there have been some syntax changes. In particular:
* Tactics on separate lines should not be separated by commas.
* In the `rw` tactic you must enclose the lemmas in square brackets, even if there is just one.
* Ihe `induction` and `cases` tactic now use a structured format, like pattern matching
  (you can alternatively use `induction' with x y ih`, like in Lean 3).
* Capitalization rules have changed, e.g. we write `List` instead of `list`.
* Indenting is significant.

I'm going to show you a declaration in Lean 4, with an incomplete or erroneous proof.
I'd like you to work step by step, and only try to make one incremental change to the proof.
(That is, fixing an error, improving the last step, or adding one more step if there is a `sorry`.)
I'm going to be automatically compiling your solution in Lean 4
to detect errors and identify further remaining goals,
so you'll have a chance to extend the proof further.

I'd like you to concentrate on just making one change, and trying to be correct and accurate.
Please make sure to include the entire declaration, with your changes, formatted in a code block.
Make sure you don't change the type signature of the declaration itself,
so you're still proving the same thing.

Let's start with the following proof:
{d.fence}"

def justOnce : M MetaM String := do
  let prompt := initialPrompt (← latestSolution)
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

def twice : M MetaM (List String) := do
  let prompt := initialPrompt (← latestSolution)
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
