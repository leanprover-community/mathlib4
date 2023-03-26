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
          pure s!"In the proof you just gave me:\n{last}there's still a sorry at line {pos.line}, where the goal is:\n{pp.fence}Write one more step of the tactic proof, replacing the tactic `sorry`, that will make further progress on these goals."
    | _ =>
        let goal := String.intercalate "\n" (unsolvedGoals.map List.tail).join |>.trim
        pure s!"The proof you just gave me:\n{last}still has unsolved goals:\n{goal.fence}Add another step of the proof, after what you've already written, that will make further progress on these goals."
  | _ =>
    pure <| s!"In the proof you just gave me:\n{last}there are some errors:\n" ++
      -- TODO decide which other errors matter or deserve emphasise (or helpful advice!)
      -- TODO mention the lines numbers in prose, possibly extracting the relevant span and quoting it
      String.intercalate "\n" otherErrors.join ++
      "\nPlease fix these, but don't add any extra steps to the proof."

def systemPrompt : String :=
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
I'd like you to work step by step, and in each successive response you'll write one more step of the proof.
(That is, fixing an error, improving the last step, or adding one more step if there is a `sorry`.)

Please make sure to include a complete declaration containing your suggestion, formatted in a code block.
It's helpful to include some informal explanation of your reasoning before or after the code block."

def initialPrompt : M IO String := do
  let prompt := "Let's start with the following proof:\n" ++ (← latestCodeBlock).markdownBody
  -- TODO if there's no proof at all yet, just a sorry, we shouldn't separately restate the goal that appears in the sorry!
  match ← sorries with
  | [] => pure prompt
  | (ctx, g, _, _) :: _ => do
      let pp ← ctx.ppGoals [g]
      pure <| prompt ++ s!"\nThe remaining goal is \n{pp.fence}"

def dialog (n : Nat) : M MetaM String := do
  sendSystemMessage systemPrompt
  askForAssistance (← initialPrompt)
  for i in List.range (n-1) do try
    done
    return s!"Success after {i+1} requests"
  catch _ =>
    askForAssistance (← feedback)
  try
    done
    return s!"Success after {n} requests"
  catch _ => return s!"Failed after {n} requests"

elab tk:"gpt" : tactic => do
  let (newDecl, result) ← discussDeclContaining tk
    (fun decl => decl.replace "gpt" "sorry") -- haha this will make some fun errors
    (dialog 3)
  logInfoAt tk result
  logInfoAt tk newDecl
