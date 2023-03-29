import Mathlib.Tactic.ChatGPT.Monad

open Lean

namespace Mathlib.Tactic.ChatGPT

def feedback : M IO String := do
  --let last := (← latestCodeBlock).markdownBody

  let errors ← (← errors).mapM fun m => do pure <| (← m.toString).splitOn "\n"
  -- We now look at the errors, and given different responses depending on what we see.
  let (unsolvedGoals, otherErrors) := errors.partition fun e => e.head! |>.endsWith "unsolved goals"
  let (_usesSorry, otherErrors) := otherErrors.partition fun e => e.head! |>.endsWith "declaration uses 'sorry'"

  match otherErrors with
  | [] => match unsolvedGoals with
    | [] => match ← sorries with
      | [] => pure "That's great, it looks like that proof works!"
      | (ctx, g, _, _) :: _ => do -- used to be (ctx, g, pos, _)
          -- TODO mention the later sorries?
          let pp ← ctx.ppGoals [g]
          pure s!"The new goal state is:\n{pp.fence}\n1. Please write out a plan for proceeding, in English (with LaTeX).\n2. Please add the next tactic step to the proof. Include the new version of your (possibly incomplete) proof in a code block. Make sure the code block is self-contained and runs."
    | _ =>
        let goal := String.intercalate "\n" (unsolvedGoals.map List.tail).join |>.trim
        pure s!"The new goal state is:\n{goal.fence}\n1. Please write out a plan for proceeding, in English (with LaTeX).\n2. Please add the next tactic step to the proof. Include the new version of your (possibly incomplete) proof in a code block. Make sure the code block is self-contained and runs."
  | _ =>
    pure <| s!"When I try to run this code, I get errors:\n" ++
      -- TODO decide which other errors matter or deserve emphasise (or helpful advice!)
      -- TODO mention the lines numbers in prose, possibly extracting the relevant span and quoting it
      String.intercalate "\n" otherErrors.join ++
      "\nPlease describe how you are going to fix this error and try again. Change the tactic step where there is an error, but do not add any additional tactic steps."

def systemPrompt : String :=
"You are a pure mathematician who is an expert in the Lean 4 theorem prover. Your job is help your user write Lean proofs.

I want to remind you that we're using Lean 4, not the older Lean 3, and there have been some syntax changes. In particular:
- Type constants are now UpperCamelCase, eg `Nat`, `List`.
- Term constants and variables are now `lowerCamelCase` rather than `snake_case`. For example, we now have `NumberTheory.Divisors.properDivisors instead of `number_theory.divisors.proper_divisors`.
- Pure functions are now written with the syntax `fun x => f x`. The old `λ x, f x` syntax will not work.
- Instead of being separated by a comma, tactics can be separated by a newline or by a semicolon. For example, we could write
```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp
  exact And.intro hq hp
```
or
```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp; exact And.intro hq hp
```
- Indentation is significant.
- In the `rw` tactic you must enclose the lemmas in square brackets, even if there is just one. For example `rw h1` is now `rw [h1]`.
- The `induction` tactic now use a structured format, like pattern matching. For example, in Lean 4 we can write
```lean
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.add_succ, ih]
```
  Alternatively you can still use `induction' with x y ih`, like in Lean 3.
- The `cases` tactic now uses a structured format, like pattern matching. For example, in Lean 4 we can write
```lean
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => apply Or.inr; exact hp
  | inr hq => apply Or.inl; exact hq
```
"

def initialPrompt : M IO String := do
  let prompt := "I am going to show you an incomplete proof and the accompanying goal state. I will ask you to complete the proof step by step, adding one tactic step in each response.

Here is the proof thus far:\n" ++ (← latestCodeBlock).markdownBody
  -- TODO if there's no proof at all yet, just a sorry, we shouldn't separately restate the goal that appears in the sorry!
  match ← sorries with
  | [] => pure prompt
  | (ctx, g, _, _) :: _ => do
      let pp ← ctx.ppGoals [g]
      pure <| prompt ++ s!"\nHere is the goal state: \n{pp.fence}\n1. Please write out a plan for proceeding, in English (with LaTeX).\n2. Please add the next tactic step to the proof. Include a new version of your (possibly incomplete) proof in a code block. Make sure the code block is self-contained and runs."

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
    (dialog 6)
  logInfoAt tk result
  logInfoAt tk newDecl
