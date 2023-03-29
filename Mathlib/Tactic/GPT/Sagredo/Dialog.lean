/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Zhangir Azerbayev
-/
import Mathlib.Tactic.GPT.Sagredo.Monad

open Lean

namespace Mathlib.Tactic.GPT.Sagredo

def goalsFeedback (goals : Format) : String :=
s!"The new goal state is:\n{goals.fence}
1. Please write out a plan for proceeding, in English (with LaTeX).
2. Please add the next tactic step to the proof.
   Include the new version of your (possibly incomplete) proof in a code block.
   Make sure the code block is self-contained and runs."

def errorFeedback (e : Lean.Message) : M IO String := do
  let preface ← match e.endPos with
  | none => pure s!"On line {e.pos.line} there was an error:"
  | some endPos => do
    let block ← latestCodeBlock
    let line := (block.body.splitOn "\n")[e.pos.line - 1]!
    let substring := line.drop e.pos.column |>.take (endPos.column - e.pos.column)
    pure s!"On line {e.pos.line} there was an error on `{substring}`:"
  pure <| preface ++ "\n" ++
    (match e.severity with | .error => "error: " | _ => "warning: ") ++
    (← e.data.toString)

def feedback : M IO String := do
  let errors ← (← errors).mapM fun m => do pure <| (m, (← m.toString).splitOn "\n")
  -- We now look at the errors, and given different responses depending on what we see.
  let (unsolvedGoals, otherErrors) := errors.partition fun e => e.2.head! |>.endsWith "unsolved goals"
  let (_usesSorry, otherErrors) := otherErrors.partition fun e => e.2.head! |>.endsWith "declaration uses 'sorry'"

  match otherErrors with
  | [] => match unsolvedGoals with
    | [] => match ← sorries with
      | [] => pure "That's great, it looks like that proof works!"
      | (ctx, g, _, _) :: _ => do
          -- TODO mention the later sorries?
          pure <| goalsFeedback (← ctx.ppGoals [g])
    | _ =>
        let goal := "\n".intercalate (unsolvedGoals.map fun p => p.2.tail).join |>.trim
        pure <| goalsFeedback goal
  | _ =>
    pure <| s!"When I try to run this code, I get errors:\n" ++
      -- TODO decide which other errors matter or deserve emphasise (or helpful advice!)
      String.intercalate "\n" (← otherErrors.mapM (fun p => errorFeedback p.1)) ++
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
      pure <| prompt ++ "\n" ++ goalsFeedback (← ctx.ppGoals [g])

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

elab tk:"sagredo" : tactic => do
  let (newDecl, result) ← discussDeclContaining tk
    (fun decl => decl.replace "sagredo" "sorry") -- TODO this is a hack
    (dialog 6)
  logInfoAt tk result
  logInfoAt tk newDecl
