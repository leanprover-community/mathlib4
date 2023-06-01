/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Zhangir Azerbayev, Zach Battleman
-/
import Mathlib.Tactic.GPT.Sagredo.Monad
import Mathlib.Tactic.GPT.Levenshtein
open Lean

namespace Lean.Elab

/-- The core function glues all the lines together, instead of putting newlines between them. -/
def ContextInfo.ppGoals' (ctx : ContextInfo) (goals : List MVarId) : IO Format :=
  if goals.isEmpty then
    return "no goals"
  else
    ctx.runMetaM {} (return Std.Format.joinSep (← goals.mapM (Meta.ppGoal ·)) "\n")

end Lean.Elab

namespace Mathlib.Tactic.GPT.Sagredo

inductive MessageType
  | unsolvedGoals | usesSorry | unknownTactic | other
deriving BEq, Repr

deriving instance Repr for MessageSeverity
structure ParsedMessage where
  type : MessageType
  severity : MessageSeverity
  lines : List String
  onLine : Nat
  span : String
deriving Repr

def ParsedMessage.of (code : String) (m : Lean.Message) : IO ParsedMessage := do
  let lines := (← m.data.toString).splitOn "\n"
  let type : MessageType := if lines.head!.endsWith "unsolved goals" then
      .unsolvedGoals
    else if lines.head!.endsWith "declaration uses 'sorry'" then
      .usesSorry
    else if lines.head!.endsWith "unknown tactic" then
      .unknownTactic
    else
      .other
  let onLine := m.pos.line
  let codeLines := code.splitOn "\n"
  let span := match m.endPos with
    | none => codeLines[m.pos.line - 1]!.drop (m.pos.column - 1) |>.trim.takeWhile (· ≠ ' ')
    | some e => codeLines[m.pos.line - 1]!.drop m.pos.column |>.take (e.column - m.pos.column)
  pure ⟨type, m.severity, lines, onLine, span⟩

def ParsedMessage.toString (m : ParsedMessage) : String :=
s!"There was an error on line {m.onLine}, located on the tokens `{m.span}`:\n\n```\n" ++
  (match m.severity with | .error => "error: " | .warning => "warning: " | _ => "") ++
    "\n".intercalate m.lines ++ "\n```\n"

def goalsFeedback (line? : Option Nat) (goals : Format) : String :=
(match line? with
| none => s!"The goal state is currently:\n"
| some line => s!"The goal state for the sorry on line {line} is:\n") ++
  goals.fence ++
  "1. Please write out a plan for proceeding, in English (with LaTeX).
2. Please add the next tactic step to the proof.
   Include the new version of your (possibly incomplete) proof in a code block.
   Make sure the code block is self-contained and runs."

def initialPrompt : M IO String := do
  let prompt := "I am going to show you an incomplete proof and the accompanying goal state.
I will ask you to complete the proof step by step, adding one tactic step in each response.

Here is the proof thus far:\n" ++ (← latestCodeBlock).markdownBody
  match ← sorries with
  | [] => pure prompt
  | (ctx, g, pos, _) :: _ => do
      if pos.line <= 2 then
        -- GPT can just read the goal from the theorem statement.
        pure prompt
      else
        pure <| prompt ++ "\n" ++ goalsFeedback none (← ctx.ppGoals' [g])

def tacticSuggestion (badTactic : String) : String :=
  let tacs := ["all_goals", "any_goals", "apply", "assumption", "by_cases", "by_contra", "cases'", "congr", "contradiction", "contrapose", "convert", "convert_to", "exact", "exfalso", "field_simp", "have", "aesop", "induction'", "intro", "iterate", "left", "linarith", "push_neg", "rcases", "rfl", "repeat", "right", "ring", "rintro", "rw", "specialize", "constructor", "simp", "swap", "symm", "tauto", "try", "unfold", "use"]

  let suggestion := (tacs.foldl (fun (best, dist) new =>
    let newDist := badTactic.levenshtein new
    if newDist < dist then
      (new, newDist)
    else
      (best, dist))
    ("", 5)).1

  s!"You used {badTactic}, but it looks like you maybe meant {suggestion}. Try that instead.\n"

def feedback : M IO String := do
  let errors ← ((← errors).filter (·.severity == .error)).mapM
    (fun e => do ParsedMessage.of (← latestCodeBlock).body e)
  -- We now look at the errors, and given different responses depending on what we see.
  let (unsolvedGoals, otherErrors) := errors.partition fun e => e.type == .unsolvedGoals
  let (_usesSorry, otherErrors) := otherErrors.partition fun e => e.type == .usesSorry
  let unknownTactics := otherErrors.filter fun e => e.type == .unknownTactic

  let badTactics := unknownTactics.map (fun t => t.span)

  match otherErrors with
  | [] => match ← sorries with
    | [] => match unsolvedGoals with
      | [] => pure "That's great, it looks like that proof works!"
      | _ => do
          let goal := "\n".intercalate (unsolvedGoals.map fun p => p.lines.tail).join |>.trim
          pure <| goalsFeedback none goal
    | (ctx, g, pos, _) :: _ =>
        -- TODO mention the later sorries?
        -- FIXME the new line characters are disappearing from this goal.
        pure <| goalsFeedback pos.line (← ctx.ppGoals' [g])
  | _ =>
    pure <| s!"When I try to run this code, I get the following error:\n\n" ++
      -- TODO decide which other errors matter or deserve emphasise (or helpful advice!)
      -- TODO mention the later errors?
      (otherErrors.head?.map (fun p => p.toString)).get! ++
      "\n\nPlease describe how you are going to fix this error and try again.\n" ++
      String.join (badTactics.map tacticSuggestion) ++
      "Change the tactic step where there is an error, but do not add any additional tactic steps."

-- Wojciech proposes adding the following:
-- ```

-- ```
-- and
-- ```
-- However, if you have concluded that the theorem is impossible to prove, justify why and leave a `sorry` in place
-- of the proof
-- ```
-- to the feedback prompt.
-- I'd like to see an example where this happens, before making this change.

def systemPrompt : String :=
"You are a pure mathematician who is an expert in the Lean 4 theorem prover.
Your job is help your user write Lean proofs.

I want to remind you that we're using Lean 4, not the older Lean 3,
and there have been some syntax changes. In particular:
- Type constants are now UpperCamelCase, eg `Nat`, `List`.
- Term constants and variables are now `lowerCamelCase` rather than `snake_case`.
  For example, we now have `NumberTheory.Divisors.properDivisors instead of
  `number_theory.divisors.proper_divisors`.
- Pure functions are now written with the syntax `fun x => f x`.
  The old `λ x, f x` syntax will not work.
- Instead of being separated by a comma, tactics can be separated by a newline or by a semicolon.
  For example, we could write
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
- In the `rw` tactic you must enclose the lemmas in square brackets, even if there is just one.
  For example `rw h1` is now `rw [h1]`.
- The `induction` tactic now uses a structured format, like pattern matching.
  For example, in Lean 4 we can write
```lean
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.add_succ, ih]
```
  Alternatively you can still use `induction' with x y ih`, like in Lean 3.
- The `cases` tactic now uses a structured format, like pattern matching.
  For example, in Lean 4 we can write
```lean
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => apply Or.inr; exact hp
  | inr hq => apply Or.inl; exact hq
```

It is extremely important that you do not change the name of the theorem you are trying to prove.
Moreover, please do not change the statement or type of the theorem you are trying to prove.
(In Lean 4 we can leave out many implicit arguments,
so don't put this back in if they look like they are missing.)

If there is a doc-string on the code the user provides,
please include it unchanged in your suggestion.

If you conclude that a proof is impossible, explain why.
If the current goal state is impossible to achieve
that does not mean that the proof is impossible.
Your approach so far might be wrong, but the theorem itself is true.
Do not change the statement or type of a theorem in order to accomodate an unprovable goal:
simply explain why the proof is impossible.
"

--- Zach proposes adding:
-- Here is a description of some basic tactics:
--  * `rfl` is a tactic that closes goals where two elements are definitionally equal such as `2 = 2`
--  * `cases` takes an inductive type and creates new goals based on its possible values
--  * `simp` will do its best to simplify a goal. This is often a good first try for simple goals and
--     if it does not work, try adding theorems and lemmas to the tactic. For example, `simp [Nat.add_comm]`
--     will use `simp` with the additional information that Natural number addition is commutative.


/--
Generate the text of the next query to send.
If we've only sent system messages so far, this should be the initial prompt,
otherwise, the feedback on the current errors, sorries, and goals.
-/
def nextQuery : M IO String := do
  if (← getLog).all (·.role == .system) then
    initialPrompt
  else
    feedback

def dialog (totalSteps : Nat := 10) (progressSteps : Nat := 4) : M IO String := do
  sendSystemMessage systemPrompt
  askForAssistance (← initialPrompt)
  for i in List.range (totalSteps - 1) do
    if (← isDone) then
      return s!"Success after {i+1} requests"
    else
      if (← recentProgress progressSteps) then
        askForAssistance (← feedback)
      else
        return s!"Failed after {i+1} requests, because no progress was made after {progressSteps} steps"
  if (← isDone) then
    return s!"Success after {totalSteps} requests"
  else
    return s!"Failed after {totalSteps} requests"

-- FIXME: the tactic doesn't compile without this,
-- however with this Lake doesn't compile...
instance [MonadLiftT m n] : MonadLiftT (StateT α m) (StateT α n) where
  monadLift := fun f s => f s

elab tk:"sagredo" : tactic => do
  let (newDecl, result) ← discussDeclContaining tk
    (fun decl => decl.replace "sagredo" "sorry") -- TODO this is a hack
    (dialog 10 4)
  logInfoAt tk result
  logInfoAt tk newDecl
