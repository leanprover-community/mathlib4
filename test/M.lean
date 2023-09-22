/-
Copyright (c) 2023 Miyahara Kō All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
import Mathlib.Data.PFunctor.Univariate.M

open PFunctor

def StringGame.CycleP : PFunctor where
  A := Option String
  B o := bif o.isSome then String else Empty

abbrev StringGame.Cycle := StringGame.CycleP.Obj

abbrev StringGame := StringGame.CycleP.M

abbrev StringGameIntl := StringGame.CycleP.MIntl

namespace StringGame

instance : AndThen StringGame where
  andThen g₁ g₂ :=
    let cycle (g : StringGame) : StringGame ⊕ Cycle StringGame :=
      match M.dest g with
      | ⟨some hint, g'⟩ => Sum.inr ⟨some hint, g'⟩
      | ⟨none, _⟩       => Sum.inl (g₂ ())
    M.corec' cycle g₁

@[specialize]
def quiz (question : String) (correct : String) (hint : String → String) : StringGame :=
  let cycle (answer : String) : Cycle String :=
    if answer = correct then
      ⟨none, Empty.elim⟩
    else
      ⟨some (hint answer), id⟩
  M.mk ⟨some question, M.corec cycle⟩

def runList (game : StringGame) (answers : List String)
    (finished : String := "Right! The game is over!") : String :=
  match M.dest game, answers with
  | ⟨some _, answered⟩, answer :: answers => runList (answered answer) answers finished
  | ⟨some hint, _⟩, [] => hint
  | ⟨none, _⟩, _ => finished

def run (game : StringGame) (finished : String := "Right! The game is over!") : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  IO.iterate game fun game => do
    match M.dest game with
    | ⟨some hint, answered⟩ =>
      stdout.putStrLn hint
      let input ← stdin.getLine
      let answer := input.dropRightWhile Char.isWhitespace
      pure <| Sum.inl <| answered answer
    | ⟨none, _⟩ =>
      stdout.putStrLn finished
      pure <| Sum.inr ()

def hintLengthDiff (correct : String) (answer : String) : String :=
  if correct.length = answer.length then
    let diffPos := correct.firstDiffPos answer
    let diffChar := correct.get diffPos
    s!"{diffPos.byteIdx + 1}-th charactor is \'{diffChar}\'"
  else
    s!"The length is {correct.length}."

def nameQuiz (familyName firstName : String) : StringGame :=
  quiz "What's my family name?" familyName (hintLengthDiff familyName) >>
    quiz "Right! So, what's my first name?" firstName (hintLengthDiff firstName)

end StringGame

namespace StringGameIntl

open StringGame

@[specialize]
def quiz (question : String) (correct : String) (hint : String → String) : StringGameIntl :=
  let cycle (answer : String) : Cycle String :=
    if answer = correct then
      ⟨none, Empty.elim⟩
    else
      ⟨some (hint answer), id⟩
  MIntl.mk ⟨some question, MIntl.corec cycle⟩

def run (game : StringGameIntl) (finished : String := "Right! The game is over!") : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  IO.iterate game fun game => do
    match MIntl.dest game with
    | ⟨some hint, answered⟩ =>
      stdout.putStrLn hint
      let input ← stdin.getLine
      let answer := input.dropRightWhile Char.isWhitespace
      pure <| Sum.inl <| answered answer
    | ⟨none, _⟩ =>
      stdout.putStrLn finished
      pure <| Sum.inr ()

def familyNameQuiz (familyName : String) : StringGameIntl :=
  quiz "What's my family name?" familyName (hintLengthDiff familyName)

end StringGameIntl

def myGame : StringGame := StringGame.nameQuiz "Miyahara" "Kō"

def myGameIntl : StringGameIntl := StringGameIntl.familyNameQuiz "Miyahara"

#eval
  myGame.runList ["Keizer"]

#eval
  myGame.runList ["Keizer", "Carneiro"]

#eval
  myGame.runList ["Keizer", "Carneiro", "Miyahara"]

#eval
  myGame.runList ["Keizer", "Carneiro", "Miyahara", "Mario"]

#eval
  myGame.runList ["Keizer", "Carneiro", "Miyahara", "Mario", "Ko"]

#eval
  myGame.runList ["Keizer", "Carneiro", "Miyahara", "Mario", "Ko", "Kō"]

def help : String := "Mathlib4 M-type testing CLI
Usage: m_test [COMMAND]

Commands:
  # No privilege required
  intl         Test using the internal definition of M-type which isn't optimized"

def main (args : List String) : IO Unit :=
  match args with
  | [] => myGame.run
  | ["intl"] => myGameIntl.run
  | _ => IO.println help
