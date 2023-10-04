/-
Copyright (c) 2023 Miyahara Kō. All rights reserved.
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

def eval (game : StringGame) (answers : List String)
    (finished : String := "Right! The game is over!") : String :=
  match M.dest game, answers with
  | ⟨some _, answered⟩, answer :: answers => eval (answered answer) answers finished
  | ⟨some hint, _⟩, [] => hint
  | ⟨none, _⟩, _ => finished

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

def eval (game : StringGameIntl) (answers : List String)
    (finished : String := "Right! The game is over!") : String :=
  match MIntl.dest game, answers with
  | ⟨some _, answered⟩, answer :: answers => eval (answered answer) answers finished
  | ⟨some hint, _⟩, [] => hint
  | ⟨none, _⟩, _ => finished

def familyNameQuiz (familyName : String) : StringGameIntl :=
  quiz "What's my family name?" familyName (hintLengthDiff familyName)

end StringGameIntl

def myGame : StringGame := StringGame.nameQuiz "Miyahara" "Kō"

def myGameIntl : StringGameIntl := StringGameIntl.familyNameQuiz "Miyahara"

#eval
  myGame.eval ["Keizer"]

#eval
  myGame.eval (List.replicate 1000 "Keizer")

-- benchmark, too slow:
-- #eval
--   myGameIntl.eval (List.replicate 1000 "Keizer")

#eval
  myGame.eval ["Keizer", "Carneiro"]

#eval
  myGame.eval ["Keizer", "Carneiro", "Miyahara"]

#eval
  myGame.eval ["Keizer", "Carneiro", "Miyahara", "Mario"]

#eval
  myGame.eval ["Keizer", "Carneiro", "Miyahara", "Mario", "Ko"]

#eval
  myGame.eval ["Keizer", "Carneiro", "Miyahara", "Mario", "Ko", "Kō"]
