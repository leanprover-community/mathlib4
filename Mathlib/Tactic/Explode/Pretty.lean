import lean
import Lean.Meta.Basic
import Mathlib.Tactic.Explode.Datatypes
set_option linter.unusedVariables false

open Lean Elab
open Std

namespace Mathlib.Explode

/- padRight ["hi", "hello"] => ["hi   ", "hello"] -/
def padRight (l : List String) : List String :=
  -- 1. Find the max length of the word in a list
  let maxL := l.foldl (λ r s => max r s.length) 0
  -- 2. Padd all words in a list with " "
  l.map (λ s =>
    let padWidth : Nat := maxL - s.length
    s ++ String.join (List.replicate padWidth " ")
  )

def formatMe : List String → List String → List String → List Entry → MetaM MessageData
  | line :: lines, dep :: deps, thm :: thms, en :: es => do
    let margin := String.join (List.replicate en.depth " │")
    let margin := match en.status with
      | Status.sintro => " ├" ++ margin
      | Status.intro  => " │" ++ margin ++ " ┌"
      | Status.reg    => " │" ++ margin ++ ""
      | Status.lam    => " │" ++ margin ++ ""
    let lhs : String := line ++ "│" ++ dep ++ "│ " ++ thm ++ margin ++ " "
    let tp : MessageData := MessageData.withContext en.context en.type
    let md := lhs ++ (MessageData.nest lhs.length tp).group ++ Format.line
    return (← formatMe lines deps thms es).compose md
  | _, _, _, _ => return MessageData.nil


def entriesToMD (es : Entries) : MetaM MessageData :=
  -- ['1', '2', '3']
  let lines := padRight (es.l.map (λ en => toString en.line))
  -- ['   ', '1,2', '  1']
  let deps  := padRight (es.l.map (λ en => String.intercalate "," (en.deps.map toString)))
  -- ['p  ', 'hP ', '∀I ']
  let thms  := padRight (es.l.map (λ en => (en.thm).toString))
  formatMe lines deps thms es.l
