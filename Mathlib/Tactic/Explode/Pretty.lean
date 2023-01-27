import lean
import Lean.Meta.Basic
import Mathlib.Tactic.Explode.Datatypes
set_option linter.unusedVariables false

open Lean Elab
open Std

namespace Mathlib.Explode

/- padRight ["hi", "hello"] => ["hi   ", "hello"] -/
def padRight (mds : List MessageData) : MetaM (List MessageData) := do
  -- 1. Find the max length of the word in a list
  let mut maxLength := 0
  for md in mds do
    let length := (← md.toString).length
    maxLength := if length > maxLength then length else maxLength

  -- 2. Padd all words in a list with " "
  let mut paddedMds := []
  for md in mds do
    let padWidth : Nat := maxLength - (← md.toString).length
    let padding := MessageData.joinSep (List.replicate padWidth " ") ""
    paddedMds := (md ++ padding) :: paddedMds
  return paddedMds.reverse

def thmToMd (context : MessageDataContext) (thm : Thm) :=
  match thm with
    | Thm.expr expr => MessageData.withContext context expr
    | Thm.name name => name.toString
    | Thm.string string => string

def rowToMd : List MessageData → List MessageData → List MessageData → List Entry → MetaM MessageData
  | line :: lines, dep :: deps, thm :: thms, en :: es => do
    let pipes := String.join (List.replicate en.depth "│ ")
    let pipes := match en.status with
      | Status.sintro => "├ "
      | Status.intro  => "│ " ++ pipes ++ "┌ "
      | Status.reg    => "│ " ++ pipes
      | Status.lam    => "│ " ++ pipes

    let type := MessageData.withContext en.context en.type

    let row := m!"{line}│{dep}│ {thm} {pipes}{type}\n"
    return (← rowToMd lines deps thms es).compose row
  | _, _, _, _ => return MessageData.nil

def entriesToMd (entries : Entries) : MetaM MessageData := do
  -- ['1', '2', '3']
  let paddedLines ← padRight (entries.l.map (λ entry =>
    m!"{entry.line}"
  ))
  -- ['   ', '1,2', '1  ']
  let paddedDeps  ← padRight (entries.l.map (λ entry =>
    m!"{String.intercalate "," (entry.deps.map toString)}"
  ))
  -- ['p  ', 'hP ', '∀I ']
  let paddedThms ← padRight (entries.l.map (λ entry =>
    thmToMd entry.context entry.thm
  ))

  rowToMd paddedLines paddedDeps paddedThms entries.l
