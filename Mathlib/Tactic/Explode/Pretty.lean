import lean
import Lean.Meta.Basic
import Mathlib.Tactic.Explode.Datatypes

open Lean Elab
open Std

/- padRight ["hi", "hello"] => ["hi   ", "hello"] -/
def padRight (l : List String) : List String :=
  -- 1. Find the max length of the word in a list
  let maxL := l.foldl (λ r s => max r s.length) 0
  -- 2. Padd all words in a list with " "
  l.map (λ s =>
    let padWidth : Nat := maxL - s.length
    s ++ String.join (List.replicate padWidth " ")
  )

def formatMe : List String → List String → List String → List Entry → MetaM Format
  | line :: lines, dep :: deps, thm :: thms, en :: es => do
    let margin := String.join (List.replicate en.depth " │")
    let margin := match en.status with
      | Status.sintro => " ├" ++ margin
      | Status.intro  => " │" ++ margin ++ " ┌"
      | Status.reg    => " │" ++ margin ++ ""
      | Status.lam    => " │" ++ margin ++ ""
    let p : Expr ← Lean.Meta.inferType en.expr
    let lhs : String := line ++ "│" ++ dep ++ "│ " ++ thm ++ margin ++ " "
    let fmt := Format.text lhs ++ (Format.nest lhs.length f!"{p}").group ++ Format.line
    return fmt.append (← formatMe lines deps thms es)
  | _, _, _, _ => return Format.nil

def entriesToFormat (es : Entries) : MetaM Format :=
  let lines := padRight (es.l.map (λ en => toString en.line))
  let deps  := padRight (es.l.map (λ en => String.intercalate "," (en.deps.map toString)))
  let thms  := padRight (es.l.map (λ en => (en.thm).toString))
  formatMe lines deps thms es.l

def formatted : MetaM Format :=
  formatMe
    ["line_1", "line_2", "line_3"]
    ["dep_1", "dep_2", "dep_3"]
    ["thm_1", "thm_2", "thm_3"]
    [myEntry, myEntry, myEntry2]

#eval formatted
