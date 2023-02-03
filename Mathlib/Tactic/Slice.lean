/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Tactic.Conv

open CategoryTheory
open Lean Parser.Tactic Elab Command Elab.Tactic Meta

-- TODO someone might like to generalise this tactic to work with other associative structures.
namespace Tactic

variable [Monad m] [MonadExceptOf Exception m]

partial def iterateUntilFailureWithResults {α : Type} (tac : m α) : m (List α) := do 
  try 
    let a ← tac
    let l ← iterateUntilFailureWithResults tac 
    pure (a :: l) 
  catch _ => pure [] 
#align tactic.repeat_with_results Tactic.iterateUntilFailureWithResults

def iterateUntilFailureCount {α : Type} (tac : m α) : m ℕ := do
  let r ← iterateUntilFailureWithResults tac
  return r.length 
#align tactic.repeat_count Tactic.iterateUntilFailureCount

end Tactic

namespace Conv

open Tactic

variable [Monad m] [MonadExceptOf Exception m]

def evalSlice (a b : Nat) : TacticM Unit := do
  iterateUntilFailure do
    ``(Category.assoc) >>= fun e => rewriteTarget' e (symm := false)
  iterateRange (a - 1) (a - 1) do
      evalTactic (← `(conv| congr))
      evalTactic (← `(tactic| rotate_left))
  let k ← iterateUntilFailureCount 
    <| ``(Category.assoc) >>= fun e => rewriteTarget' e (symm := true) 
  let c := k+1+a-b
  iterateRange c c <| evalTactic (← `(conv| congr))
  iterateUntilFailure do 
    ``(Category.assoc) >>= fun e => rewriteTarget' e (symm := false) 

elab "slice" a:num b:num : conv => evalSlice a.getNat b.getNat

open Lean Parser.Tactic Parser.Tactic.Conv Elab.Tactic Meta
syntax (name := sliceLHS) "sliceLHS" num num " => " convSeq : tactic
macro_rules
  | `(tactic| sliceLHS $a $b => $seq) =>
    `(tactic| conv => lhs; slice $a $b; ($seq:convSeq))

syntax (name := sliceRHS) "sliceRHS" num num " => " convSeq : tactic
macro_rules
  | `(tactic| sliceRHS $a $b => $seq) =>
    `(tactic| conv => rhs; slice $a $b; ($seq:convSeq))

-- add_tactic_doc
--   { Name := "slice"
--     category := DocCategory.tactic
--     declNames := [`tactic.interactive.slice_lhs, `tactic.interactive.slice_rhs]
--     tags := ["category theory"] }
--
