/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Tactic.Conv

/-!
# The `slice` tactic

Applies a tactic to an interval of terms from a term obtained by repeated application
of `Category.comp`.

-/

open CategoryTheory
open Lean Parser.Tactic Elab Command Elab.Tactic Meta

-- TODO someone might like to generalise this tactic to work with other associative structures.

/- Porting note: moved `repeat_with_results` to `repeat_count` to `Mathlib/Tactic/Core.lean` -/

open Parser.Tactic.Conv

/--
`slice` is a conv tactic; if the current focus is a composition of several morphisms,
`slice a b` reassociates as needed, and zooms in on the `a`-th through `b`-th morphisms.
Thus if the current focus is `(a ≫ b) ≫ ((c ≫ d) ≫ e)`, then `slice 2 3` zooms to `b ≫ c`.
-/
syntax (name := slice) "slice " num ppSpace num : conv

/--
`evalSlice`
- rewrites the target expression using `Category.assoc`.
- uses `congr` to split off the first `a-1` terms and rotates to `a`-th (last) term
- counts the number `k` of rewrites as it uses `←Category.assoc` to bring the target to
  left associated form; from the first step this is the total number of remaining terms from `C`
- it now splits off `b-a` terms from target using `congr` leaving the desired subterm
- finally, it rewrites it once more using `Category.assoc` to bring it to right-associated
  normal form
-/
def evalSlice (a b : Nat) : TacticM Unit := do
  let _ ← iterateUntilFailureWithResults do
    evalTactic (← `(conv| rw [Category.assoc]))
  iterateRange (a - 1) (a - 1) do
      evalTactic (← `(conv| congr))
      evalTactic (← `(tactic| rotate_left))
  let k ← iterateUntilFailureCount
    <| evalTactic (← `(conv| rw [← Category.assoc]))
  let c := k+1+a-b
  iterateRange c c <| evalTactic (← `(conv| congr))
  let _ ← iterateUntilFailureWithResults do
    evalTactic (← `(conv| rw [Category.assoc]))

/-- `slice` is implemented by `evalSlice`. -/
elab "slice " a:num ppSpace b:num : conv => evalSlice a.getNat b.getNat

/--
`slice_lhs a b => tac` zooms to the left hand side, uses associativity for categorical
composition as needed, zooms in on the `a`-th through `b`-th morphisms, and invokes `tac`.
-/
syntax (name := sliceLHS) "slice_lhs " num ppSpace num " => " convSeq : tactic
macro_rules
  | `(tactic| slice_lhs $a $b => $seq) =>
    `(tactic| conv => lhs; slice $a $b; ($seq:convSeq))

/--
`slice_rhs a b => tac` zooms to the right hand side, uses associativity for categorical
composition as needed, zooms in on the `a`-th through `b`-th morphisms, and invokes `tac`.
-/
syntax (name := sliceRHS) "slice_rhs " num ppSpace num " => " convSeq : tactic
macro_rules
  | `(tactic| slice_rhs $a $b => $seq) =>
    `(tactic| conv => rhs; slice $a $b; ($seq:convSeq))

/- Porting note: update when `add_tactic_doc` is supported` -/
-- add_tactic_doc
--   { Name := "slice"
--     category := DocCategory.tactic
--     declNames := [`tactic.interactive.sliceLHS, `tactic.interactive.sliceRHS]
--     tags := ["category theory"] }
--
