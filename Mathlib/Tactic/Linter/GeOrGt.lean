/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Lean.Elab.Command
import Lean.Linter.Util

/-!
## The `ge_or_gt` linter

A linter for checking whether a declaration contains a `≥` or `>` in an illegal position:
`≤` or `<` should be used instead.

**Why is this bad?**
`rw` and `simp` require ... equality, so for these tactics,
`rw` or `simp` will only apply if `≥` or `>` line up --> normal form.

This check excludes, in particular, comments, a `≥` or `>` symbol in custom notation
and predicate binders like `∃ i ≥ 1`. We also exclude the bodies of proofs;
we include hypotheses (unlike in mathlib3) and conclusions of theorems and lemmas.

Unlike in mathlib3, this checks hypotheses, definitions and conclusions as well as proofs. -/

open Lean Elab Command

namespace Mathlib.Linter.ge_or_gt

/-- Whether a syntax element is a "greater" or "greater than" sign.
(This excludes, in particular, comments, a `≥` or `>` symbol as part of custom or local notation
 and predicate binders like `∃ i ≥ 1`.) -/
def is_ge_or_gt : Syntax → Bool
  | `($_ ≥ $_) => true
  | `($_ > $_) => true
  | _ => false

/-- The `ge_or_gt` linter emits a warning if a declaration contains `≥` or `>`
  in illegal places. -/
register_option linter.geOrGt : Bool := {
  defValue := true
  descr := "enable the `ge_or_gt` linter"
}

-- xxx: this feels like repetitive boilerplate; is there a way to abstract this?
/-- Gets the value of the `linter.geOrGt` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.geOrGt o

-- bug in the elaborator: inlining this fails
def is_bla (start : Syntax) : Bool :=
  match start with
  | `((· > · )) | `((· ≥ ·)) => true
  | _ => false

/-- docstring here -/
def getOrGtLinter : Linter where
  run := withSetOptionIn fun stx => do
    unless getLinterHash (← getOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    match stx.findStack? (fun _ ↦ true) is_ge_or_gt with
    | some ((head, _n)::chain) =>
      -- if the `≥` or `>` is surrounded by ⬝, this is a comparator: continue
      let r : Bool := match chain with
       | (start, _n)::_rest =>
        is_bla start
       | _ => false
      if r then
        logInfo (toMessageData chain)
        return
      -- let r := head.find? is_ge_or_gt
      -- if let some s ← r then
      --   return
      -- let dot := `(sdf)
      -- xxx how to get item before and after!
      --match head with
      --| `(⬝ > ⬝) => return--`(⬝)::[]]

      -- match _chain with
      --  | body::last =>
      --   have : _chain ≠ [] := sorry
      --   return
      --  | _ => return--if let some l ← _chain.getLast then
      --Linter.logLint linter.geOrGt last sorry m!"last item is"
      Linter.logLint linter.geOrGt head m!"'≥ or > is used in an illegal position\n\
      please change the statement to use ≤ or < instead"
    | _ => return

initialize addLinter getOrGtLinter

end Mathlib.Linter.ge_or_gt
